/*
 * BSD 3-Clause License
 * 
 * Copyright (c) 2023, General Electric Company.
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice, this
 *    list of conditions and the following disclaimer.
 * 
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 
 * 3. Neither the name of the copyright holder nor the names of its
 *    contributors may be used to endorse or promote products derived from
 *    this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package com.ge.research.osate.verdict.handlers;

import com.ge.research.osate.verdict.aadl2vdm.Agree2Vdm;
import com.ge.research.osate.verdict.gui.BundlePreferences;
import com.ge.research.osate.verdict.gui.PRAResultsView;
import com.ge.research.osate.verdict.gui.PRASettingsPanel;
import com.ge.research.osate.verdict.gui.ViewUtils;
import com.ge.verdict.vdm.VdmTranslator;
import com.google.common.io.Files;
import io.micrometer.core.instrument.Clock;
import io.micrometer.core.instrument.Metrics;
import io.micrometer.core.instrument.Timer;
import io.micrometer.core.instrument.simple.SimpleConfig;
import io.micrometer.core.instrument.simple.SimpleMeterRegistry;
import java.io.File;
import java.io.IOException;
import java.nio.file.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.intro.IIntroPart;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;
import verdict.vdm.vdm_model.Model;

public class PRAHandler extends AbstractHandler {

    private static volatile int currentIteration =
            0; // iteration will be accessed by multiple threads, hence a
    // volatile type
    private static String projectDirectory = "";
    private static String projectName = "";
    private static File projectDir = null;
    private static String tmpDirPath = "";
    private static HashMap<String, ArrayList<String>> iterationResults = new HashMap<>();

    private static void printMetrics() {
        Function<Timer, Integer> visitTimer =
                timer -> {
                    System.out.println(
                            timer.getId().getName()
                                    + " for iteration: "
                                    + currentIteration
                                    + timer.getId().getTag("model")
                                    + " : "
                                    + timer.totalTime(TimeUnit.SECONDS)
                                    + " secs");
                    return 0;
                };
        Metrics.globalRegistry.forEachMeter(
                meter -> meter.match(null, null, visitTimer, null, null, null, null, null, null));
        Metrics.globalRegistry.clear();
    }

    public static IStatus performPRAAnalysis() throws InterruptedException {
        try {

            VerdictHandlersUtils.printGreeting();
            String dockerImage = BundlePreferences.getDockerImage();
            String bundleJar = BundlePreferences.getBundleJar();

            if (dockerImage.isEmpty() && bundleJar.isEmpty()) {
                System.out.println("Please set VERDICT Bundle Jar path in Preferences");
                VerdictHandlersUtils.finishRun();
                return Status.CANCEL_STATUS;
            }
            Timer.Sample sample = Timer.start(Metrics.globalRegistry);
            File tmpDir = java.nio.file.Files.createTempDirectory(projectName).toFile();
            tmpDirPath = tmpDir.getAbsolutePath();
            runKind2(projectDir);

            if (!isCRVUnsafe(0)) {
                VerdictLogger.info("The latest AADL model is safe");
                VerdictHandlersUtils.finishRun();
                // showPRAResultsView(parseKind2Results(new
                // File(System.getProperty("java.io.tmpdir"), "crv_output.xml")));
                return Status.OK_STATUS;
            }

            for (int iteration = 1; iteration <= PRASettingsPanel.getMaxIterations(); iteration++) {
                currentIteration = iteration;
                // Run Kind2
                VerdictLogger.info("Running Kind2 on " + projectDir + ", iteration: " + iteration);

                VerdictLogger.info("Temp Dir: " + tmpDirPath);
                File vdm = new File(tmpDirPath + "/behavior.xml");
                runAadl2Vdm(projectDir, vdm);
                VerdictBundleCommand command = new VerdictBundleCommand();
                command.jarOrImage("", BundlePreferences.getPraBin())
                        .argBind2(new File(tmpDirPath).getCanonicalPath(), "/tmp");
                int status = command.runJarOrImage();
                if (status != 0) {
                    VerdictLogger.severe(
                            "An error occured when running the PRA Docker Container with Image: "
                                    + BundlePreferences.getPraBin());
                    VerdictHandlersUtils.finishRun();
                    return Status.CANCEL_STATUS;
                } else {
                    try {
                        Files.copy(
                                new File(tmpDirPath + "/suggestion.xml"),
                                new File(BundlePreferences.getPraOutput() + "/suggestion.xml"));
                        VerdictLogger.info(
                                "suggestion.xml written to path: "
                                        + BundlePreferences.getPraOutput());

                        // Based on suggestion.xml, extract values and substitute them in agree
                        // constants and run Kind2
                        NodeList nList = readProofRepairSuggestion();
                        updateAgreeConstants(nList);

                    } catch (/* IOException */ Exception e) {
                        VerdictLogger.severe(
                                "Error generating suggestion xml at the configured output path: "
                                        + BundlePreferences.getPraOutput());
                        VerdictHandlersUtils.finishRun();
                        return Status.CANCEL_STATUS;
                    }
                }

                // run Kind2
                sample.stop(Metrics.timer("Timer.pra", "model", "PRA"));
                printMetrics();
                sample = Timer.start(Metrics.globalRegistry);
                runKind2(projectDir);
                if (!isCRVUnsafe(iteration)) {
                    VerdictLogger.info("The latest AADL model is safe");
                    VerdictHandlersUtils.finishRun();
                    // showPRAResultsView(parseKind2Results(new
                    // File(System.getProperty("java.io.tmpdir"), "crv_output.xml")));
                    return Status.OK_STATUS;
                }
                /*
                 * VerdictHandlersUtils.modifyAgreeDocuments(project, (file, resource) -> { if
                 * (resource != null) { resource.getAllContents().forEachRemaining(obj -> {
                 * if(obj instanceof com.rockwellcollins.atc.agree.agree.IntLitExpr) {
                 * System.out.println(((com.rockwellcollins.atc.agree.agree.IntLitExpr)
                 * obj).getVal()); ((com.rockwellcollins.atc.agree.agree.IntLitExpr)
                 * obj).setVal("111");
                 *
                 * } }); } });
                 */
            }
        } catch (IOException e) {
            VerdictLogger.severe("ERROR when trying to run the oyster-ml docker container");
            return Status.CANCEL_STATUS;
        } finally {
            VerdictHandlersUtils.finishRun();
        }

        VerdictLogger.info(
                "Could not repair the AADL model within "
                        + PRASettingsPanel.getMaxIterations()
                        + " number of iterations");
        VerdictLogger.info(
                "Proof Repair Analysis has reached the configured maximum number of iterations");
        VerdictHandlersUtils.finishRun();
        return Status.OK_STATUS;
    }

    public static void initPRAAnalysis() {
        currentIteration = 0;
        iterationResults.clear();
        showPRAResultsView(iterationResults);
    }

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {

        if (!saveEditor()) {
            return null;
        }
        initPRAAnalysis();

        Metrics.addRegistry(new SimpleMeterRegistry(SimpleConfig.DEFAULT, Clock.SYSTEM));

        if (VerdictHandlersUtils.startRun()) {
            // Print on console
            IIntroPart introPart = PlatformUI.getWorkbench().getIntroManager().getIntro();
            PlatformUI.getWorkbench().getIntroManager().closeIntro(introPart);
            final IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindow(event);
            VerdictHandlersUtils.setPrintOnConsole("PRA Output");
            final Display mainThreadDisplay = Display.getCurrent();
            List<String> selection = VerdictHandlersUtils.getCurrentSelection(event);
            projectDir = new File(selection.get(0));
            projectDirectory = projectDir.getAbsolutePath();
            projectName = projectDir.getName();

            IJobChangeListener praDoneListener =
                    new IJobChangeListener() {

                        @Override
                        public void aboutToRun(IJobChangeEvent event) {
                            // TODO Auto-generated method stub

                        }

                        @Override
                        public void awake(IJobChangeEvent event) {
                            // TODO Auto-generated method stub

                        }

                        @Override
                        public void done(IJobChangeEvent event) {
                            // TODO Auto-generated method stub
                            showPRAResultsView(iterationResults);
                            if (currentIteration + 1 == PRASettingsPanel.getMaxIterations()) {
                                VerdictHandlersUtils.finishRun();
                            }
                        }

                        @Override
                        public void running(IJobChangeEvent event) {
                            // TODO Auto-generated method stub

                        }

                        @Override
                        public void scheduled(IJobChangeEvent event) {
                            // TODO Auto-generated method stub

                        }

                        @Override
                        public void sleeping(IJobChangeEvent event) {
                            // TODO Auto-generated method stub

                        }
                    };

            Job job =
                    new Job("Performing Proof Repair Analysis") {
                        @Override
                        protected IStatus run(IProgressMonitor monitor) {
                            try {
                                performPRAAnalysis();
                            } catch (InterruptedException e) {
                                // TODO Auto-generated catch block
                                e.printStackTrace();
                            }
                            return Status.OK_STATUS;
                        }
                    };
            job.addJobChangeListener(praDoneListener);
            job.schedule();
        }

        return null;
    }

    public static void showPRAResultsView(HashMap<String, ArrayList<String>> kind2Results) {

        PRAResultsView.kind2Results = kind2Results;
        Display.getDefault()
                .asyncExec(
                        () -> {
                            org.apache.commons.lang3.tuple.Pair<IWorkbenchPage, IViewPart> pair =
                                    ViewUtils.getPageAndViewByViewId(PRAResultsView.ID);
                            if (pair != null && pair.getLeft() != null && pair.getRight() != null) {
                                pair.getLeft().hideView(pair.getRight());
                                try {
                                    pair.getLeft().showView(PRAResultsView.ID);
                                } catch (PartInitException e) {
                                    // TODO Auto-generated catch block
                                    e.printStackTrace();
                                }
                            }
                        });
    }

    /**
     * Calls Aadl2Vdm translator and writes model to vdmFile
     *
     * @param dir
     * @param vdmFile
     */
    public static void runAadl2Vdm(File dir, File vdmFile) {
        Agree2Vdm agree2vdm = new Agree2Vdm();
        Model model = agree2vdm.executeForOyster(dir);
        VdmTranslator.marshalToXml(model, vdmFile);
    }

    public static boolean runBundle(
            String bundleJar,
            String dockerImage,
            String projectName,
            String praBin,
            String outputXml)
            throws IOException {

        VerdictBundleCommand command = new VerdictBundleCommand();
        command.jarOrImage(bundleJar, dockerImage)
                .arg("--csv")
                .arg(projectName)
                .arg("--pra")
                .arg(praBin)
                .arg(outputXml);

        int code = command.runJarOrImage();
        return code == 0;
    }

    public static boolean isCRVUnsafe(int iteration) {

        // Parse "Answer" tags from crv_output.xml and check for any "invalid" answer
        Set<String> propertyNames = iterationResults.keySet();
        for (String propertyName : propertyNames) {
            if (!iterationResults.get(propertyName).get(iteration).equals("valid")) {
                return true;
            }
        }
        return false;
    }

    public static HashMap<String, ArrayList<String>> parseKind2Results(File fCRVOutput) {

        DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
        DocumentBuilder dBuilder = null;
        Document doc = null;
        try {
            dBuilder = dbFactory.newDocumentBuilder();
            doc = dBuilder.parse(fCRVOutput);
        } catch (Exception e) {
            VerdictLogger.severe("ERROR loading and parsing of Kind2 CRV Output XML file");
            return null;
        }
        doc.getDocumentElement().normalize();
        NodeList properties = doc.getElementsByTagName("Property");
        for (int i = 0; i < properties.getLength(); i++) {
            String propertyName =
                    properties.item(i).getAttributes().getNamedItem("name").getTextContent();
            // find Answer node
            NodeList children = properties.item(i).getChildNodes();
            for (int j = 0; j < children.getLength(); j++) {
                if (children.item(j).getNodeName().equals("Answer")) {
                    String propertyResult = children.item(j).getTextContent();
                    ArrayList<String> propertyResults = iterationResults.get(propertyName);
                    if (propertyResults == null) {
                        propertyResults = new ArrayList<>();
                    }
                    propertyResults.add(propertyResult);
                    iterationResults.put(propertyName, propertyResults);
                    break;
                }
            }
        }

        /*
         * NodeList nList = doc.getElementsByTagName("Answer"); for (int i = 0; i <
         * nList.getLength(); i++) { if
         * (!nList.item(i).getTextContent().equals("valid")) { return true; } } return
         * false;
         */
        return iterationResults;
    }

    public static void runKind2(File projectDir) {

        // invoke kind2 on project's aadl models
        try {
            String dockerImage = BundlePreferences.getDockerImage();
            String bundleJar = BundlePreferences.getBundleJar();
            if (dockerImage.isEmpty() && bundleJar.isEmpty()) {
                System.out.println("Please set VERDICT Bundle Jar path in Preferences");
                return;
            }
            String kind2Bin = BundlePreferences.getKind2Bin();
            if (dockerImage.isEmpty() && kind2Bin.isEmpty()) {
                System.out.println("Please set kind2 binary path in Preferences");
                return;
            }

            File vdmFile =
                    new File(System.getProperty("java.io.tmpdir"), projectDir.getName() + ".xml");
            runAadl2Vdm(projectDir, vdmFile);
            File crvOutput = new File(System.getProperty("java.io.tmpdir"), "crv_output.xml");
            String outputPath = crvOutput.getAbsolutePath();
            // monitor.setTaskName("Running Kind2");
            if (CRVHandler.runBundle(bundleJar, dockerImage, vdmFile, outputPath, kind2Bin)) {
                // Kind2 ran successfully, copy crv_output.xml into shared folder for oyster-ml
                // docker
                Files.copy(
                        new File(outputPath),
                        new File(new File(tmpDirPath).getAbsolutePath() + "/crv_output.xml"));
                HashMap<String, ArrayList<String>> kind2Results = parseKind2Results(crvOutput);
                showPRAResultsView(kind2Results);
            }
        } catch (IOException e) {
            VerdictLogger.severe(e.toString());
        }
    }

    public static NodeList readProofRepairSuggestion() {
        // Currently, making a lot of assumptions on the suggestions.xml that is being
        // read
        // The suggestions.xml contains suggested start times for apps from AADL model
        // Current format of suggestions.xml prediction is: <Prediction(\d)+
        // APP_start_time="(\d+)" /> in regex
        VerdictLogger.info("Reading suggestions from Machine Learning Model");
        File suggestionXml = new File(BundlePreferences.getPraOutput() + "/suggestion.xml");
        if (!suggestionXml.exists()) {
            VerdictLogger.severe(
                    "suggestion.xml does not exist, please set a valid output path for Proof Repair Analysis");
            return null;
        }
        DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
        DocumentBuilder dBuilder = null;
        Document doc = null;
        try {
            dBuilder = dbFactory.newDocumentBuilder();
            doc = dBuilder.parse(suggestionXml);
        } catch (Exception e) {
            VerdictLogger.severe(
                    "ERROR loading and parsing of Proof Repair XML file suggested by Machine Learning Component");
            return null;
        }
        doc.getDocumentElement().normalize();
        NodeList nList = doc.getElementsByTagName("prediction");
        return nList;
    }

    public static void updateAgreeConstants(NodeList nList) {
        // Assumed that the list of changes are supplied in input nList, and that only
        // agree constants from Agree_Consts.aadl are update
        int length = nList.getLength();
        List<String> linesIn = null;
        List<String> linesOut = new ArrayList<>();
        Path path = null;
        path = Paths.get(projectDirectory + "/Agree_Consts.aadl");
        if (path == null) {
            VerdictLogger.severe("Agree_Consts.aadl does not exist, please check");
            return;
        }

        try {
            linesIn = java.nio.file.Files.readAllLines(path);
        } catch (IOException e1) {

            VerdictLogger.severe("Cannot read lines from Agree_Consts.aadl");
            return;
        }

        linesIn.forEach(
                line -> {
                    boolean bReplaced = false;
                    for (int i = 0; i < length; i++) { // length is currently small
                        NamedNodeMap attrs = nList.item(i).getAttributes();
                        String agreeConstant = attrs.getNamedItem("agree-constant").getNodeValue();
                        String suggestedValue =
                                attrs.getNamedItem("suggested-value").getNodeValue();
                        if (line.contains(agreeConstant)) {
                            String lineReplaced = line.replaceAll("\\d+", suggestedValue);
                            linesOut.add(lineReplaced);
                            bReplaced = true;
                            break;
                        }
                    }
                    if (!bReplaced) {
                        linesOut.add(line);
                    }
                });
        try {
            java.nio.file.Files.write(path, linesOut);
        } catch (IOException e) {
            VerdictLogger.severe("Error writing back to Agree_Consts.aadl");
        }
    }

    public static int getCurrentIteration() {
        return currentIteration;
    }

    public static boolean saveEditor() {
        Shell shell = new Shell();
        // save the invoking .aadl editor if it has unsaved content
        IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
        IEditorPart openEditor = page.getActiveEditor();
        if (openEditor != null) {
            boolean response = page.saveEditor(openEditor, true);
            if (response && openEditor.isDirty()) {
                MessageDialog.openError(
                        shell,
                        "PRA Analysis",
                        "Please save unsaved content in the file before proceeding.");
                return false;
            }
        }
        return true;
    }
}
