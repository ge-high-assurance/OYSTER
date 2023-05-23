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
import com.ge.research.osate.verdict.gui.CRVReportGenerator;
import com.ge.research.osate.verdict.gui.CRVSettingsPanel;
import com.ge.verdict.vdm.VdmTranslator;
import java.io.File;
import java.io.IOException;
import java.util.List;
import org.apache.commons.io.FileUtils;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.intro.IIntroPart;
import verdict.vdm.vdm_model.Model;

public class ProofCertificateHandler extends AbstractHandler {

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        if (VerdictHandlersUtils.startRun()) {
            // Print on console
            IIntroPart introPart = PlatformUI.getWorkbench().getIntroManager().getIntro();
            PlatformUI.getWorkbench().getIntroManager().closeIntro(introPart);
            final IWorkbenchWindow iWindow = HandlerUtil.getActiveWorkbenchWindow(event);
            VerdictHandlersUtils.setPrintOnConsole("CRV Output");
            final Display mainThreadDisplay = Display.getCurrent();

            // Set up the thread to invoke the translators and Kind2
            Thread kpgAnalysisThread =
                    new Thread() {
                        @Override
                        public void run() {
                            try {
                                String dockerImage = BundlePreferences.getDockerImage();
                                String bundleJar = BundlePreferences.getBundleJar();
                                if (dockerImage.isEmpty() && bundleJar.isEmpty()) {
                                    System.out.println(
                                            "Please set VERDICT Bundle Jar path in Preferences");
                                    return;
                                }
                                String kind2Bin = BundlePreferences.getKind2Bin();
                                if (dockerImage.isEmpty() && kind2Bin.isEmpty()) {
                                    System.out.println(
                                            "Please set kind2 binary path in Preferences");
                                    return;
                                }

                                VerdictHandlersUtils.printGreeting();

                                List<String> selection =
                                        VerdictHandlersUtils.getCurrentSelection(event);
                                File projectDir = new File(selection.get(0));
                                File vdmFile =
                                        new File(
                                                System.getProperty("java.io.tmpdir"),
                                                projectDir.getName() + ".xml");
                                runAadl2Vdm(projectDir, vdmFile);

                                String jkindBin = BundlePreferences.getJKindBin();
                                String certificatePath = BundlePreferences.getCertificatePath();

                                String outputPath =
                                        new File(
                                                        System.getProperty("java.io.tmpdir"),
                                                        "crv_output.xml")
                                                .getCanonicalPath();
                                String outputPathBa =
                                        new File(
                                                        System.getProperty("java.io.tmpdir"),
                                                        "crv_output_ba.xml")
                                                .getCanonicalPath();

                                // clear contents of certificatePath folder before invoking proof
                                // generation
                                File certificateDir = new File(certificatePath);
                                if (!certificateDir.exists() || !certificateDir.isDirectory()) {
                                    VerdictLogger.severe(
                                            "Configured proof output folder: "
                                                    + certificatePath
                                                    + " is either missing or not a directory");
                                }
                                FileUtils.cleanDirectory(certificateDir);
                                if (runBundle(
                                        bundleJar,
                                        dockerImage,
                                        vdmFile,
                                        outputPath,
                                        kind2Bin,
                                        jkindBin,
                                        certificatePath)) {
                                    // Run this code on the UI thread
                                    mainThreadDisplay.asyncExec(
                                            () -> {
                                                new CRVReportGenerator(
                                                        outputPath, outputPathBa, iWindow);
                                            });
                                }
                            } catch (IOException e) {
                                VerdictLogger.severe(e.toString());
                            } finally {
                                VerdictHandlersUtils.finishRun();
                            }
                        }
                    };
            kpgAnalysisThread.start();
        }
        return null;
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
            File vdmFile,
            String outputPath,
            String kind2bin,
            String jkindbin,
            String certificatePath)
            throws IOException {

        VerdictBundleCommand command = new VerdictBundleCommand();
        command.jarOrImage(bundleJar, dockerImage)
                .arg("--vdm")
                .argBind(vdmFile.getCanonicalPath(), "/app/vdm/" + vdmFile.getName())
                .arg("--kpg")
                .argBind(outputPath, "/app/tmp/crv_output.xml")
                .argBind2(certificatePath, "/app/output/")
                .arg2(kind2bin, "/app/kind2")
                .arg(jkindbin)
                .arg(
                        (dockerImage != null && !dockerImage.isEmpty())
                                ? "/app/output"
                                : certificatePath); // use /app/output if using a docker image
        // otherwise, use certificatePath when running
        // native

        if (CRVSettingsPanel.isSmtLib) {
            command.arg("-SMT");
        }
        if (CRVSettingsPanel.isLFSC) {
            command.arg("-LFSC");
        }

        int code = command.runJarOrImage();
        return code == 0;
    }
}
