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

import com.ge.oyster.translators.Aadl2Odm;
import com.ge.research.osate.verdict.gui.BundlePreferences;
import com.ge.research.osate.verdict.gui.TSNSchedSettingsPanel;
import com.ge.research.osate.verdict.gui.TSNView;
import com.ge.research.osate.verdict.gui.ViewUtils;
import com.google.common.io.FileWriteMode;
import com.google.common.io.Files;

import io.micrometer.core.instrument.Clock;
import io.micrometer.core.instrument.Metrics;
import io.micrometer.core.instrument.Timer;
import io.micrometer.core.instrument.simple.SimpleConfig;
import io.micrometer.core.instrument.simple.SimpleMeterRegistry;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IProject;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.intro.IIntroPart;
import org.osate.aadl2.EndToEndFlow;
import org.osate.aadl2.EndToEndFlowElement;
import org.osate.aadl2.EndToEndFlowSegment;
import org.osate.aadl2.FlowElement;
import org.osate.aadl2.FlowImplementation;
import org.osate.aadl2.FlowKind;
import org.osate.aadl2.FlowSegment;
import org.osate.aadl2.PropertyAssociation;
import org.osate.aadl2.SystemImplementation;
import org.osate.aadl2.impl.FlowSpecificationImpl;
import org.zeroturnaround.exec.ProcessExecutor;

import java.io.File;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class ValidateTSNScheduleHandler extends AbstractHandler {

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        Metrics.addRegistry(new SimpleMeterRegistry(SimpleConfig.DEFAULT, Clock.SYSTEM));
        if (VerdictHandlersUtils.startRun()) {
            // Print on console
            IIntroPart introPart = PlatformUI.getWorkbench().getIntroManager().getIntro();
            PlatformUI.getWorkbench().getIntroManager().closeIntro(introPart);
            final IWorkbenchWindow iWindow = HandlerUtil.getActiveWorkbenchWindow(event);
            VerdictHandlersUtils.setPrintOnConsole("\n\n Info: Validate TSN schedules");
            Thread praAnalysisThread =
                    new Thread() {
                        @Override
                        public void run() {
                            try {

                                VerdictHandlersUtils.printGreeting();

                                Timer.Sample sample = Timer.start(Metrics.globalRegistry);
                                List<String> selection =
                                        VerdictHandlersUtils.getCurrentSelection(event);
                                File projectDir = new File(selection.get(0));

                                IProject project = VerdictHandlersUtils.getCurrentIProject(event);
                                Aadl2Odm a2o = new Aadl2Odm();
                                ImmutablePair<oyster.odm.odm_model.Model, List<EObject>>
                                        AADL2OdmRes = a2o.execute(projectDir);

                                // Extract TSN schedule from TSN streams (aka VLs)

                                // index all system implementations
                                Map<String, SystemImplementation> sysImpls = new HashMap<>();
                                Map<String, List<String>> vlPaths = new HashMap<>();
                                HashMap<String, Boolean> tsnValidation = new HashMap<>();
                                HashMap<String, Boolean> tsnLFSCValidation = new HashMap<>();
                                HashMap<String, Boolean> tsnAletheValidation = new HashMap<>();

                                Map<String, Map<String, Integer>> tsnProps = new HashMap<>();
                                for (Object object : AADL2OdmRes.right) {
                                    if (object instanceof SystemImplementation) {
                                        SystemImplementation sysImpl =
                                                (SystemImplementation) object;
                                        sysImpls.put(sysImpl.getName().split("\\.")[1], sysImpl);
                                    }
                                }

                                for (Object object : AADL2OdmRes.right) {
                                    if (object instanceof SystemImplementation) {
                                        SystemImplementation sysImpl =
                                                (SystemImplementation) object;
                                        if (sysImpl.getName().equals("IMA.Impl")) {
                                            List<EndToEndFlow> e2eFlows =
                                                    sysImpl.getAllEndToEndFlows();
                                            for (EndToEndFlow e2eFlow : e2eFlows) {
                                                List<String> components = new ArrayList<>();
                                                List<EndToEndFlowSegment> flowSegments =
                                                        e2eFlow.getAllFlowSegments();
                                                for (EndToEndFlowSegment flowSegment :
                                                        flowSegments) {
                                                    if (flowSegment.getContext() == null) {
                                                        continue;
                                                    }
                                                    EndToEndFlowElement flowElement =
                                                            flowSegment.getFlowElement();
                                                    if (flowElement
                                                            instanceof FlowSpecificationImpl) {
                                                        FlowSpecificationImpl flowSpecImpl =
                                                                (FlowSpecificationImpl) flowElement;
                                                        FlowKind flowKind = flowSpecImpl.getKind();
                                                        if (flowKind.equals(FlowKind.SOURCE)
                                                                || flowKind.equals(FlowKind.SINK)
                                                                || flowKind.equals(FlowKind.PATH)) {
                                                            // skip
                                                            components.add(
                                                                    flowSegment
                                                                            .getContext()
                                                                            .getName()
                                                                            .toString());
                                                            Object flowSpecObj =
                                                                    (Object) flowSpecImpl;
                                                            traverseFlowSegment(
                                                                    flowSegment
                                                                            .getContext()
                                                                            .getName(),
                                                                    flowSpecObj,
                                                                    components,
                                                                    sysImpls);
                                                        } else {
                                                            // recursively get sub-flows
                                                            int a = 0;
                                                            a++;
                                                        }

                                                        int a = 0;
                                                        a++;
                                                    }
                                                }

                                                vlPaths.put(e2eFlow.getName(), components);
                                                Map<String, Integer> tsnSchedProps =
                                                        new HashMap<>();
                                                List<PropertyAssociation> propAssocs =
                                                        e2eFlow.getOwnedPropertyAssociations();
                                                for (PropertyAssociation propAssoc : propAssocs) {
                                                    if (propAssoc
                                                            .getProperty()
                                                            .getName()
                                                            .equals("tsn_sched_start_time")) {
                                                        int start_time =
                                                                Integer.parseInt(
                                                                        propAssoc
                                                                                .getOwnedValues()
                                                                                .get(0)
                                                                                .getOwnedValue()
                                                                                .toString());
                                                        tsnSchedProps.put(
                                                                "tsn_sched_start_time", start_time);
                                                    }

                                                    if (propAssoc
                                                            .getProperty()
                                                            .getName()
                                                            .equals("tsn_sched_arrival_limit")) {
                                                        int arrival_limit =
                                                                Integer.parseInt(
                                                                        propAssoc
                                                                                .getOwnedValues()
                                                                                .get(0)
                                                                                .getOwnedValue()
                                                                                .toString());
                                                        tsnSchedProps.put(
                                                                "tsn_sched_arrival_limit",
                                                                arrival_limit);
                                                    }

                                                    if (propAssoc
                                                            .getProperty()
                                                            .getName()
                                                            .equals("tsn_sched_threshold")) {
                                                        int threshold =
                                                                Integer.parseInt(
                                                                        propAssoc
                                                                                .getOwnedValues()
                                                                                .get(0)
                                                                                .getOwnedValue()
                                                                                .toString());
                                                        tsnSchedProps.put(
                                                                "tsn_sched_threshold", threshold);
                                                    }

                                                    if (propAssoc
                                                            .getProperty()
                                                            .getName()
                                                            .equals("tsn_link_bandwidth")) {
                                                        int link_bw =
                                                                Integer.parseInt(
                                                                        propAssoc
                                                                                .getOwnedValues()
                                                                                .get(0)
                                                                                .getOwnedValue()
                                                                                .toString());
                                                        tsnSchedProps.put(
                                                                "tsn_link_bandwidth", link_bw);
                                                    }

                                                    if (propAssoc
                                                            .getProperty()
                                                            .getName()
                                                            .equals("tsn_frame_size")) {
                                                        int frame_size =
                                                                Integer.parseInt(
                                                                        propAssoc
                                                                                .getOwnedValues()
                                                                                .get(0)
                                                                                .getOwnedValue()
                                                                                .toString());
                                                        tsnSchedProps.put(
                                                                "tsn_frame_size", frame_size);
                                                    }
                                                }

                                                tsnProps.put(e2eFlow.getName(), tsnSchedProps);
                                            }

                                            // generate smt delay calculations

                                            for (String key : vlPaths.keySet()) {
                                                String lemma =
                                                        "(assert (>= arrival_time (+ arrival_limit threshold)))\n";
                                                String smtPreamble =
                                                        "(set-logic QF_LIA)\n"
                                                                + "(declare-fun latency () Int)\n"
                                                                + "(declare-fun threshold () Int)\n"
                                                                + "(declare-fun start_time () Int)\n"
                                                                + "(declare-fun formula () Int)\n"
                                                                + "(declare-fun arrival_time () Int)\n"
                                                                + "(declare-fun arrival_limit () Int)\n"
                                                                + "(assert (= start_time "
                                                                + tsnProps.get(key)
                                                                        .get("tsn_sched_start_time")
                                                                + "))\n"
                                                                + "(assert (= threshold "
                                                                + tsnProps.get(key)
                                                                        .get("tsn_sched_threshold")
                                                                + "))\n"
                                                                + "(assert (= arrival_limit "
                                                                + tsnProps.get(key)
                                                                        .get(
                                                                                "tsn_sched_arrival_limit")
                                                                + "))\n";

                                                String smtDelay = "";
                                                Set<String> visited = new HashSet<>();
                                                List<String> flowElements = vlPaths.get(key);

                                                List<String> delayVariables =
                                                        new ArrayList<String>();
                                                for (String flowElement : flowElements) {

                                                    // component, delay charged component egress and
                                                    // ingress, except at source and
                                                    // destination
                                                    String component = flowElement;
                                                    if (visited.contains(component)) {
                                                        continue;
                                                    } else {
                                                        visited.add(component);
                                                    }

                                                    if (flowElement.contains("CCR")) {
                                                        continue;
                                                    }

                                                    if (flowElement.contains("ACS")) {
                                                        int ideal_max_ptp = 50;
                                                        int ideal_max_qbv = 50;
                                                        int tas_jitter =
                                                                ideal_max_ptp + ideal_max_qbv;
                                                        int ingress_delay = 9;
                                                        int egress_delay = 9;
                                                        int sw_fabric_delay = 1008;
                                                        String comp_egress_delay =
                                                                component + "_egress_delay";
                                                        String comp_fabric_delay =
                                                                component + "_fabric_delay";
                                                        String comp_ingress_delay =
                                                                component + "_ingress_delay";

                                                        String comp_tas_jitter =
                                                                component + "_tas_jitter";

                                                        String declare_egress_delay =
                                                                "(declare-fun "
                                                                        + comp_egress_delay
                                                                        + "  () Int)";
                                                        String declare_fabric_delay =
                                                                "(declare-fun "
                                                                        + comp_fabric_delay
                                                                        + "  () Int)";
                                                        String declare_ingress_delay =
                                                                "(declare-fun "
                                                                        + comp_ingress_delay
                                                                        + "  () Int)";

                                                        String declare_comp_tasjitter =
                                                                "(declare-fun "
                                                                        + comp_tas_jitter
                                                                        + "  () Int)";

                                                        String assert_egress_delay =
                                                                "(assert (= "
                                                                        + comp_egress_delay
                                                                        + " "
                                                                        + egress_delay
                                                                        + "))";
                                                        String assert_fabric_delay =
                                                                "(assert (= "
                                                                        + comp_fabric_delay
                                                                        + " "
                                                                        + sw_fabric_delay
                                                                        + "))";
                                                        String assert_ingress_delay =
                                                                "(assert (= "
                                                                        + comp_ingress_delay
                                                                        + " "
                                                                        + ingress_delay
                                                                        + "))";

                                                        String assert_tasjitter =
                                                                "(assert (= "
                                                                        + comp_tas_jitter
                                                                        + " "
                                                                        + tas_jitter
                                                                        + "))";

                                                        smtDelay +=
                                                                declare_egress_delay
                                                                        + "\n"
                                                                        + declare_fabric_delay
                                                                        + "\n"
                                                                        + declare_ingress_delay
                                                                        + "\n"
                                                                        + declare_comp_tasjitter
                                                                        + "\n"
                                                                        + assert_egress_delay
                                                                        + "\n"
                                                                        + assert_fabric_delay
                                                                        + "\n"
                                                                        + assert_ingress_delay
                                                                        + "\n"
                                                                        + assert_tasjitter
                                                                        + "\n";

                                                        delayVariables.add(comp_egress_delay);
                                                        delayVariables.add(comp_fabric_delay);
                                                        delayVariables.add(comp_ingress_delay);
                                                        delayVariables.add(comp_tas_jitter);

                                                    } else {
                                                        int frame_size =
                                                                tsnProps.get(key)
                                                                        .get("tsn_frame_size");
                                                        int link_bw =
                                                                tsnProps.get(key)
                                                                        .get("tsn_link_bandwidth");
                                                        int link_tx_time =
                                                                (frame_size * 8) / link_bw;
                                                        int ideal_max_ptp = 100;
                                                        int ideal_max_qbv = 100;
                                                        int tas_jitter =
                                                                ideal_max_ptp + ideal_max_qbv;
                                                        int propagation =
                                                                10; // from chronos example

                                                        String link_delay =
                                                                component + "_link_delay";
                                                        String prop_delay =
                                                                component + "_propagation_delay";
                                                        String comp_tas_jitter =
                                                                component + "_tas_jitter";

                                                        String declare_link_delay =
                                                                "(declare-fun "
                                                                        + link_delay
                                                                        + "  () Int)";

                                                        String declare_prop_delay =
                                                                "(declare-fun "
                                                                        + prop_delay
                                                                        + "  () Int)";
                                                        String declare_comp_tasjitter =
                                                                "(declare-fun "
                                                                        + comp_tas_jitter
                                                                        + "  () Int)";

                                                        String assert_link_delay =
                                                                "(assert (= "
                                                                        + link_delay
                                                                        + " "
                                                                        + link_tx_time
                                                                        + "))";
                                                        String assert_prop_delay =
                                                                "(assert (= "
                                                                        + prop_delay
                                                                        + " "
                                                                        + propagation
                                                                        + "))";
                                                        String assert_tasjitter =
                                                                "(assert (= "
                                                                        + comp_tas_jitter
                                                                        + " "
                                                                        + tas_jitter
                                                                        + "))";

                                                        delayVariables.add(link_delay);
                                                        delayVariables.add(prop_delay);
                                                        delayVariables.add(comp_tas_jitter);
                                                        smtDelay +=
                                                                declare_link_delay
                                                                        + "\n"
                                                                        + declare_prop_delay
                                                                        + "\n"
                                                                        + declare_comp_tasjitter
                                                                        + "\n"
                                                                        + assert_link_delay
                                                                        + "\n"
                                                                        + assert_prop_delay
                                                                        + "\n"
                                                                        + assert_tasjitter
                                                                        + "\n";
                                                    }
                                                }
                                                String sumDelay = "(+ ";
                                                for (String delayVar : delayVariables) {
                                                    sumDelay += delayVar + "\n";
                                                }
                                                sumDelay += ")";
                                                String assert_latency =
                                                        "(assert (= latency "
                                                                + sumDelay
                                                                + "))"
                                                                + "\n";
                                                smtDelay += assert_latency;
                                                String arrival_time =
                                                        "(assert (= arrival_time (+ start_time latency)))"
                                                                + "\n";
                                                smtDelay += arrival_time;
                                                smtDelay += "(check-sat)\n";
                                                String proofOutput =
                                                        BundlePreferences.getCertificatePath();

                                                String smtText =
                                                        smtPreamble + lemma + "\n" + smtDelay;
                                                String smtModelText =
                                                        smtPreamble
                                                                + "\n"
                                                                + smtDelay
                                                                // + "\n" + "(set-option
                                                                // :produce-models true)"
                                                                + "\n"
                                                                + "(get-model)";

                                                String smtFile = proofOutput + "/" + key + ".smt2";
                                                String smtModelFile =
                                                        proofOutput + "/" + key + "_model.smt2";
                                                File file = new File(smtFile);
                                                File modelFile = new File(smtModelFile);

                                                FileWriteMode[] modes = {};
                                                Files.asCharSink(
                                                                file,
                                                                Charset.defaultCharset(),
                                                                modes)
                                                        .write(smtText);
                                                Files.asCharSink(
                                                                modelFile,
                                                                Charset.defaultCharset(),
                                                                modes)
                                                        .write(smtModelText);

                                                Set<String> proofFormats =
                                                        TSNSchedSettingsPanel.getProofFormats();
                                                for (String proofFormat : proofFormats) {
                                                    ProcessExecutor executor =
                                                            new ProcessExecutor();
                                                    ArrayList<String> args =
                                                            new ArrayList<String>(
                                                                    Arrays.asList(
                                                                            BundlePreferences
                                                                                    .getCVC5Path(),
                                                                            "--dump-proof",
                                                                            "--proof-format-mode="
                                                                                    + proofFormat,
                                                                            "--simplification=none",
                                                                            smtFile));
                                                    executor.command(args);
                                                    executor.destroyOnExit();
                                                    executor.redirectError(System.err);
                                                    // executor.redirectOutput(System.out);
                                                    String output =
                                                            executor.readOutput(true)
                                                                    .execute()
                                                                    .outputUTF8();
                                                    if (output.equals("sat\n")) {
                                                        // constraints are unsatisfiable
                                                        VerdictLogger.info(
                                                                "TSN schedule validation failed for "
                                                                        + key);
                                                        tsnValidation.put(key, false);
                                                    } else {
                                                        String proofFile2 =
                                                                proofOutput
                                                                        + "/"
                                                                        + key
                                                                        + "."
                                                                        + "verit";
                                                        VerdictLogger.info(
                                                                "TSN schedule validated succeeded for "
                                                                        + key);
                                                        // redirect proofs to Proof output folder

                                                        // if proof mode is alethe regenerate using
                                                        // verit
                                                        if (proofFormat.equals("alethe")) {
                                                            ProcessExecutor verit =
                                                                    new ProcessExecutor();
                                                            ArrayList<String> veritArgs =
                                                                    new ArrayList<String>(
                                                                            Arrays.asList(
                                                                                    BundlePreferences
                                                                                            .getVeritPath(),
                                                                                    "--proof="
                                                                                            + proofFile2,
                                                                                    smtFile));
                                                            verit.command(veritArgs);
                                                            verit.destroyOnExit();
                                                            verit.redirectError(System.err);
                                                            verit.execute();

                                                            // alethe proof checking
                                                            if (proofFormat.equals("alethe")
                                                                    && TSNSchedSettingsPanel
                                                                            .isAletheCheckEnabled()) {
                                                                ProcessExecutor executor2 =
                                                                        new ProcessExecutor();
                                                                ArrayList<String> args2 =
                                                                        new ArrayList<String>(
                                                                                Arrays.asList(
                                                                                        BundlePreferences
                                                                                                .getAletheCheckerPath(),
                                                                                        "check",
                                                                                        proofFile2,
                                                                                        smtFile));
                                                                executor2.command(args2);
                                                                executor2.destroyOnExit();
                                                                executor2.redirectError(System.err);
                                                                // executor.redirectOutput(System.out);
                                                                String output3 =
                                                                        executor2
                                                                                .readOutput(true)
                                                                                .execute()
                                                                                .outputUTF8();
                                                                if (output3.contains("valid")) {
                                                                    // table proof check results
                                                                    tsnAletheValidation.put(
                                                                            key, true);
                                                                } else {
                                                                    tsnAletheValidation.put(
                                                                            key, false);
                                                                }
                                                            }

                                                        } else {

                                                            String proofFile =
                                                                    proofOutput
                                                                            + "/"
                                                                            + key
                                                                            + "."
                                                                            + proofFormat;
                                                            VerdictLogger.info(
                                                                    "Proof produced at "
                                                                            + proofFile);
                                                            File dotFile = new File(proofFile);
                                                            // remove unsat at the beginning of the
                                                            // dot
                                                            // proof
                                                            String output2 =
                                                                    output.replaceAll("unsat", "");
                                                            Files.asCharSink(
                                                                            dotFile,
                                                                            Charset
                                                                                    .defaultCharset(),
                                                                            modes)
                                                                    .write(output2);
                                                            tsnValidation.put(key, true);

                                                            // perform proof checking

                                                            if (proofFormat.equals("lfsc")
                                                                    && TSNSchedSettingsPanel
                                                                            .isLFSCCheckEnabled()) {
                                                                ProcessExecutor executor2 =
                                                                        new ProcessExecutor();
                                                                ArrayList<String> args2 =
                                                                        new ArrayList<String>(
                                                                                Arrays.asList(
                                                                                        BundlePreferences
                                                                                                .getLFSCCheckerPath(),
                                                                                        proofFile));
                                                                executor2.command(args2);
                                                                executor2.destroyOnExit();
                                                                executor2.redirectError(System.err);
                                                                // executor.redirectOutput(System.out);
                                                                String output3 =
                                                                        executor2
                                                                                .readOutput(true)
                                                                                .execute()
                                                                                .outputUTF8();
                                                                if (output3.contains("success")) {
                                                                    // table proof check results
                                                                    tsnLFSCValidation.put(
                                                                            key, true);
                                                                } else {
                                                                    tsnLFSCValidation.put(
                                                                            key, false);
                                                                }
                                                            }
                                                        }
                                                    }
                                                }

                                                // produce models too!
                                                ProcessExecutor executor4 = new ProcessExecutor();
                                                ArrayList<String> args3 =
                                                        new ArrayList<String>(
                                                                Arrays.asList(
                                                                        BundlePreferences
                                                                                .getCVC5Path(),
                                                                        "--produce-models",
                                                                        smtModelFile));
                                                executor4.command(args3);
                                                executor4.destroyOnExit();
                                                executor4.redirectError(System.err);
                                                String output4 =
                                                        executor4
                                                                .readOutput(true)
                                                                .execute()
                                                                .outputUTF8();
                                                String[] lines = output4.split("\n");
                                                for (String line : lines) {
                                                    if (line.contains("define-fun arrival_time")) {
                                                        String[] tokens =
                                                                line.replace(")", "").split(" ");
                                                        int arrival_time2 =
                                                                Integer.parseInt(
                                                                        tokens[tokens.length - 1]);
                                                        tsnProps.get(key)
                                                                .put(
                                                                        "tsn_sched_arrival_time",
                                                                        arrival_time2);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }

                                // show tsn validation report
                                Display.getDefault()
                                        .asyncExec(
                                                () -> {
                                                    TSNView.tsnResults = tsnValidation;
                                                    TSNView.tsnLFSCResults = tsnLFSCValidation;
                                                    TSNView.tsnAletheResults = tsnAletheValidation;
                                                    TSNView.tsnProps = tsnProps;
                                                    org.apache.commons.lang3.tuple.Pair<
                                                                    IWorkbenchPage, IViewPart>
                                                            pair =
                                                                    ViewUtils
                                                                            .getPageAndViewByViewId(
                                                                                    TSNView.ID);
                                                    if (pair != null
                                                            && pair.getLeft() != null
                                                            && pair.getRight() != null) {
                                                        pair.getLeft().hideView(pair.getRight());
                                                        try {
                                                            pair.getLeft().showView(TSNView.ID);
                                                        } catch (PartInitException e) {
                                                            // TODO Auto-generated catch block
                                                            e.printStackTrace();
                                                        }
                                                    }
                                                });

                            } catch (Exception e) {
                                e.printStackTrace();
                            } finally {
                                VerdictHandlersUtils.finishRun();
                            }
                        }
                    };

            praAnalysisThread.start();
        }
        return null;
    }

    public static void traverseFlowSegment(
            String context,
            Object flowArtifact,
            List<String> components,
            Map<String, SystemImplementation> sysImpls) {
        String component = null;
        if (flowArtifact instanceof FlowSpecificationImpl) {
            FlowSpecificationImpl flowSpecImpl = (FlowSpecificationImpl) flowArtifact;
            SystemImplementation sysImpl = sysImpls.get(context);
            List<FlowImplementation> flowImpls = sysImpl.getAllFlowImplementations();
            for (FlowImplementation flowImpl : flowImpls) {
                if (flowImpl.getName().equals(flowSpecImpl.getName())) {
                    List<FlowSegment> flowSegments = flowImpl.getOwnedFlowSegments();
                    for (FlowSegment flowSegment : flowSegments) {
                        if (flowSegment.getContext() == null) {
                            continue;
                        }
                        component = flowSegment.getContext().getName();
                        components.add(component);
                        FlowElement flowElement = flowSegment.getFlowElement();
                        if (flowElement instanceof FlowSpecificationImpl) {
                            traverseFlowSegment(component, flowElement, components, sysImpls);
                        }
                    }
                }
            }
        }
    }
}
