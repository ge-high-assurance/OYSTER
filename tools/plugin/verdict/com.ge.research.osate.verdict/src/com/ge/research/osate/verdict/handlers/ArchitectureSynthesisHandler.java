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
import com.ge.oyster.translators.Odm2Z3;
import com.ge.oyster.translators.Odm2Z3Result;
import com.ge.oyster.translators.Z32AADL;
import com.ge.research.osate.verdict.gui.IMASynthesisSettingsPanel;

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
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.intro.IIntroPart;
import org.zeroturnaround.exec.InvalidExitValueException;

import java.io.File;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;

public class ArchitectureSynthesisHandler extends AbstractHandler {

    private static void printMetrics() {
        Function<Timer, Integer> visitTimer =
                timer -> {
                    System.out.println(
                            timer.getId().getName()
                                    + " for "
                                    + timer.getId().getTag("model")
                                    + ": "
                                    + timer.totalTime(TimeUnit.SECONDS)
                                    + " secs");
                    return 0;
                };
        Metrics.globalRegistry.forEachMeter(
                meter -> meter.match(null, null, visitTimer, null, null, null, null, null, null));
        Metrics.globalRegistry.clear();
    }

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        Metrics.addRegistry(new SimpleMeterRegistry(SimpleConfig.DEFAULT, Clock.SYSTEM));
        if (VerdictHandlersUtils.startRun()) {
            // Print on console
            IIntroPart introPart = PlatformUI.getWorkbench().getIntroManager().getIntro();
            PlatformUI.getWorkbench().getIntroManager().closeIntro(introPart);
            final IWorkbenchWindow iWindow = HandlerUtil.getActiveWorkbenchWindow(event);
            VerdictHandlersUtils.setPrintOnConsole("\n\n Info: Architecture Synthesis Output");
            final Display mainThreadDisplay = Display.getCurrent();
            Timer.Sample sample = Timer.start(Metrics.globalRegistry);
            Thread praAnalysisThread =
                    new Thread() {
                        @Override
                        public void run() {
                            try {

                                VerdictHandlersUtils.printGreeting();
                                Odm2Z3.vlEndsAtGPM.clear();
                                Odm2Z3.vlStartsFromGPM.clear();
                                Odm2Z3.PortConnectionMap.clear();
                                Odm2Z3.PortConnectionMapForZ3.clear();
                                Timer.Sample sample = Timer.start(Metrics.globalRegistry);
                                List<String> selection =
                                        VerdictHandlersUtils.getCurrentSelection(event);
                                File projectDir = new File(selection.get(0));

                                IProject project = VerdictHandlersUtils.getCurrentIProject(event);
                                Aadl2Odm a2o = new Aadl2Odm();
                                ImmutablePair<oyster.odm.odm_model.Model, List<EObject>>
                                        AADL2OdmRes = a2o.execute(projectDir);
                                Odm2Z3 o = new Odm2Z3();

                                Odm2Z3Result result =
                                        o.execute(AADL2OdmRes.left, AADL2OdmRes.right, true, false);

                                if (result == null && !IMASynthesisSettingsPanel.unsatCoreYes) {
                                    return;
                                }

                                if (result == null && IMASynthesisSettingsPanel.unsatCoreYes) {
                                    // re-run Non-VL constraints and report the unsat core;
                                    (new Odm2Z3())
                                            .execute(
                                                    AADL2OdmRes.left,
                                                    AADL2OdmRes.right,
                                                    true,
                                                    true);
                                    return;
                                }

                                if (!Objects.isNull(result)) {

                                    Odm2Z3 o2 = new Odm2Z3();
                                    Odm2Z3Result result2 =
                                            o2.execute(
                                                    AADL2OdmRes.left,
                                                    AADL2OdmRes.right,
                                                    false,
                                                    false);
                                    if (result2 == null
                                            && !IMASynthesisSettingsPanel.unsatCoreYes) {
                                        return;
                                    }

                                    if (result2 == null && IMASynthesisSettingsPanel.unsatCoreYes) {
                                        // re-run Non-VL constraints and report the unsat core;
                                        (new Odm2Z3())
                                                .execute(
                                                        AADL2OdmRes.left,
                                                        AADL2OdmRes.right,
                                                        false,
                                                        true);
                                        return;
                                    }
                                    System.out.println(
                                            "Info: A feasible solution found by the SMT Solver");
                                    VerdictLogger.info(
                                            "Writing the synthesized AADL architecture to file...");
                                    Z32AADL z = new Z32AADL();

                                    List<EObject> synAadlObjects =
                                            z.execute(
                                                    result.getModel(),
                                                    result.getCtx(),
                                                    result2.getModel(),
                                                    result2.getCtx(),
                                                    project,
                                                    result.getFlowNamesToSrcDestInstance(),
                                                    result.getInstanceBoundTohostCompName(),
                                                    AADL2OdmRes.right);
                                    result.getCtx().close();
                                    result2.getCtx().close();

                                    sample.stop(
                                            Metrics.timer(
                                                    "Timer.imasynth", "model", "IMA Synthesis"));
                                    VerdictLogger.info("Finished writing to an AADL file");
                                    printMetrics();
                                }
                            } catch (InvalidExitValueException e) {
                                // TODO Auto-generated catch block
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
}
