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

import com.ge.research.osate.verdict.gui.BundlePreferences;
import com.ge.research.osate.verdict.gui.ProofValidationSettingsPanel;
import java.io.File;
import java.io.IOException;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.intro.IIntroPart;

public class ProofValidationHandler extends AbstractHandler {

    private static final String JOB_INTRO = "Proof Validation Output";
    private static final String JOB_NAME = "Proof Validator job";

    private static final String MISSING_DOCKER_IMAGE =
            "Please configure Proof Validator docker image in Preferences";

    private static final String MISSING_PROOF_PATH =
            "Configured proof output folder: %s is either missing or not a directory";

    private static final String VALIDATION_ERROR = "Error running run proof validation";
    private static final String HEADER = "Proof Validator(s)";
    private static final String NO_PROVERS_SELECTED = "No proof validators enabled. "
    		+ "Configure in OYSTER > Proof Validation Settings";

    // Debounce runs between all threads 
    private static boolean isRunning;
    private static Object lock = new Object();

    private static boolean startRun() {
       synchronized (lock) {
	        if (!isRunning) {
	            isRunning = true;
	            return true;
	        }
	        return false;
       }
    }

    private static void endRun() {
      synchronized (lock) {
        isRunning = false;
      }
    }

    @Override
    public Object execute(final ExecutionEvent event) {

        if (!startRun()) {
            return null;
        }
        try {
        	
        	final IIntroPart introPart = PlatformUI.getWorkbench().getIntroManager().getIntro();
            PlatformUI.getWorkbench().getIntroManager().closeIntro(introPart);
            
        	VerdictHandlersUtils.setPrintOnConsole(JOB_INTRO);
        	VerdictHandlersUtils.printGreeting();
        	
            final Job proofValidationJob = new RunProofValidatorJob(JOB_NAME);
            proofValidationJob.schedule();
            proofValidationJob.join();

        } catch (final InterruptedException e) {
            VerdictLogger.severe(VALIDATION_ERROR);
        }

        endRun();
        return null;
    }

    private static class RunProofValidatorJob extends Job {

        public RunProofValidatorJob(final String name) {
            super(String.format(JOB_NAME, name));
        }

        @Override
        protected IStatus run(IProgressMonitor monitor) {
        	
        	VerdictLogger.printHeader(HEADER);
        	
        	final boolean lfscEnabled = ProofValidationSettingsPanel.isLfscEnabled();
        	final boolean z3Enabled = ProofValidationSettingsPanel.isZ3Enabled();
        	final boolean cvc5Enabled = ProofValidationSettingsPanel.isCvc5Enabled();
        	
        	if(!(lfscEnabled || z3Enabled || cvc5Enabled)) {
            	VerdictLogger.severe(NO_PROVERS_SELECTED);
            	return Status.CANCEL_STATUS; 
        	}
        	
            try {

                final String dockerImage = BundlePreferences.getProofValidationImage();

                if (dockerImage.isEmpty()) {
                    VerdictLogger.severe(MISSING_DOCKER_IMAGE);
                    return Status.CANCEL_STATUS;
                }

                final String certificatePath = BundlePreferences.getCertificatePath();

                final File certificateDir = new File(certificatePath);
                if (!certificateDir.exists() || !certificateDir.isDirectory()) {
                    VerdictLogger.severe(String.format(MISSING_PROOF_PATH, certificatePath));

                    return Status.CANCEL_STATUS;
                }
                
                runBundle(
                        dockerImage,
                        certificatePath,
                        lfscEnabled,
                        z3Enabled,
                        cvc5Enabled);

                return Status.OK_STATUS;

            } catch (final IOException e) {
                VerdictLogger.severe(e.toString());
                return Status.CANCEL_STATUS;
            }
        }
    }

    private static boolean runBundle(
            final String dockerImage,
            final String mountPath,
            final boolean lfscEnabled,
            final boolean z3Enabled,
            final boolean cvc5Enabled)
            throws IOException {

        final VerdictBundleCommand command = new VerdictBundleCommand();
        command.setDockerImage(dockerImage);
        command.arg("-l");
        command.arg(String.valueOf(lfscEnabled));
        command.arg("-z");
        command.arg(String.valueOf(z3Enabled));
        command.arg("-c");
        command.arg(String.valueOf(cvc5Enabled));
        command.argBind2(mountPath, "/proofs");
        final int code = command.runWithDocker();
        return code == 0;
    }
}
