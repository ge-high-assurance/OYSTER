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

import com.ge.research.osate.verdict.gui.AssuranceCaseSettingsPanel;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;

/**
 * @author Saswata Paul If the settings panel is not created yet, we create a new one; otherwise, we
 *     bring the old panel to the front.
 */
public class AssuranceCaseSettingsHandler extends AbstractHandler {
    private static AssuranceCaseSettingsPanel assuranceCaseSettingsWindow;

    @Override
    /** Populating settings panel */
    public Object execute(ExecutionEvent event) throws ExecutionException {

        // Creating the GSN settings window
        if (assuranceCaseSettingsWindow == null) {
            assuranceCaseSettingsWindow = new AssuranceCaseSettingsPanel();
            assuranceCaseSettingsWindow.run();
            assuranceCaseSettingsWindow = null;
        } else {
            assuranceCaseSettingsWindow.bringToFront(assuranceCaseSettingsWindow.getShell());
        }
        return null;
    }

    //	/**
    //	 * Can be used to dynamically populate the
    //	 * settings panel
    //	 */
    //	public Object execute(ExecutionEvent event) throws ExecutionException {
    //
    //		//Creating the GSN settings window
    //		if (gsnSettingsWindow == null) {
    //			/**
    //			 * Create the list of all goal ids here
    //			 * and send it to populate the panel
    //			 */
    //			List<String> selection = VerdictHandlersUtils.getCurrentSelection(event);
    //			File projectDir = new File(selection.get(0));
    //			Aadl2Vdm aadl2vdm = new Aadl2Vdm();
    //			List<String> allReqIds =
    // populateVdmWithOnlyRequirementIds(aadl2vdm.preprocessAadlFiles(projectDir));
    //			//sending list to populate GSN settings panel
    //			gsnSettingsWindow = new GSNSettingsPanel(allReqIds);
    //			gsnSettingsWindow.run();
    //			gsnSettingsWindow = null;
    //		} else {
    //			gsnSettingsWindow.bringToFront(gsnSettingsWindow.getShell());
    //		}
    //		return null;
    //	}

    //	/**
    //	 * A function that returns a list of all requirement IDs
    //	 * @param objects
    //	 * @return
    //	 */
    //	public List<String> populateVdmWithOnlyRequirementIds(List<EObject> objects) {
    //		List<String> allReqIds = new ArrayList<>();
    //
    //		List<ComponentType> componentTypes = new ArrayList<>();
    //
    //		for(EObject obj : objects) {
    //			if (obj instanceof SystemType) {
    //				componentTypes.add((SystemType) obj);
    //			} else if (obj instanceof BusType) {
    //				componentTypes.add((BusType)obj);
    //			} else if (obj instanceof SubprogramType) {
    //				componentTypes.add((SubprogramType)obj);
    //			} else if (obj instanceof ThreadType) {
    //				componentTypes.add((ThreadType)obj);
    //			} else if (obj instanceof MemoryType) {
    //				componentTypes.add((MemoryType)obj);
    //			} else if (obj instanceof DeviceType) {
    //				componentTypes.add((DeviceType)obj);
    //			} else if (obj instanceof AbstractType) {
    //				componentTypes.add((AbstractType)obj);
    //			} else if (obj instanceof ProcessType) {
    //				componentTypes.add((ProcessType)obj);
    //			} else if (obj instanceof ThreadGroupType) {
    //				componentTypes.add((ThreadGroupType)obj);
    //			} else if (obj instanceof VirtualProcessorType) {
    //				componentTypes.add((VirtualProcessorType)obj);
    //			} else if (obj instanceof ProcessorType) {
    //				componentTypes.add((ProcessorType)obj);
    //			}
    //		}
    //
    //		for(ComponentType compType : componentTypes) {
    //			List<CyberMission> missionReqs = new ArrayList<>();
    //			List<CyberReq> cyberReqs = new ArrayList<>();
    //			List<SafetyReq> safetyReqs = new ArrayList<>();
    //
    //			for(AnnexSubclause annex : compType.getOwnedAnnexSubclauses()) {
    //				if(annex.getName().equalsIgnoreCase("verdict")) {
    //					Verdict verdictAnnex = VerdictUtil.getVerdict(annex);
    //
    //					for (Statement statement : verdictAnnex.getElements()) {
    //						if(statement instanceof CyberMission) {
    //							missionReqs.add((CyberMission)statement);
    //						} else if(statement instanceof CyberReq) {
    //							cyberReqs.add((CyberReq)statement);
    //						} else if(statement instanceof SafetyReq) {
    //							safetyReqs.add((SafetyReq)statement);
    //						}
    //					}
    //				}
    //			}
    //
    //			if(!missionReqs.isEmpty()) {
    //				for(CyberMission aMission : missionReqs) {
    //					allReqIds.add(aMission.getId());
    //				}
    //
    //			}
    //			if(!cyberReqs.isEmpty()) {
    //				for(CyberReq aCyberReq : cyberReqs) {
    //					allReqIds.add(aCyberReq.getId());
    //				}
    //
    //			}
    //			if(!missionReqs.isEmpty()) {
    //				for(CyberMission aMission : missionReqs) {
    //					allReqIds.add(aMission.getId());
    //				}
    //
    //			}
    //			if(!safetyReqs.isEmpty()) {
    //				for(SafetyReq aSafetyReq : safetyReqs) {
    //					allReqIds.add(aSafetyReq.getId());
    //				}
    //
    //			}
    //		}
    //
    //		// Removing duplicates
    //        List<String> duplicateFree = new ArrayList<>(new HashSet<>(allReqIds));
    //
    //        return duplicateFree;
    //	}

}
