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

import com.ge.oyster.proof_repair_assistant.PRAResultsInstance;
import com.rockwellcollins.atc.agree.agree.Contract;
import com.rockwellcollins.atc.agree.agree.SpecStatement;
import com.rockwellcollins.atc.agree.agree.impl.AgreeContractImpl;
import com.rockwellcollins.atc.agree.agree.impl.AgreeContractSubclauseImpl;
import com.rockwellcollins.atc.agree.agree.impl.GuaranteeStatementImpl;
import java.io.File;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.eclipse.core.resources.IProject;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.osate.aadl2.AnnexSubclause;
import org.osate.aadl2.Property;
import org.osate.aadl2.impl.DefaultAnnexSubclauseImpl;

public class PRAAadlWriter {

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
                        "OYSTER PRA",
                        "Please save unsaved content in the file before proceeding.");
                return false;
            }
        }
        return true;
    }

    public static void perform(IProject project, File projectDir, PRAResultsInstance results) {
        if (!saveEditor()) return;
        Map<String, Property> props = new LinkedHashMap<>();

        {
            List<EObject> objs = VerdictHandlersUtils.preprocessAadlFiles(projectDir);
            for (EObject obj : objs) {
                if (obj instanceof Property) {
                    Property prop = (Property) obj;
                    System.out.println(prop.getFullName());
                    props.put(prop.getFullName(), prop);
                }
            }
        }

        // Currently, the only thing that is supported is adding and removing guarantee
        // properties
        Map<String, List<PRAResultsInstance.RemoveItem>> removeElemChanges = new LinkedHashMap<>();

        Map<String, List<PRAResultsInstance.AddItem>> addElemChanges = new LinkedHashMap<>();

        for (PRAResultsInstance.RemoveItem item : results.removes) {
            if (!removeElemChanges.containsKey(item.component)) {
                removeElemChanges.put(item.component, new ArrayList<>());
            }
            removeElemChanges.get(item.component).add(item);
        }

        for (PRAResultsInstance.AddItem item : results.adds) {
            if (!addElemChanges.containsKey(item.component)) {
                addElemChanges.put(item.component, new ArrayList<>());
            }
            addElemChanges.get(item.component).add(item);
        }

        VerdictHandlersUtils.modifyAgreeDocuments(
                project,
                (file, resource) -> {
                    if (resource != null) {

                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {

                                            // This locates a guarantee statement, however at this
                                            // time we are unsure of how
                                            // to change the statement
                                            if (obj instanceof org.osate.aadl2.System) {
                                                org.osate.aadl2.System sc =
                                                        (org.osate.aadl2.System) obj;
                                                for (org.osate.aadl2.Element e :
                                                        sc.getOwnedElements()) {

                                                    if (e instanceof DefaultAnnexSubclauseImpl) {
                                                        DefaultAnnexSubclauseImpl as =
                                                                (DefaultAnnexSubclauseImpl) e;

                                                        if (as.getName().equals("agree")) {
                                                            AnnexSubclause asc =
                                                                    as.getParsedAnnexSubclause();
                                                            if (asc
                                                                    instanceof
                                                                    AgreeContractSubclauseImpl) {
                                                                AgreeContractSubclauseImpl acsi =
                                                                        (AgreeContractSubclauseImpl)
                                                                                asc;
                                                                Contract cacsi = acsi.getContract();

                                                                if (cacsi
                                                                        instanceof
                                                                        AgreeContractImpl) {
                                                                    AgreeContractImpl aci =
                                                                            (AgreeContractImpl)
                                                                                    cacsi;

                                                                    for (SpecStatement ss :
                                                                            aci.getSpecs()) {

                                                                        if (ss
                                                                                instanceof
                                                                                GuaranteeStatementImpl) {
                                                                            GuaranteeStatementImpl
                                                                                    gss =
                                                                                            (GuaranteeStatementImpl)
                                                                                                    ss;
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        });
                    } else {
                        System.err.println("Error: resource is null for file: " + file);
                    }
                });
    }
}
