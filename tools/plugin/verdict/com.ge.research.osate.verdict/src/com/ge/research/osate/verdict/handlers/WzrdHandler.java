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

import com.ge.research.osate.verdict.gui.StatementEditor;
import com.ge.research.osate.verdict.gui.WzrdDashboard;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.xtext.resource.EObjectAtOffsetHelper;
import org.eclipse.xtext.ui.editor.XtextEditor;
import org.eclipse.xtext.ui.editor.outline.IOutlineNode;
import org.eclipse.xtext.ui.editor.utils.EditorUtils;
import org.osate.aadl2.impl.SystemTypeImpl;

/**
 * @author Paul Meng, Soumya Talukder Date: Jun 25, 2019
 */
public class WzrdHandler extends AbstractHandler {

    public IFile fileModel = null;
    private static boolean isRunningNow = false;

    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {

        IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindowChecked(event);

        if (isRunningNow) {
            MessageDialog.openError(
                    window.getShell(),
                    "VERDICT Wizard Launcher",
                    "Cannot launch multiple sessions of Wizard simultaneously. Aborting..");
            return null;
        } else {
            isRunningNow = true;
        }

        try {
            // set auto-refresh of eclipse editor "ON"
            IEclipsePreferences prefs =
                    InstanceScope.INSTANCE.getNode("org.eclipse.core.resources");
            prefs.putBoolean(ResourcesPlugin.PREF_AUTO_REFRESH, true);
            try {
                prefs.flush();
            } catch (Exception e) {
                System.out.println("Error in setting auto-refresh");
                System.out.println(e.getStackTrace());
            }

            Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();

            // save the invoking .aadl editor if it has unsaved content
            IWorkbenchPage page =
                    PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
            IEditorPart openEditor = page.getActiveEditor();

            if (openEditor != null) {
                boolean response = page.saveEditor(openEditor, true);
                if (!response) {
                    isRunningNow = false;
                    return null;
                } else if (openEditor.isDirty()) {
                    MessageDialog.openError(
                            window.getShell(),
                            "VERDICT Wizard Launcher",
                            "Cannot launch Wizard with unsaved content on the editor. Aborting..");
                    isRunningNow = false;
                    return null;
                }
            }

            // Skip the dashboard when Wizard is invoked from a valid text selection
            if (HandlerUtil.getCurrentSelection(event) instanceof TextSelection) {
                XtextEditor xtextEditor = EditorUtils.getActiveXtextEditor();
                TextSelection ts =
                        (TextSelection) xtextEditor.getSelectionProvider().getSelection();
                xtextEditor
                        .getDocument()
                        .readOnly(
                                resource -> {
                                    EObject e =
                                            new EObjectAtOffsetHelper()
                                                    .resolveContainedElementAt(
                                                            resource, ts.getOffset());
                                    if (e instanceof SystemTypeImpl) {
                                        SystemTypeImpl selectedSys = (SystemTypeImpl) e;
                                        setModelPath(e);
                                        StatementEditor editor =
                                                new StatementEditor(
                                                        selectedSys,
                                                        fileModel.getFullPath(),
                                                        shell,
                                                        window.getShell().getBounds(),
                                                        "osate");
                                        if (editor.isValid()) {
                                            editor.run();
                                        }
                                    } else {
                                        MessageDialog.openError(
                                                window.getShell(),
                                                "VERDICT Wizard Launcher",
                                                "Selected object must be a SystemTypeImpl to launch cyber-property editor Wizard.");
                                    }
                                    return EcoreUtil.getURI(e);
                                });
                isRunningNow = false;
                return null;
            }

            IStructuredSelection selection =
                    (IStructuredSelection) HandlerUtil.getCurrentSelection(event);
            // Skip the dashboard when Wizard is invoked from a valid Outline Node
            // Launch dashboard when invoked from a valid .aadl file
            if (selection.getFirstElement() instanceof IOutlineNode) {
                IOutlineNode node = (IOutlineNode) selection.getFirstElement();

                node.readOnly(
                        state -> {
                            EObject selectedObject = state;
                            setModelPath(selectedObject);
                            if (selectedObject instanceof SystemTypeImpl) {
                                SystemTypeImpl selectedSys = (SystemTypeImpl) selectedObject;
                                setModelPath(selectedObject);
                                StatementEditor editor =
                                        new StatementEditor(
                                                selectedSys,
                                                fileModel.getFullPath(),
                                                shell,
                                                window.getShell().getBounds(),
                                                "osate");
                                if (editor.isValid()) {
                                    editor.run();
                                }
                            } else {
                                MessageDialog.openError(
                                        window.getShell(),
                                        "VERDICT Wizard Launcher",
                                        "Selected object must be a SystemTypeImpl to launch Cyber Requirement Wizard. The currently selected element is:"
                                                + selectedObject.getClass().toString());
                            }
                            isRunningNow = false;
                            return null;
                        });
            } else if (selection.getFirstElement() instanceof IFile) {
                fileModel = (IFile) selection.getFirstElement();
                if (!fileModel.getFileExtension().equals("aadl")) {
                    MessageDialog.openError(
                            window.getShell(),
                            "VERDICT Wizard Launcher",
                            "Wizard can be launched from files only with .aadl extension.");
                    return null;
                }

                IFile file = (IFile) selection.getFirstElement();
                URI uri =
                        URI.createPlatformResourceURI(file.getFullPath().toPortableString(), true);
                ResourceSet rs = new ResourceSetImpl();
                Resource resource = rs.getResource(uri, true);
                try {
                    resource.load(null);
                } catch (Exception e) {
                    e.printStackTrace();
                }

                // the following code loads all the cross-referred .aadl resources in the
                // project
                //				IFile fileRoot = WorkspaceSynchronizer.getFile(resource);
                //				IResource parent = fileRoot.getParent();
                //				IResource[] children = parent.getProject().members();
                //
                //				for (int i = 0; i < children.length; i++) {
                //					if (children[i].getFileExtension().equals("aadl") && children[i] != file) {
                //						URI uriXRefered =
                // URI.createPlatformResourceURI(children[i].getFullPath().toPortableString(),
                //								true);
                //						Resource resourceXRefered = rs.getResource(uriXRefered, true);
                //						System.out.println(
                //								resourceXRefered.toString() + "----loading status: " +
                // resourceXRefered.isLoaded());
                //					}
                //				}

                WzrdDashboard dashboard =
                        new WzrdDashboard(resource, shell, fileModel.getFullPath());
                if (dashboard.isValid()) {
                    dashboard.run();
                }
            }
            isRunningNow = false;
        } catch (Exception e) {
            System.out.println("Error in Wizard!!");
            e.printStackTrace();
        }
        return null;
    }

    // sets the invoking .aadl model file path to IPath variable
    private void setModelPath(EObject root) {
        Resource res = root.eResource();
        URI uri = res.getURI();
        fileModel =
                ResourcesPlugin.getWorkspace()
                        .getRoot()
                        .getFile(new Path(uri.toPlatformString(true)));
    }
}
