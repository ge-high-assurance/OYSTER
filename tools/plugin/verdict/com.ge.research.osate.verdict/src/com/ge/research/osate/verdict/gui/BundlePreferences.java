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
package com.ge.research.osate.verdict.gui;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

public class BundlePreferences extends FieldEditorPreferencePage
        implements IWorkbenchPreferencePage {
    // preference keys
    private static final String STEM_DIR = "STEM";
    private static final String DOCKER_IMAGE = "verdict_bundle_image";
    // private static final int FIRST_NON_DOCKER_INDEX = 3; // index of first non-Docker field
    // editor (including separator)
    private static final String BUNDLE_JAR = "verdict_bundle_jar";
    private static final String KIND2_BIN = "kind2_bin";
    private static final String SOTERIA_PP_BIN = "soteria_pp_bin";
    private static final String GRAPH_VIZ_PATH = "graph_viz_path";
    private static final String JKIND_BIN = "jkind_bin";
    private static final String CERTIFICATE_PATH = "certificate_path";
    private static final String PRA_BIN = "proof_repair_assistant_bin";
    private static final String PRA_OUTPUT = "proof_repair_assistant_output";
    private static final String PROOF_VALIDATION_IMAGE = "proof_validation_image";
    private static final String CVC5_PATH = "cvc5_path";
    private static final String LFSC_CHECKER_PATH = "lfsc_checker";
    private static final String VERIT_PATH = "verit_path";
    private static final String ALETHE_CHECKER_PATH = "alethe_checker";

    private static final ArrayList<String> NECESSARY_WITH_DOCKER =
            new ArrayList<>(
                    Arrays.asList(DOCKER_IMAGE, PRA_BIN, PRA_OUTPUT, PROOF_VALIDATION_IMAGE));
    // singleton preference store
    private static ScopedPreferenceStore preferenceStore =
            new ScopedPreferenceStore(InstanceScope.INSTANCE, "com.ge.research.osate.oyster");
    // child field editors
    private List<FieldEditor> fields = new ArrayList<>();

    public BundlePreferences() {
        super(GRID);
    }

    @Override
    public void init(IWorkbench workbench) {
        setPreferenceStore(preferenceStore);
        setDescription("Preferences for OYSTER");
    }

    public static String getStemDir() {
        return preferenceStore.getString(STEM_DIR);
    }

    public static String getDockerImage() {
        return preferenceStore.getString(DOCKER_IMAGE);
    }

    public static String getBundleJar() {
        return preferenceStore.getString(BUNDLE_JAR);
    }

    public static String getKind2Bin() {
        return preferenceStore.getString(KIND2_BIN);
    }

    public static String getSoteriaPpBin() {
        return preferenceStore.getString(SOTERIA_PP_BIN);
    }

    public static String getGraphVizPath() {
        return preferenceStore.getString(GRAPH_VIZ_PATH);
    }

    public static String getJKindBin() {
        return preferenceStore.getString(JKIND_BIN);
    }

    public static String getCertificatePath() {
        return preferenceStore.getString(CERTIFICATE_PATH);
    }

    public static String getPraBin() {
        return preferenceStore.getString(PRA_BIN);
    }

    public static String getPraOutput() {
        return preferenceStore.getString(PRA_OUTPUT);
    }

    public static String getProofValidationImage() {
        return preferenceStore.getString(PROOF_VALIDATION_IMAGE);
    }

    public static String getCVC5Path() {
        return preferenceStore.getString(CVC5_PATH);
    }

    public static String getLFSCCheckerPath() {
        return preferenceStore.getString(LFSC_CHECKER_PATH);
    }

    public static String getVeritPath() {
        return preferenceStore.getString(VERIT_PATH);
    }

    public static String getAletheCheckerPath() {
        return preferenceStore.getString(ALETHE_CHECKER_PATH);
    }

    @Override
    public void propertyChange(PropertyChangeEvent event) {
        // Disable the non-docker field editors if the user types a docker image name
        String preferenceName = ((FieldEditor) event.getSource()).getPreferenceName();
        if (DOCKER_IMAGE.equals(preferenceName)) {
            String dockerImage = ((StringFieldEditor) event.getSource()).getStringValue();
            boolean isEnabled = dockerImage.isEmpty();

            /*for (int i = FIRST_NON_DOCKER_INDEX; i < fields.size(); i++) {
            	fields.get(i).setEnabled(isEnabled, getFieldEditorParent());
            }*/

            Iterator<FieldEditor> fieldsIterator = fields.iterator();
            while (fieldsIterator.hasNext()) {
                FieldEditor field = fieldsIterator.next();
                String fieldPreferenceName = field.getPreferenceName();
                if (!NECESSARY_WITH_DOCKER.contains(fieldPreferenceName)) {
                    field.setEnabled(isEnabled, getFieldEditorParent());
                }
            }
        }
        super.propertyChange(event);
    }

    @Override
    protected void createFieldEditors() {
        //        DirectoryFieldEditor stemDir =
        //                new DirectoryFieldEditor(STEM_DIR, "STEM Project Path:",
        // getFieldEditorParent());
        //        addField(stemDir);

        StringFieldEditor dockerImage =
                new StringFieldEditor(DOCKER_IMAGE, "Bundle Docker Image:", getFieldEditorParent());
        addField(dockerImage);

        LabelFieldEditor separator =
                new LabelFieldEditor(
                        "   --- Remaining fields not needed if Docker is used ---   ",
                        getFieldEditorParent());
        addField(separator);

        FileFieldEditor bundleJar =
                new FileFieldEditor(BUNDLE_JAR, "Bundle Jar:", true, getFieldEditorParent());
        bundleJar.setFileExtensions(new String[] {"*.jar"});
        addField(bundleJar);

        FileFieldEditor kind2Bin =
                new FileFieldEditor(KIND2_BIN, "Kind2 Binary:", true, getFieldEditorParent());
        addField(kind2Bin);

        //        FileFieldEditor soteriaPpBin =
        //                new FileFieldEditor(
        //                        SOTERIA_PP_BIN, "Soteria++ Binary:", true,
        // getFieldEditorParent());
        //        addField(soteriaPpBin);

        //        DirectoryFieldEditor graphVizPath =
        //                new DirectoryFieldEditor(GRAPH_VIZ_PATH, "GraphViz Path:",
        // getFieldEditorParent());
        //        addField(graphVizPath);

        LabelFieldEditor kindSeparator =
                new LabelFieldEditor(
                        "   --- Remaining fields only needed if proof certificate generation desired ---   ",
                        getFieldEditorParent());
        addField(kindSeparator);

        FileFieldEditor jkindBin =
                new FileFieldEditor(JKIND_BIN, "JKind Binary:", true, getFieldEditorParent());
        addField(jkindBin);

        DirectoryFieldEditor certificatePath =
                new DirectoryFieldEditor(CERTIFICATE_PATH, "Proof Output:", getFieldEditorParent());
        addField(certificatePath);

        LabelFieldEditor PRAseparator =
                new LabelFieldEditor(
                        "   --- Remaining fields only needed if proof repair assistant desired ---   ",
                        getFieldEditorParent());
        addField(PRAseparator);

        StringFieldEditor praBin =
                new StringFieldEditor(
                        PRA_BIN, "Proof Repair Assistant Docker:", getFieldEditorParent());
        addField(praBin);

        DirectoryFieldEditor praOutput =
                new DirectoryFieldEditor(
                        PRA_OUTPUT, "Proof Repair Assistant Output:", getFieldEditorParent());
        addField(praOutput);

        final LabelFieldEditor ProofSeparator =
                new LabelFieldEditor(
                        "   --- Remaining fields only needed if proof validation desired ---   ",
                        getFieldEditorParent());

        addField(ProofSeparator);

        final StringFieldEditor proofValidatorDocker =
                new StringFieldEditor(
                        PROOF_VALIDATION_IMAGE, "Proof Validation Docker:", getFieldEditorParent());

        addField(proofValidatorDocker);

        final LabelFieldEditor TSNProofSeparator =
                new LabelFieldEditor(
                        "   --- Remaining fields only needed if TSN schedule proof validation desired ---   ",
                        getFieldEditorParent());

        addField(TSNProofSeparator);

        final FileFieldEditor cvc5 =
                new FileFieldEditor(CVC5_PATH, "CVC5 Path:", getFieldEditorParent());

        addField(cvc5);

        final FileFieldEditor LFSCChecker =
                new FileFieldEditor(
                        LFSC_CHECKER_PATH, "LFSC Checker Path:", getFieldEditorParent());

        addField(LFSCChecker);

        //        final FileFieldEditor verit =
        //                new FileFieldEditor(VERIT_PATH, "veriT Path:", getFieldEditorParent());
        //
        //        addField(verit);
        //
        //        final FileFieldEditor AletheChecker =
        //                new FileFieldEditor(
        //                        ALETHE_CHECKER_PATH, "Alethe Checker Path:",
        // getFieldEditorParent());
        //
        //        addField(AletheChecker);
    }

    @Override
    protected void addField(FieldEditor editor) {
        fields.add(editor);
        super.addField(editor);
    }
}
