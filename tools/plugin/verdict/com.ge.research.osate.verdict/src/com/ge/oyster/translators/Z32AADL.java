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
package com.ge.oyster.translators;

import com.ge.research.osate.verdict.gui.IMASynthesisSettingsPanel;
import com.ge.research.osate.verdict.handlers.VerdictHandlersUtils;
import com.google.inject.Injector;
import com.microsoft.z3.FuncDecl;

import org.apache.commons.math3.util.Pair;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;
import org.eclipse.xtext.ui.editor.model.XtextDocument;
import org.eclipse.xtext.ui.editor.model.XtextDocumentProvider;
import org.osate.aadl2.Aadl2Package;
import org.osate.aadl2.AbstractNamedValue;
import org.osate.aadl2.Connection;
import org.osate.aadl2.DataPort;
import org.osate.aadl2.DirectionType;
import org.osate.aadl2.EndToEndFlow;
import org.osate.aadl2.EndToEndFlowSegment;
import org.osate.aadl2.Feature;
import org.osate.aadl2.FlowEnd;
import org.osate.aadl2.FlowImplementation;
import org.osate.aadl2.FlowKind;
import org.osate.aadl2.FlowSegment;
import org.osate.aadl2.FlowSpecification;
import org.osate.aadl2.IntegerLiteral;
import org.osate.aadl2.ModalPropertyValue;
import org.osate.aadl2.Property;
import org.osate.aadl2.PropertyAssociation;
import org.osate.aadl2.PropertyExpression;
import org.osate.aadl2.StringLiteral;
import org.osate.aadl2.Subcomponent;
import org.osate.aadl2.SubcomponentType;
import org.osate.aadl2.SystemSubcomponentType;
import org.osate.aadl2.SystemType;
import org.osate.aadl2.impl.EnumerationLiteralImpl;
import org.osate.aadl2.impl.NamedValueImpl;
import org.osate.aadl2.impl.SubcomponentImpl;
import org.osate.xtext.aadl2.Aadl2StandaloneSetup;
import org.osate.xtext.aadl2.ui.internal.Aadl2Activator;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Scanner;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Z32AADL {
    String topLevelComponentType = null;

    boolean fsbBandwidthYes = IMASynthesisSettingsPanel.fsbBandwidthYes;
    boolean fsbAppScheduleYes = IMASynthesisSettingsPanel.fsbAppScheduleYes;
    static HashMap<String, String> ccrBoundaryPort = new HashMap<>();
    static HashMap<String, String> ccrFlowPathPort = new HashMap<>();
    public static Map<String, List<String>> vlflowconMap = new HashMap<>();
    static Map<String, List<String>> subCompsFromModel = new HashMap<>();
    static HashMap<String, Pair<String, Boolean>> ccrSource = new HashMap<>();
    static HashMap<String, Pair<String, Boolean>> ccrSink = new HashMap<>();
    // app -> AppScheduleInfo
    // processor = null for single core
    Map<String, AppScheduleInfo> app_schedule_infos;
    static Set<Subcomponent> subComps = new HashSet<>();
    static Set<org.osate.aadl2.SystemImplementation> sysImpls = new HashSet<>();
    static Set<org.osate.aadl2.SystemType> sysTypes = new HashSet<>();

    // entry point to the Z3 to AADL translation
    public List<EObject> execute(
            com.microsoft.z3.Model z3Model,
            com.microsoft.z3.Context ctx,
            com.microsoft.z3.Model z3Model2,
            com.microsoft.z3.Context ctx2,
            IProject project,
            Map<String, Pair<String, String>> flowNamesToSrcDestInstance,
            List<String> instanceBoundTohostCompName,
            List<EObject> AADLInputObjects) {

        subComps.clear();
        sysImpls.clear();
        sysTypes.clear();
        subCompsFromModel.clear();
        ccrBoundaryPort.clear();
        ccrFlowPathPort.clear();
        List<File> dirs = VerdictHandlersUtils.collectAllDirs(project.getLocation().toFile());
        List<String> aadlFileNames = new ArrayList<>();
        String odmFileName = "";

        // read all OYSTER properties to a map
        Map<String, Property> props = new LinkedHashMap<>();
        for (EObject obj : AADLInputObjects) {
            if (obj instanceof Property) {
                Property prop = (Property) obj;
                props.put(prop.getFullName(), prop);
            }
        }

        // Obtain all AADL files contents in the project
        String projectPath = project.getLocation().toFile().getAbsolutePath();

        for (File subdir : dirs) {
            for (File file : subdir.listFiles()) {
                if (file.getAbsolutePath().endsWith(".aadl")) {
                    String absPath = file.getAbsolutePath();
                    String relPath = absPath.substring(projectPath.length() + 1);
                    aadlFileNames.add(relPath);
                } else if (file.getAbsolutePath().endsWith("\\odm.xml")
                        || file.getAbsolutePath().endsWith("/odm.xml")) {
                    odmFileName = file.getAbsolutePath();
                }
            }
        }

        // currently, we read the correct AADL file name from the package name written
        // in the ODM file
        String packageName = getCorretAadlFileNameFromODM(odmFileName);
        List<Resource> resources = VerdictHandlersUtils.loadAadlFiles(dirs.get(0));
        int resIndex = getIndexOfLookupElement(packageName, resources);
        Resource updateFile = resources.get(resIndex);

        // copy original input aadl file and create a new synthesized aadl file
        File orig = new File(updateFile.getURI().toFileString());
        File copOfOrig =
                new File(updateFile.getURI().toFileString().replace(".aadl", "_synthesized.aadl"));

        try {
            com.google.common.io.Files.copy(orig, copOfOrig);
        } catch (Exception e) {
            System.err.println("Error: failed to process correct aadl file");
            e.printStackTrace();
        }

        List<String> firstNameList = new ArrayList<String>();
        BiConsumer<String, XtextResource> findFirst =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        List<EObject> res = new ArrayList<EObject>();
                        TreeIterator<EObject> iterator = resource.getAllContents();
                        while (iterator.hasNext()) {
                            EObject cur = iterator.next();
                            if (cur instanceof org.osate.aadl2.SystemType) {
                                org.osate.aadl2.SystemType s = (org.osate.aadl2.SystemType) cur;
                                res.add(s);
                                firstNameList.add(s.getName());
                                break;
                            }
                        }
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), findFirst);

        String firstName = firstNameList.get(0);
        List<String> names = new ArrayList<String>();
        HashMap<String, String> name2FullName = new HashMap<String, String>();
        HashMap<String, Subcomponent> fullName2SubComponent = new HashMap<String, Subcomponent>();
        List<SubcomponentType> subcomponentTypes = new ArrayList<SubcomponentType>();
        List<String> implNames = new ArrayList<String>();
        List<Subcomponent> subs = new ArrayList<Subcomponent>();

        // add new implementations based on the subcomponents
        subCompsFromModel = readFLCmapping(z3Model);

        BiConsumer<String, XtextResource> addedNames =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {
                                                org.osate.aadl2.SystemImplementation s =
                                                        (org.osate.aadl2.SystemImplementation) obj;
                                                implNames.add(s.getFullName());
                                                List<Subcomponent> comps =
                                                        s.getOwnedSubcomponents();
                                                for (Subcomponent comp : comps) {
                                                    subComps.add(comp);
                                                    boolean isChild = false;

                                                    for (String entry :
                                                            subCompsFromModel.keySet()) {
                                                        List<String> list =
                                                                subCompsFromModel.get(entry);
                                                        for (String element : list) {
                                                            if (element.split("\\.")[1].equals(
                                                                    comp.getName())) {
                                                                isChild = true;
                                                                break;
                                                            }
                                                        }
                                                    }
                                                    if (isChild == false && !subs.contains(comp)) {
                                                        subs.add(comp);
                                                    }
                                                }

                                                // subs.addAll(s.getOwnedSubcomponents());
                                                for (Subcomponent sb : s.getOwnedSubcomponents()) {
                                                    String fullName =
                                                            sb.getComponentType().getName()
                                                                    + "."
                                                                    + sb.getName();
                                                    subcomponentTypes.add(sb.getSubcomponentType());
                                                    names.add(fullName);
                                                    name2FullName.put(sb.getName(), fullName);
                                                    fullName2SubComponent.put(fullName, sb);
                                                }
                                            }
                                        });
                    } else {
                        System.err.println("Error: resource is null for file: " + file);
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), addedNames);

        String synthName = implNames.get(0).split("\\.")[0] + ".Synthesis";
        topLevelComponentType = implNames.get(0).split("\\.")[0];
        names.add(synthName);

        try {
            BufferedReader file = new BufferedReader(new FileReader(copOfOrig.getAbsolutePath()));
            StringBuffer buffer = new StringBuffer();
            String line;

            Boolean foundAddPoint = false;
            Boolean beenTrue = false;
            while ((line = file.readLine()) != null) {
                if (line.contains(firstName)) {
                    foundAddPoint = true;
                    if (foundAddPoint && !beenTrue) {
                        for (String name : names) {
                            List<String> txt = addBaseSystemImpl(name);
                            for (String t : txt) {
                                buffer.append(t);
                                buffer.append('\n');
                            }

                            buffer.append('\n');
                        }

                        beenTrue = true;
                    }
                }

                buffer.append(line);
                buffer.append('\n');
            }

            file.close();
            String inputStr = buffer.toString();

            FileOutputStream fileOut = new FileOutputStream(copOfOrig.getAbsolutePath());
            fileOut.write(inputStr.getBytes());
            fileOut.close();
        } catch (Exception e) {
            System.err.println("Problem reading file.");
        }

        subComps.clear();
        subCompsFromModel.clear();
        subCompsFromModel = readFLCmapping(z3Model);

        // add all subcomponents under a component implementation
        BiConsumer<String, XtextResource> addSubcomponents =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {
                                                org.osate.aadl2.SystemImplementation s =
                                                        (org.osate.aadl2.SystemImplementation) obj;
                                                List<String> subcomponents =
                                                        subCompsFromModel.get(s.getName());

                                                if (!Objects.isNull(subcomponents)
                                                        && subcomponents.size() > 0) {
                                                    for (String sub : subcomponents) {
                                                        SystemSubcomponentTypeDuplicator ssd =
                                                                new SystemSubcomponentTypeDuplicator();
                                                        s.createOwnedSystemSubcomponent()
                                                                .setSystemSubcomponentType(
                                                                        (SystemSubcomponentType)
                                                                                ssd);
                                                    }

                                                    for (int i = 0; i < subcomponents.size(); i++) {
                                                        SubcomponentImpl sub =
                                                                (SubcomponentImpl)
                                                                        s.getAllSubcomponents()
                                                                                .get(i);
                                                        sub.getSubcomponentType()
                                                                .setName(subcomponents.get(i));
                                                        String newName =
                                                                subcomponents.get(i)
                                                                        .split("\\.")[1];
                                                        sub.setName(newName);
                                                    }
                                                }
                                            }
                                        });
                    } else {
                        System.err.println("Error: resource is null for file: " + file);
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), addSubcomponents);

        // add all ports under a component type
        BiConsumer<String, XtextResource> addPorts =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj instanceof org.osate.aadl2.SystemType) {
                                                org.osate.aadl2.SystemType s =
                                                        (org.osate.aadl2.SystemType) obj;
                                                for (String key :
                                                        Odm2Z3.PortConnectionMap.keySet()) {
                                                    // handle ports in system types
                                                    String sourceInfo =
                                                            Odm2Z3.PortConnectionMap.get(key)
                                                                    .generateSourceInfo();
                                                    String insName = sourceInfo.split("\\.")[0];
                                                    String portName = sourceInfo.split("\\.")[1];
                                                    String typeName = null;

                                                    for (FuncDecl<?> func1 :
                                                            z3Model.getConstDecls()) {
                                                        if (func1.getName()
                                                                .toString()
                                                                .equals(insName)) {
                                                            typeName = func1.getRange().toString();
                                                            break;
                                                        }
                                                    }

                                                    if ((typeName != null)
                                                            && typeName.equals(s.getName())) {
                                                        boolean found = false;
                                                        for (DataPort dp : s.getOwnedDataPorts()) {
                                                            if (dp.getName().equals(portName)) {
                                                                found = true;
                                                                break;
                                                            }
                                                        }

                                                        if (found == false) {
                                                            DataPort dataPort =
                                                                    s.createOwnedDataPort();
                                                            dataPort.setName(portName);
                                                            dataPort.setDirection(
                                                                    DirectionType.IN_OUT);
                                                        }
                                                    }
                                                }

                                                for (String key :
                                                        Odm2Z3.PortConnectionMap.keySet()) {
                                                    // handle ports in system types
                                                    String destInfo =
                                                            Odm2Z3.PortConnectionMap.get(key)
                                                                    .generateDestInfo();
                                                    String insName = destInfo.split("\\.")[0];
                                                    String portName = destInfo.split("\\.")[1];
                                                    String typeName = null;

                                                    for (FuncDecl<?> func1 :
                                                            z3Model.getConstDecls()) {
                                                        if (func1.getName()
                                                                .toString()
                                                                .equals(insName)) {
                                                            typeName = func1.getRange().toString();
                                                            break;
                                                        }
                                                    }

                                                    if ((typeName != null)
                                                            && typeName.equals(s.getName())) {
                                                        boolean found = false;
                                                        for (DataPort dp : s.getOwnedDataPorts()) {
                                                            if (dp.getName().equals(portName)) {
                                                                found = true;
                                                                break;
                                                            }
                                                        }

                                                        if (found == false) {
                                                            DataPort dataPort =
                                                                    s.createOwnedDataPort();
                                                            dataPort.setName(portName);
                                                            dataPort.setDirection(
                                                                    DirectionType.IN_OUT);
                                                        }
                                                    }
                                                }
                                            }
                                        });
                    } else {
                        System.err.println("Error: resource is null for file: " + file);
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), addPorts);

        // attempts to create and print the app schedule
        // string if present in the model
        // and the option is selected by the user
        if (fsbAppScheduleYes) {
            app_schedule_infos =
                    Z3ModelReader.func_get_app_start_times(
                            z3Model2, ctx2, instanceBoundTohostCompName);
            if (app_schedule_infos.keySet().size() > 0) {
                List<String> app_sched_strings =
                        Z3ModelReader.func_generate_schedule_strings(z3Model2, app_schedule_infos);
                for (String app_sched_string : app_sched_strings) {
                    if (!(app_sched_string.equals(""))) {
                        System.out.println(
                                "Info: A schedule string for processor " + app_sched_string);
                    }
                }
            }
        }
        // create new synthesized implementation for the top-level implementations
        // add subcomponents and their properties
        BiConsumer<String, XtextResource> createNewImpl =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {
                                                org.osate.aadl2.SystemImplementation s =
                                                        (org.osate.aadl2.SystemImplementation) obj;
                                                if (s.getName().contains(synthName)) {

                                                    for (Subcomponent sub : subs) {
                                                        SystemSubcomponentTypeDuplicator ssd =
                                                                new SystemSubcomponentTypeDuplicator();
                                                        ssd.setName(
                                                                sub.getSubcomponentType().getName()
                                                                        + "."
                                                                        + sub.getName());
                                                        s.createOwnedSystemSubcomponent()
                                                                .setSystemSubcomponentType(
                                                                        (SystemSubcomponentType)
                                                                                ssd);
                                                    }

                                                    for (int i = 0; i < subs.size(); i++) {
                                                        Subcomponent sub =
                                                                s.getOwnedSubcomponents().get(i);
                                                        String name =
                                                                sub.getSubcomponentType()
                                                                        .getName()
                                                                        .split("\\.")[1];
                                                        sub.setName(name);
                                                        for (PropertyAssociation pa :
                                                                subs.get(i)
                                                                        .getOwnedPropertyAssociations()) {
                                                            PropertyAssociation npa =
                                                                    sub
                                                                            .createOwnedPropertyAssociation();
                                                            npa.setProperty(pa.getProperty());
                                                            npa.createOwnedValue()
                                                                    .setOwnedValue(
                                                                            pa.getOwnedValues()
                                                                                    .get(0)
                                                                                    .getOwnedValue());
                                                        }
                                                    }
                                                } else {
                                                    for (Subcomponent sub :
                                                            s.getAllSubcomponents()) {
                                                        if (fsbAppScheduleYes) {
                                                            if (app_schedule_infos.get(
                                                                            sub.getName())
                                                                    != null) {

                                                                // add app start time as OYSTER
                                                                // property if applicable
                                                                PropertyAssociation pa =
                                                                        sub
                                                                                .createOwnedPropertyAssociation();
                                                                Property property =
                                                                        props.get("start_time");
                                                                pa.setProperty(property);
                                                                ModalPropertyValue propVal =
                                                                        pa.createOwnedValue();
                                                                IntegerLiteral val =
                                                                        (IntegerLiteral)
                                                                                propVal
                                                                                        .createOwnedValue(
                                                                                                Aadl2Package
                                                                                                        .eINSTANCE
                                                                                                        .getIntegerLiteral());
                                                                val.setValue(
                                                                        app_schedule_infos.get(
                                                                                        sub
                                                                                                .getName())
                                                                                .start_initial);

                                                                // add prcessor name and period for
                                                                // multi-core scheduling
                                                                if (app_schedule_infos.get(
                                                                                        sub
                                                                                                .getName())
                                                                                .procName
                                                                        != null) {
                                                                    PropertyAssociation pa2 =
                                                                            sub
                                                                                    .createOwnedPropertyAssociation();
                                                                    Property property2 =
                                                                            props.get(
                                                                                    "processor_name");
                                                                    pa2.setProperty(property2);
                                                                    ModalPropertyValue propVal2 =
                                                                            pa2.createOwnedValue();
                                                                    StringLiteral val2 =
                                                                            (StringLiteral)
                                                                                    propVal2
                                                                                            .createOwnedValue(
                                                                                                    Aadl2Package
                                                                                                            .eINSTANCE
                                                                                                            .getStringLiteral());
                                                                    val2.setValue(
                                                                            app_schedule_infos.get(
                                                                                            sub
                                                                                                    .getName())
                                                                                    .procName);

                                                                    PropertyAssociation pa3 =
                                                                            sub
                                                                                    .createOwnedPropertyAssociation();
                                                                    Property property3 =
                                                                            props.get("period");
                                                                    pa3.setProperty(property3);
                                                                    ModalPropertyValue propVal3 =
                                                                            pa3.createOwnedValue();
                                                                    IntegerLiteral val3 =
                                                                            (IntegerLiteral)
                                                                                    propVal3
                                                                                            .createOwnedValue(
                                                                                                    Aadl2Package
                                                                                                            .eINSTANCE
                                                                                                            .getIntegerLiteral());
                                                                    val3.setValue(
                                                                            app_schedule_infos.get(
                                                                                            sub
                                                                                                    .getName())
                                                                                    .period);
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }

                                            if (obj instanceof org.osate.aadl2.SystemType) {
                                                sysTypes.add((org.osate.aadl2.SystemType) obj);
                                            }
                                        });
                    } else {
                        System.err.println("Error: resource is null for file: " + file);
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), createNewImpl);

        Map<Pair<String, String>, String> connMap =
                Z3ModelReader.readFunc_Port_Connection_Port(
                        z3Model, ctx, "Port", "Connection", "Port");
        Map<String, Integer> bandwidthMap =
                Z3ModelReader.readFunc_Connection_bandwidth(z3Model, "Connection");

        // add connections and properties (link bandwidth) to the synthesized component
        // implementation
        BiConsumer<String, XtextResource> createNewImplConnection =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {
                                                org.osate.aadl2.SystemImplementation s =
                                                        (org.osate.aadl2.SystemImplementation) obj;

                                                // find internal connections

                                                // find cross component connections
                                                if (!s.getName().equals(synthName)) {

                                                    for (String key :
                                                            Odm2Z3.PortConnectionMap.keySet()) {
                                                        // handle connections in top-level system
                                                        // implementations
                                                        PortConnection pc =
                                                                Odm2Z3.PortConnectionMap.get(key);
                                                        String src =
                                                                pc.generateSourceInfo()
                                                                        .split("\\.")[0];
                                                        String srcPort =
                                                                pc.generateSourceInfo()
                                                                        .split("\\.")[1];
                                                        String dest =
                                                                pc.generateDestInfo()
                                                                        .split("\\.")[0];
                                                        String destPort =
                                                                pc.generateDestInfo()
                                                                        .split("\\.")[1];
                                                        String connName = pc.getConnectionName();

                                                        Feature srcEndPort = null;

                                                        Feature destEndPort = null;
                                                        Subcomponent srcSub = null;
                                                        Subcomponent destSub = null;

                                                        for (Subcomponent sub :
                                                                s.getOwnedSubcomponents()) {
                                                            if (sub.getName().equals(src)) {
                                                                for (Feature f :
                                                                        sub.getAllFeatures()) {
                                                                    if (f
                                                                                    instanceof
                                                                                    org.osate.aadl2
                                                                                            .impl
                                                                                            .DataPortImpl
                                                                            && f.getName()
                                                                                    .equals(
                                                                                            srcPort)) {
                                                                        srcEndPort = f;
                                                                        srcSub = sub;
                                                                    }
                                                                }
                                                            }

                                                            if (sub.getName().equals(dest)) {
                                                                for (Feature f :
                                                                        sub.getAllFeatures()) {
                                                                    if (f
                                                                                    instanceof
                                                                                    org.osate.aadl2
                                                                                            .impl
                                                                                            .DataPortImpl
                                                                            && f.getName()
                                                                                    .equals(
                                                                                            destPort)) {
                                                                        destEndPort = f;
                                                                        destSub = sub;
                                                                    }
                                                                }
                                                            }
                                                        }

                                                        if (srcEndPort != null
                                                                && destEndPort != null) {
                                                            Connection c =
                                                                    s.createOwnedPortConnection();
                                                            c.createSource();
                                                            c.getSource().setContext(srcSub);
                                                            c.getSource()
                                                                    .setConnectionEnd(srcEndPort);
                                                            c.createDestination();
                                                            c.getDestination().setContext(destSub);
                                                            c.getDestination()
                                                                    .setConnectionEnd(destEndPort);
                                                            c.setBidirectional(true);
                                                            c.setName(connName);

                                                            int bandwidth =
                                                                    bandwidthMap.get(connName);
                                                            PropertyAssociation pa =
                                                                    c
                                                                            .createOwnedPropertyAssociation();
                                                            Property property =
                                                                    props.get("bandwidth");
                                                            pa.setProperty(property);
                                                            ModalPropertyValue propVal =
                                                                    pa.createOwnedValue();
                                                            IntegerLiteral val =
                                                                    (IntegerLiteral)
                                                                            propVal
                                                                                    .createOwnedValue(
                                                                                            Aadl2Package
                                                                                                    .eINSTANCE
                                                                                                    .getIntegerLiteral());
                                                            val.setValue(bandwidth);
                                                        }

                                                        if (srcSub != null && destSub == null) {
                                                            if (dest.equals(
                                                                    s.getName()
                                                                            .replace(
                                                                                    s.getType()
                                                                                                    .getName()
                                                                                            + ".",
                                                                                    ""))) {
                                                                Connection c =
                                                                        s
                                                                                .createOwnedPortConnection();
                                                                c.createSource();
                                                                c.getSource().setContext(srcSub);
                                                                c.getSource()
                                                                        .setConnectionEnd(
                                                                                srcEndPort);
                                                                c.createDestination();

                                                                // c.getDestination().setContext((Context) s);

                                                                List<Feature> features =
                                                                        s.getAllFeatures();
                                                                Feature ownDestPort = null;
                                                                for (Feature f : features) {
                                                                    if (f.getFullName()
                                                                            .equals(destPort)) {
                                                                        ownDestPort = f;
                                                                        break;
                                                                    }
                                                                }
                                                                c.getDestination()
                                                                        .setConnectionEnd(
                                                                                ownDestPort);
                                                                c.setBidirectional(true);
                                                                c.setName(connName);

                                                                int bandwidth =
                                                                        bandwidthMap.get(connName);
                                                                PropertyAssociation pa =
                                                                        c
                                                                                .createOwnedPropertyAssociation();
                                                                Property property =
                                                                        props.get("bandwidth");
                                                                pa.setProperty(property);
                                                                ModalPropertyValue propVal =
                                                                        pa.createOwnedValue();
                                                                IntegerLiteral val =
                                                                        (IntegerLiteral)
                                                                                propVal
                                                                                        .createOwnedValue(
                                                                                                Aadl2Package
                                                                                                        .eINSTANCE
                                                                                                        .getIntegerLiteral());
                                                                val.setValue(bandwidth);
                                                            }
                                                        }

                                                        if (srcSub == null && destSub != null) {
                                                            if (src.equals(
                                                                    s.getName()
                                                                            .replace(
                                                                                    s.getType()
                                                                                                    .getName()
                                                                                            + ".",
                                                                                    ""))) {
                                                                Connection c =
                                                                        s
                                                                                .createOwnedPortConnection();
                                                                c.createSource();
                                                                /*
                                                                 * c.getSource().setContext(srcSub); c.getSource() .setConnectionEnd(
                                                                 * srcEndPort);
                                                                 */
                                                                c.createDestination();

                                                                // c.getDestination().setContext((Context) s);

                                                                List<Feature> features =
                                                                        s.getAllFeatures();
                                                                Feature ownSrcPort = null;
                                                                for (Feature f : features) {
                                                                    if (f.getFullName()
                                                                            .equals(srcPort)) {
                                                                        ownSrcPort = f;
                                                                        break;
                                                                    }
                                                                }
                                                                c.getSource()
                                                                        .setConnectionEnd(
                                                                                ownSrcPort);
                                                                c.getDestination()
                                                                        .setContext(destSub);
                                                                c.getDestination()
                                                                        .setConnectionEnd(
                                                                                destEndPort);
                                                                c.setBidirectional(true);
                                                                c.setName(connName);

                                                                int bandwidth =
                                                                        bandwidthMap.get(connName);
                                                                PropertyAssociation pa =
                                                                        c
                                                                                .createOwnedPropertyAssociation();
                                                                Property property =
                                                                        props.get("bandwidth");
                                                                pa.setProperty(property);
                                                                ModalPropertyValue propVal =
                                                                        pa.createOwnedValue();
                                                                IntegerLiteral val =
                                                                        (IntegerLiteral)
                                                                                propVal
                                                                                        .createOwnedValue(
                                                                                                Aadl2Package
                                                                                                        .eINSTANCE
                                                                                                        .getIntegerLiteral());
                                                                val.setValue(bandwidth);
                                                            }
                                                        }
                                                    }
                                                } else {

                                                    for (String key :
                                                            Odm2Z3.PortConnectionMap.keySet()) {
                                                        // handle connections in top-level system
                                                        // implementations
                                                        PortConnection pc =
                                                                Odm2Z3.PortConnectionMap.get(key);
                                                        String src =
                                                                pc.generateSourceInfo()
                                                                        .split("\\.")[0];
                                                        String srcPort =
                                                                pc.generateSourceInfo()
                                                                        .split("\\.")[1];
                                                        String dest =
                                                                pc.generateDestInfo()
                                                                        .split("\\.")[0];
                                                        String destPort =
                                                                pc.generateDestInfo()
                                                                        .split("\\.")[1];
                                                        String connName = pc.getConnectionName();

                                                        Feature srcEndPort = null;
                                                        Feature destEndPort = null;
                                                        Subcomponent srcSub = null;
                                                        Subcomponent destSub = null;

                                                        for (Subcomponent sub :
                                                                s.getOwnedSubcomponents()) {
                                                            if (sub.getName().equals(src)) {
                                                                for (Feature f :
                                                                        sub.getAllFeatures()) {
                                                                    if (f
                                                                                    instanceof
                                                                                    org.osate.aadl2
                                                                                            .impl
                                                                                            .DataPortImpl
                                                                            && f.getName()
                                                                                    .equals(
                                                                                            srcPort)) {
                                                                        srcEndPort = f;
                                                                        srcSub = sub;
                                                                    }
                                                                }
                                                            }

                                                            if (sub.getName().equals(dest)) {
                                                                for (Feature f :
                                                                        sub.getAllFeatures()) {
                                                                    if (f
                                                                                    instanceof
                                                                                    org.osate.aadl2
                                                                                            .impl
                                                                                            .DataPortImpl
                                                                            && f.getName()
                                                                                    .equals(
                                                                                            destPort)) {
                                                                        destEndPort = f;
                                                                        destSub = sub;
                                                                    }
                                                                }
                                                            }
                                                        }

                                                        if (srcEndPort != null
                                                                && destEndPort != null) {
                                                            Connection c =
                                                                    s.createOwnedPortConnection();
                                                            c.createSource();
                                                            c.getSource().setContext(srcSub);
                                                            c.getSource()
                                                                    .setConnectionEnd(srcEndPort);
                                                            c.createDestination();
                                                            c.getDestination().setContext(destSub);
                                                            c.getDestination()
                                                                    .setConnectionEnd(destEndPort);
                                                            c.setBidirectional(true);
                                                            c.setName(connName);

                                                            int bandwidth =
                                                                    bandwidthMap.get(connName);
                                                            PropertyAssociation pa =
                                                                    c
                                                                            .createOwnedPropertyAssociation();
                                                            Property property =
                                                                    props.get("bandwidth");
                                                            pa.setProperty(property);
                                                            ModalPropertyValue propVal =
                                                                    pa.createOwnedValue();
                                                            IntegerLiteral val =
                                                                    (IntegerLiteral)
                                                                            propVal
                                                                                    .createOwnedValue(
                                                                                            Aadl2Package
                                                                                                    .eINSTANCE
                                                                                                    .getIntegerLiteral());
                                                            val.setValue(bandwidth);
                                                        }
                                                    }
                                                }
                                            }
                                        });
                    } else {
                        System.err.println("Error: resource is null for file: " + file);
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), createNewImplConnection);

        // add VL flows to all the system component implementations
        // with bag, mtu properties

        vlflowconMap =
                Z3ModelReader.readFunc_VLFlow_Connection(z3Model, ctx, flowNamesToSrcDestInstance);

        BiConsumer<String, XtextResource> createFlowSpecs =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {
                                                org.osate.aadl2.SystemImplementation s =
                                                        (org.osate.aadl2.SystemImplementation) obj;
                                                if (!s.getName().equals("IMA.Impl")) {
                                                    Map<String, Integer> vlTomtu =
                                                            Z3ModelReader.getMap_VLToMtu(z3Model2);
                                                    Map<String, Integer> vlTobag =
                                                            Z3ModelReader.getMap_VLToBag(z3Model2);

                                                    for (String flow : vlflowconMap.keySet()) {
                                                        String ccrBoundary =
                                                                getCCRBoundary(
                                                                        Odm2Z3.vlStartsFromGPM.get(
                                                                                flow),
                                                                        removeDuplicates(
                                                                                vlflowconMap.get(
                                                                                        flow)));
                                                        ccrBoundaryPort.put(flow, ccrBoundary);
                                                        String ccrFlowPort =
                                                                getCCRFlowPathPort(
                                                                        Odm2Z3.vlStartsFromGPM.get(
                                                                                flow),
                                                                        removeDuplicates(
                                                                                vlflowconMap.get(
                                                                                        flow)));
                                                        ccrFlowPathPort.put(flow, ccrFlowPort);

                                                        List<String> flowSegments =
                                                                removeDuplicates(
                                                                        vlflowconMap.get(flow));
                                                        for (int i = 0;
                                                                i <= flowSegments.size() - 1;
                                                                i++) {
                                                            String elm = flowSegments.get(i);
                                                            String vlElmName =
                                                                    (flow
                                                                                    + "_"
                                                                                    + elm.split(
                                                                                                    "\\.")[
                                                                                            0])
                                                                            .replaceAll("\\.", "_");
                                                            String elmIns = elm.split("\\.")[0];
                                                            // find CCR port boundary

                                                            if (i == 0) {
                                                                for (Subcomponent sub :
                                                                        s.getAllSubcomponents()) {
                                                                    if (sub.getName()
                                                                            .equals(elmIns)) {
                                                                        for (Feature ft :
                                                                                sub
                                                                                        .getAllFeatures()) {
                                                                            if (ft
                                                                                            instanceof
                                                                                            org
                                                                                                    .osate
                                                                                                    .aadl2
                                                                                                    .impl
                                                                                                    .DataPortImpl
                                                                                    && ft.getName()
                                                                                            .equals(
                                                                                                    elm.split(
                                                                                                                    "\\.")[
                                                                                                            1])) {
                                                                                FlowSpecification
                                                                                        f =
                                                                                                sub.getComponentType()
                                                                                                        .createOwnedFlowSpecification();
                                                                                FlowEnd fend =
                                                                                        f
                                                                                                .createOutEnd();
                                                                                fend.setFeature(ft);
                                                                                f.setOutEnd(fend);
                                                                                f.setKind(
                                                                                        FlowKind
                                                                                                .SOURCE);
                                                                                f.setName(
                                                                                        vlElmName);

                                                                                break;
                                                                            }
                                                                        }
                                                                    }
                                                                }

                                                            } else if (i
                                                                    == flowSegments.size() - 1) {
                                                                for (Subcomponent sub :
                                                                        s.getAllSubcomponents()) {
                                                                    if (sub.getName()
                                                                            .equals(elmIns)) {
                                                                        for (Feature ft :
                                                                                sub
                                                                                        .getAllFeatures()) {
                                                                            if (ft
                                                                                            instanceof
                                                                                            org
                                                                                                    .osate
                                                                                                    .aadl2
                                                                                                    .impl
                                                                                                    .DataPortImpl
                                                                                    && ft.getName()
                                                                                            .equals(
                                                                                                    elm.split(
                                                                                                                    "\\.")[
                                                                                                            1])) {
                                                                                FlowSpecification
                                                                                        f =
                                                                                                sub.getComponentType()
                                                                                                        .createOwnedFlowSpecification();
                                                                                FlowEnd fend =
                                                                                        f
                                                                                                .createInEnd();
                                                                                fend.setFeature(ft);
                                                                                f.setInEnd(fend);
                                                                                f.setKind(
                                                                                        FlowKind
                                                                                                .SINK);
                                                                                f.setName(
                                                                                        vlElmName);
                                                                                /*
                                                                                 * EndToEndFlowSegment seg = e2eFlow
                                                                                 * .createOwnedEndToEndFlowSegment(); seg.setFlowElement( f);
                                                                                 * seg.setContext(sub);
                                                                                 */
                                                                                break;
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            } else {

                                                                String elm2 =
                                                                        flowSegments.get(i + 1);
                                                                if (!elm2.contains(".")) {
                                                                    continue;
                                                                }

                                                                String vlElmName2 =
                                                                        (flow
                                                                                        + "_"
                                                                                        + elm2.split(
                                                                                                        "\\.")[
                                                                                                0])
                                                                                .replaceAll(
                                                                                        "\\.", "_");
                                                                String elmIns2 =
                                                                        elm2.split("\\.")[0];

                                                                if (elmIns2.equals(elmIns)) {
                                                                    for (Subcomponent sub :
                                                                            s
                                                                                    .getAllSubcomponents()) {
                                                                        if (sub.getName()
                                                                                .equals(elmIns)) {
                                                                            Feature ft1 = null;
                                                                            Feature ft2 = null;
                                                                            for (Feature ft :
                                                                                    sub
                                                                                            .getAllFeatures()) {
                                                                                if (ft
                                                                                                instanceof
                                                                                                org
                                                                                                        .osate
                                                                                                        .aadl2
                                                                                                        .impl
                                                                                                        .DataPortImpl
                                                                                        && ft.getName()
                                                                                                .equals(
                                                                                                        elm.split(
                                                                                                                        "\\.")[
                                                                                                                1])) {
                                                                                    ft1 = ft;
                                                                                } else if (ft
                                                                                                instanceof
                                                                                                org
                                                                                                        .osate
                                                                                                        .aadl2
                                                                                                        .impl
                                                                                                        .DataPortImpl
                                                                                        && ft.getName()
                                                                                                .equals(
                                                                                                        elm2.split(
                                                                                                                        "\\.")[
                                                                                                                1])) {
                                                                                    ft2 = ft;
                                                                                }
                                                                            }

                                                                            if (ft1 != null
                                                                                    && ft2
                                                                                            != null) {

                                                                                FlowSpecification
                                                                                        f =
                                                                                                sub.getComponentType()
                                                                                                        .createOwnedFlowSpecification();
                                                                                FlowEnd fend1 =
                                                                                        f
                                                                                                .createInEnd();
                                                                                fend1.setFeature(
                                                                                        ft1);
                                                                                FlowEnd fend2 =
                                                                                        f
                                                                                                .createOutEnd();
                                                                                fend2.setFeature(
                                                                                        ft2);
                                                                                f.setInEnd(fend1);
                                                                                f.setOutEnd(fend2);
                                                                                f.setKind(
                                                                                        FlowKind
                                                                                                .PATH);
                                                                                f.setName(
                                                                                        vlElmName);
                                                                                /*
                                                                                 * EndToEndFlowSegment seg = e2eFlow
                                                                                 * .createOwnedEndToEndFlowSegment(); seg.setFlowElement( f);
                                                                                 * seg.setContext(sub);
                                                                                 */
                                                                                break;
                                                                            }
                                                                        }
                                                                    }
                                                                    i++; // increment by 1 here, for
                                                                    // loop will also increment
                                                                    // by 1
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
                };

        modifyAadlDocument(project, copOfOrig.getName(), createFlowSpecs);

        sysImpls.clear();
        subComps.clear();
        sysTypes.clear();
        BiConsumer<String, XtextResource> trackInfo =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {
                                                org.osate.aadl2.SystemImplementation s =
                                                        (org.osate.aadl2.SystemImplementation) obj;
                                                sysImpls.add(s);
                                            }

                                            if (obj instanceof org.osate.aadl2.Subcomponent) {
                                                org.osate.aadl2.Subcomponent s =
                                                        (org.osate.aadl2.Subcomponent) obj;
                                                subComps.add(s);
                                            }

                                            if (obj instanceof org.osate.aadl2.SystemType) {
                                                org.osate.aadl2.SystemType s =
                                                        (org.osate.aadl2.SystemType) obj;
                                                sysTypes.add(s);
                                            }
                                        });
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), trackInfo);

        BiConsumer<String, XtextResource> createCCRFlow =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {
                                                org.osate.aadl2.SystemImplementation sysImpl =
                                                        (org.osate.aadl2.SystemImplementation) obj;
                                                if (sysImpl.getName().equals(synthName)) {
                                                    for (Subcomponent sub :
                                                            sysImpl.getAllSubcomponents()) {
                                                        org.osate.aadl2.SystemType sysType =
                                                                (org.osate.aadl2.SystemType)
                                                                        sub.getComponentType();
                                                        if (sysType.getName().equals("CCR")) {
                                                            for (String flowName :
                                                                    Odm2Z3.vlStartsFromGPM
                                                                            .keySet()) {
                                                                Feature boundaryPort = null;
                                                                Feature pathPort = null;

                                                                List<String> flowSegments =
                                                                        removeDuplicates(
                                                                                vlflowconMap.get(
                                                                                        flowName));

                                                                if (!presentInFlow(
                                                                        sub.getName(),
                                                                        flowSegments)) {
                                                                    continue;
                                                                }

                                                                if (isCCRSource(sub, flowName)
                                                                        && Odm2Z3.vlStartsFromGPM
                                                                                        .get(
                                                                                                flowName)
                                                                                == true) {
                                                                    for (Feature ft2 :
                                                                            sysType
                                                                                    .getAllFeatures()) {
                                                                        if (ft2.getName()
                                                                                .equals(
                                                                                        ccrBoundaryPort
                                                                                                .get(
                                                                                                        flowName))) {
                                                                            boundaryPort = ft2;
                                                                            break;
                                                                        }
                                                                    }
                                                                    if (boundaryPort
                                                                            != null /* && pathPort == null */) {
                                                                        FlowSpecification f2 =
                                                                                sysType
                                                                                        .createOwnedFlowSpecification();
                                                                        FlowEnd out =
                                                                                f2.createOutEnd();
                                                                        f2.setKind(FlowKind.SOURCE);
                                                                        f2.setName(
                                                                                flowName
                                                                                        + "_ccrsource_"
                                                                                        + sub
                                                                                                .getName());
                                                                        f2.setOutEnd(out);
                                                                        out.setFeature(
                                                                                boundaryPort);
                                                                    }
                                                                }

                                                                if (isCCRSink(sub, flowName)
                                                                        && Odm2Z3.vlStartsFromGPM
                                                                                        .get(
                                                                                                flowName)
                                                                                == false) {
                                                                    for (Feature ft2 :
                                                                            sysType
                                                                                    .getAllFeatures()) {
                                                                        if (ft2.getName()
                                                                                .equals(
                                                                                        ccrBoundaryPort
                                                                                                .get(
                                                                                                        flowName))) {
                                                                            boundaryPort = ft2;
                                                                            break;
                                                                        }
                                                                    }
                                                                    if (boundaryPort
                                                                            != null /* && pathPort == null */) {
                                                                        FlowSpecification f2 =
                                                                                sysType
                                                                                        .createOwnedFlowSpecification();
                                                                        FlowEnd in =
                                                                                f2.createInEnd();
                                                                        f2.setKind(FlowKind.SINK);
                                                                        f2.setName(
                                                                                flowName
                                                                                        + "_ccrsink_"
                                                                                        + sub
                                                                                                .getName());
                                                                        f2.setInEnd(in);
                                                                        in.setFeature(boundaryPort);
                                                                    }
                                                                }
                                                                if (!isCCRSource(sub, flowName)
                                                                        && !isCCRSink(
                                                                                sub, flowName)) {
                                                                    FlowSpecification f2 =
                                                                            sysType
                                                                                    .createOwnedFlowSpecification();
                                                                    Pair<String, String>
                                                                            boundaryPorts =
                                                                                    getBoundaryPorts(
                                                                                            sub
                                                                                                    .getName(),
                                                                                            flowSegments);
                                                                    if (boundaryPorts == null) {
                                                                        continue;
                                                                    }
                                                                    for (Feature ft2 :
                                                                            sysType
                                                                                    .getAllFeatures()) {
                                                                        if (ft2
                                                                                        instanceof
                                                                                        org.osate
                                                                                                .aadl2
                                                                                                .DataPort
                                                                                && ft2.getName()
                                                                                        .equals(
                                                                                                boundaryPorts
                                                                                                        .getFirst())) {
                                                                            boundaryPort = ft2;
                                                                        }

                                                                        if (ft2
                                                                                        instanceof
                                                                                        org.osate
                                                                                                .aadl2
                                                                                                .DataPort
                                                                                && ft2.getName()
                                                                                        .equals(
                                                                                                boundaryPorts
                                                                                                        .getSecond())) {
                                                                            pathPort = ft2;
                                                                        }
                                                                    }

                                                                    if (boundaryPort != null
                                                                            && pathPort != null) {
                                                                        f2.setKind(FlowKind.PATH);
                                                                        f2.setName(
                                                                                flowName
                                                                                        + "_ccre2e_"
                                                                                        + sub
                                                                                                .getName());
                                                                        FlowEnd in =
                                                                                f2.createInEnd();
                                                                        f2.setInEnd(in);
                                                                        in.setFeature(boundaryPort);
                                                                        FlowEnd out =
                                                                                f2.createOutEnd();
                                                                        f2.setOutEnd(out);
                                                                        out.setFeature(pathPort);
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        });
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), createCCRFlow);

        Map<String, Integer> vlTomtu = Z3ModelReader.getMap_VLToMtu(z3Model2);
        Map<String, Integer> vlTobag = Z3ModelReader.getMap_VLToBag(z3Model2);

        BiConsumer<String, XtextResource> createCCRFlowImpl =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {

                                                org.osate.aadl2.SystemImplementation sysImpl =
                                                        (org.osate.aadl2.SystemImplementation) obj;

                                                for (String flowName :
                                                        Odm2Z3.vlStartsFromGPM.keySet()) {
                                                    if (Odm2Z3.vlStartsFromGPM.get(flowName)
                                                            == true) {
                                                        List<String> flowSegments =
                                                                removeDuplicates(
                                                                        vlflowconMap.get(flowName));
                                                        int i = 0;
                                                        int ccrBoundary = -1;

                                                        for (String comp : flowSegments) {
                                                            if (comp.contains(
                                                                    "CCR")) { // TODO : use CCR type
                                                                // from Oyster
                                                                // properties
                                                                ccrBoundary = i;
                                                                break;
                                                            }
                                                            i++;
                                                        }

                                                        String ccrComp =
                                                                flowSegments.get(i).split("\\.")[0];
                                                        String ccrPort =
                                                                flowSegments.get(i).split("\\.")[1];

                                                        if (!sysImpl.getName().contains(ccrComp)) {
                                                            // only process ccrComp for the current
                                                            // flow
                                                            continue;
                                                        }

                                                        if (ccrBoundary < 0) {
                                                            // fail silently
                                                            continue;
                                                        }

                                                        FlowImplementation flowImpl =
                                                                sysImpl
                                                                        .createOwnedFlowImplementation();
                                                        flowImpl.setKind(FlowKind.SOURCE);

                                                        for (String mtuFlow : vlTomtu.keySet()) {
                                                            if (flowName.contains(mtuFlow)) {
                                                                if (vlTomtu.get(
                                                                                /* flowName.replaceAll("\\.", "_").split("_")[0] */ mtuFlow)
                                                                        != null) {
                                                                    PropertyAssociation pae2e =
                                                                            flowImpl
                                                                                    .createOwnedPropertyAssociation();
                                                                    Property propertye2e =
                                                                            props.get("mtu");
                                                                    pae2e.setProperty(propertye2e);
                                                                    ModalPropertyValue propVale2e =
                                                                            pae2e
                                                                                    .createOwnedValue();
                                                                    IntegerLiteral vale2e =
                                                                            (IntegerLiteral)
                                                                                    propVale2e
                                                                                            .createOwnedValue(
                                                                                                    Aadl2Package
                                                                                                            .eINSTANCE
                                                                                                            .getIntegerLiteral());
                                                                    vale2e.setValue(
                                                                            vlTomtu.get(
                                                                                    /* flowName.replaceAll("\\.", "_").split("_")[0] */ mtuFlow));
                                                                    break;
                                                                }
                                                            }
                                                        }

                                                        for (String bagFlow : vlTomtu.keySet()) {
                                                            if (flowName.contains(bagFlow)) {
                                                                if (vlTobag.get(
                                                                                /* flowName.replaceAll("\\.", "_").split("_")[0] */ bagFlow)
                                                                        != null) {
                                                                    PropertyAssociation pae2e2 =
                                                                            flowImpl
                                                                                    .createOwnedPropertyAssociation();
                                                                    Property propertye2e2 =
                                                                            props.get("bag");
                                                                    pae2e2.setProperty(
                                                                            propertye2e2);
                                                                    ModalPropertyValue propVale2e2 =
                                                                            pae2e2
                                                                                    .createOwnedValue();
                                                                    IntegerLiteral vale2e2 =
                                                                            (IntegerLiteral)
                                                                                    propVale2e2
                                                                                            .createOwnedValue(
                                                                                                    Aadl2Package
                                                                                                            .eINSTANCE
                                                                                                            .getIntegerLiteral());
                                                                    vale2e2.setValue(
                                                                            vlTobag.get(
                                                                                    /* flowName.replaceAll("\\.", "_").split("_")[0] */ bagFlow));
                                                                }
                                                                break;
                                                            }
                                                        }

                                                        for (FlowSpecification flowSpec :
                                                                sysImpl.getType()
                                                                        .getAllFlowSpecifications()) {
                                                            if (flowSpec.getName()
                                                                    .contains(
                                                                            flowName
                                                                                    + "_ccrsource_"
                                                                                    + ccrComp)) {
                                                                flowImpl.setSpecification(flowSpec);
                                                                break;
                                                            }
                                                        }

                                                        i = 0;
                                                        while (i < ccrBoundary) {
                                                            String currentSegment =
                                                                    flowSegments.get(i);
                                                            if (!currentSegment.contains(".")) {
                                                                // current segment is a connection,
                                                                // subcomponent of toplevel
                                                                for (Connection conn :
                                                                        sysImpl
                                                                                .getAllConnections()) {

                                                                    if (conn.getName()
                                                                            .equals(
                                                                                    currentSegment)) {
                                                                        FlowSegment segment =
                                                                                flowImpl
                                                                                        .createOwnedFlowSegment();
                                                                        segment.setFlowElement(
                                                                                conn);
                                                                        break;
                                                                    }
                                                                }
                                                                i++;
                                                                continue;
                                                            }

                                                            String currentComponent =
                                                                    currentSegment.split("\\.")[0];
                                                            String currentPort =
                                                                    currentSegment.split("\\.")[1];

                                                            for (Subcomponent sub :
                                                                    sysImpl.getAllSubcomponents()) {
                                                                if (sub.getName()
                                                                                .contains(
                                                                                        currentComponent)
                                                                        || currentComponent
                                                                                .contains(
                                                                                        sub
                                                                                                .getName())) {
                                                                    for (FlowSpecification
                                                                            flowSpec :
                                                                                    sub.getComponentType()
                                                                                            .getAllFlowSpecifications()) {
                                                                        if (flowSpec.getName()
                                                                                .equals(
                                                                                        flowName
                                                                                                + "_"
                                                                                                + currentComponent)) {
                                                                            FlowSegment segment =
                                                                                    flowImpl
                                                                                            .createOwnedFlowSegment();
                                                                            segment.setFlowElement(
                                                                                    flowSpec);
                                                                            segment.setContext(sub);
                                                                            break;
                                                                        }
                                                                    }
                                                                }
                                                            }

                                                            if (i + 1 < ccrBoundary) {
                                                                String nextSegment =
                                                                        flowSegments.get(i + 1);
                                                                if (nextSegment.contains(".")) {
                                                                    String nextComponent =
                                                                            nextSegment
                                                                                    .split("\\.")[
                                                                                    0];
                                                                    String nextPort =
                                                                            nextSegment
                                                                                    .split("\\.")[
                                                                                    1];
                                                                    if (currentComponent.equals(
                                                                            nextComponent)) {
                                                                        // i, i+1 are the same
                                                                        // component, their flow
                                                                        // path spec is already
                                                                        // processed, moving to next
                                                                        // port or connection
                                                                        i += 2;
                                                                    } else {
                                                                        // move to next component
                                                                        // (component port or
                                                                        // connection)
                                                                        i += 1;
                                                                    }
                                                                } else {
                                                                    // next segment is a connection
                                                                    i += 1;
                                                                }
                                                            } else {
                                                                break;
                                                            }
                                                        }

                                                        for (Feature ft :
                                                                sysImpl.getAllFeatures()) {
                                                            if (ft.getName()
                                                                    .equals(
                                                                            ccrBoundaryPort.get(
                                                                                    flowName))) {
                                                                FlowEnd outEnd =
                                                                        flowImpl.createOutEnd();
                                                                outEnd.setFeature(ft);
                                                                flowImpl.setOutEnd(outEnd);
                                                                break;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        });
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), createCCRFlowImpl);

        BiConsumer<String, XtextResource> createCCRE2EFlows =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {

                                                org.osate.aadl2.SystemImplementation sysImpl =
                                                        (org.osate.aadl2.SystemImplementation) obj;
                                                if (sysImpl.getName().contains("CCR")) {

                                                    for (String flowName :
                                                            Odm2Z3.vlStartsFromGPM.keySet()) {
                                                        List<String> flowSegments =
                                                                removeDuplicates(
                                                                        vlflowconMap.get(flowName));
                                                        String ccrComp =
                                                                sysImpl.getName().split("\\.")[1];
                                                        if (presentInFlow(ccrComp, flowSegments)) {
                                                            if (!isCCRSource(
                                                                            getSubcomponentByName(
                                                                                    ccrComp),
                                                                            flowName)
                                                                    && !isCCRSink(
                                                                            getSubcomponentByName(
                                                                                    ccrComp),
                                                                            flowName)) {
                                                                Pair<String, String> boundaryPorts =
                                                                        getBoundaryPorts(
                                                                                sysImpl.getName()
                                                                                        .split(
                                                                                                "\\.")[
                                                                                        1],
                                                                                flowSegments);
                                                                String inPort =
                                                                        boundaryPorts.getFirst();
                                                                String outPort =
                                                                        boundaryPorts.getSecond();

                                                                int startIndex = -1;
                                                                int endIndex = -1;
                                                                for (int i = 0;
                                                                        i < flowSegments.size();
                                                                        i++) {
                                                                    if (flowSegments
                                                                                    .get(i)
                                                                                    .contains(
                                                                                            ccrComp
                                                                                                    + "."
                                                                                                    + inPort)
                                                                            && startIndex == -1) {
                                                                        startIndex = i;
                                                                        continue;
                                                                    }
                                                                    if (flowSegments
                                                                                    .get(i)
                                                                                    .contains(
                                                                                            ccrComp
                                                                                                    + "."
                                                                                                    + outPort)
                                                                            && startIndex != -1
                                                                            && endIndex == -1) {
                                                                        endIndex = i;
                                                                        break;
                                                                    }
                                                                }

                                                                FlowImplementation flowImpl =
                                                                        sysImpl
                                                                                .createOwnedFlowImplementation();
                                                                flowImpl.setKind(FlowKind.PATH);

                                                                for (String mtuFlow :
                                                                        vlTomtu.keySet()) {
                                                                    if (flowName.contains(
                                                                            mtuFlow)) {
                                                                        if (vlTomtu.get(
                                                                                        /* flowName.replaceAll("\\.", "_").split("_")[0] */ mtuFlow)
                                                                                != null) {
                                                                            PropertyAssociation
                                                                                    pae2e =
                                                                                            flowImpl
                                                                                                    .createOwnedPropertyAssociation();
                                                                            Property propertye2e =
                                                                                    props.get(
                                                                                            "mtu");
                                                                            pae2e.setProperty(
                                                                                    propertye2e);
                                                                            ModalPropertyValue
                                                                                    propVale2e =
                                                                                            pae2e
                                                                                                    .createOwnedValue();
                                                                            IntegerLiteral vale2e =
                                                                                    (IntegerLiteral)
                                                                                            propVale2e
                                                                                                    .createOwnedValue(
                                                                                                            Aadl2Package
                                                                                                                    .eINSTANCE
                                                                                                                    .getIntegerLiteral());
                                                                            vale2e.setValue(
                                                                                    vlTomtu.get(
                                                                                            /*
                                                                                             * flowName.replaceAll("\\.", "_").split("_")[0]
                                                                                             */ mtuFlow));
                                                                            break;
                                                                        }
                                                                    }
                                                                }

                                                                for (String bagFlow :
                                                                        vlTomtu.keySet()) {
                                                                    if (flowName.contains(
                                                                            bagFlow)) {
                                                                        if (vlTobag.get(
                                                                                        /* flowName.replaceAll("\\.", "_").split("_")[0] */ bagFlow)
                                                                                != null) {
                                                                            PropertyAssociation
                                                                                    pae2e2 =
                                                                                            flowImpl
                                                                                                    .createOwnedPropertyAssociation();
                                                                            Property propertye2e2 =
                                                                                    props.get(
                                                                                            "bag");
                                                                            pae2e2.setProperty(
                                                                                    propertye2e2);
                                                                            ModalPropertyValue
                                                                                    propVale2e2 =
                                                                                            pae2e2
                                                                                                    .createOwnedValue();
                                                                            IntegerLiteral vale2e2 =
                                                                                    (IntegerLiteral)
                                                                                            propVale2e2
                                                                                                    .createOwnedValue(
                                                                                                            Aadl2Package
                                                                                                                    .eINSTANCE
                                                                                                                    .getIntegerLiteral());
                                                                            vale2e2.setValue(
                                                                                    vlTobag.get(
                                                                                            /*
                                                                                             * flowName.replaceAll("\\.", "_").split("_")[0]
                                                                                             */ bagFlow));
                                                                        }
                                                                        break;
                                                                    }
                                                                }

                                                                for (FlowSpecification flowSpec :
                                                                        sysImpl.getType()
                                                                                .getAllFlowSpecifications()) {
                                                                    if (flowSpec.getName()
                                                                            .equals(
                                                                                    flowName
                                                                                            + "_ccre2e_"
                                                                                            + ccrComp)) {
                                                                        flowImpl.setSpecification(
                                                                                flowSpec);
                                                                        break;
                                                                    }
                                                                }

                                                                FlowEnd inEnd =
                                                                        flowImpl.createInEnd();
                                                                for (Feature ft :
                                                                        sysImpl.getAllFeatures()) {
                                                                    if (ft.getName()
                                                                            .equals(inPort)) {
                                                                        inEnd.setFeature(ft);
                                                                        flowImpl.setInEnd(inEnd);
                                                                        break;
                                                                    }
                                                                }

                                                                for (int i = startIndex + 1;
                                                                        i < endIndex;
                                                                        i++) {

                                                                    String currentSegment =
                                                                            flowSegments.get(i);
                                                                    if (!currentSegment.contains(
                                                                            ".")) {
                                                                        // current segment is a
                                                                        // connection, subcomponent
                                                                        // of
                                                                        // toplevel
                                                                        for (Connection conn :
                                                                                sysImpl
                                                                                        .getAllConnections()) {

                                                                            if (conn.getName()
                                                                                    .equals(
                                                                                            currentSegment)) {
                                                                                FlowSegment
                                                                                        segment =
                                                                                                flowImpl
                                                                                                        .createOwnedFlowSegment();
                                                                                segment
                                                                                        .setFlowElement(
                                                                                                conn);
                                                                                break;
                                                                            }
                                                                        }
                                                                        continue;
                                                                    }

                                                                    String currentComponent =
                                                                            currentSegment
                                                                                    .split("\\.")[
                                                                                    0];
                                                                    String currentPort =
                                                                            currentSegment
                                                                                    .split("\\.")[
                                                                                    1];

                                                                    for (Subcomponent sub :
                                                                            sysImpl
                                                                                    .getAllSubcomponents()) {
                                                                        if (sub.getName()
                                                                                        .contains(
                                                                                                currentComponent)
                                                                                || currentComponent
                                                                                        .contains(
                                                                                                sub
                                                                                                        .getName())) {
                                                                            for (FlowSpecification
                                                                                    flowSpec :
                                                                                            sub.getComponentType()
                                                                                                    .getAllFlowSpecifications()) {

                                                                                if (flowSpec.getName()
                                                                                        .equals(
                                                                                                flowName
                                                                                                        + "_"
                                                                                                        + currentComponent)) {
                                                                                    FlowSegment
                                                                                            segment =
                                                                                                    flowImpl
                                                                                                            .createOwnedFlowSegment();
                                                                                    segment
                                                                                            .setFlowElement(
                                                                                                    flowSpec);
                                                                                    segment
                                                                                            .setContext(
                                                                                                    sub);
                                                                                    break;
                                                                                }
                                                                            }
                                                                        }
                                                                    }

                                                                    if (i + 1
                                                                            < flowSegments.size()) {
                                                                        String nextSegment =
                                                                                flowSegments.get(
                                                                                        i + 1);
                                                                        if (nextSegment.contains(
                                                                                ".")) {
                                                                            String nextComponent =
                                                                                    nextSegment
                                                                                            .split(
                                                                                                    "\\.")[
                                                                                            0];

                                                                            if (currentComponent
                                                                                    .equals(
                                                                                            nextComponent)) {
                                                                                // i, i+1 are the
                                                                                // same
                                                                                // component, their
                                                                                // flow
                                                                                // path spec is
                                                                                // already
                                                                                // processed, moving
                                                                                // to
                                                                                // next port or
                                                                                // connection
                                                                                i += 1;

                                                                            } else {
                                                                                // move to next
                                                                                // component
                                                                                // (component
                                                                                // port or
                                                                                // connection)
                                                                                // i += 1;
                                                                            }
                                                                        } else {
                                                                            // next segment is a
                                                                            // connection
                                                                            // i += 1;
                                                                        }
                                                                    } else {
                                                                        break;
                                                                    }
                                                                }

                                                                FlowEnd outEn =
                                                                        flowImpl.createOutEnd();
                                                                for (Feature ft :
                                                                        sysImpl.getAllFeatures()) {
                                                                    if (ft.getName()
                                                                            .equals(outPort)) {
                                                                        outEn.setFeature(ft);
                                                                        flowImpl.setOutEnd(outEn);
                                                                        break;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        });
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), createCCRE2EFlows);

        BiConsumer<String, XtextResource> createCCRFlowImplSink =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {

                                                org.osate.aadl2.SystemImplementation sysImpl =
                                                        (org.osate.aadl2.SystemImplementation) obj;

                                                for (String flowName :
                                                        Odm2Z3.vlEndsAtGPM.keySet()) {

                                                    if (Odm2Z3./* vlStartsFromGPM */ vlEndsAtGPM
                                                                            .get(flowName)
                                                                    == true
                                                            && Odm2Z3.vlStartsFromGPM.get(flowName)
                                                                    == false) {
                                                        List<String> flowSegments =
                                                                removeDuplicates(
                                                                        vlflowconMap.get(flowName));
                                                        int i = flowSegments.size() - 1;
                                                        int ccrBoundary = -1;

                                                        for (; i >= 0; i--) {
                                                            String comp = flowSegments.get(i);
                                                            if (comp.contains(
                                                                    "CCR")) { // TODO : use CCR type
                                                                // from Oyster
                                                                // properties
                                                                ccrBoundary = i;
                                                                break;
                                                            }
                                                        }

                                                        String ccrComp =
                                                                flowSegments.get(i).split("\\.")[0];
                                                        String ccrPort =
                                                                flowSegments.get(i).split("\\.")[1];

                                                        if (!sysImpl.getName().contains(ccrComp)) {
                                                            // only process ccrComp for the current
                                                            // flow
                                                            continue;
                                                        }

                                                        if (ccrBoundary < 0) {
                                                            // fail silently
                                                            continue;
                                                        }

                                                        FlowImplementation flowImpl =
                                                                sysImpl
                                                                        .createOwnedFlowImplementation();
                                                        flowImpl.setKind(
                                                                FlowKind./* SOURCE */ SINK);

                                                        for (Feature ft :
                                                                sysImpl.getAllFeatures()) {
                                                            if (ft.getName()
                                                                    .equals(
                                                                            ccrBoundaryPort.get(
                                                                                    flowName))) {
                                                                FlowEnd inEnd =
                                                                        flowImpl.
                                                                                /* createOutEnd */ createInEnd();
                                                                inEnd.setFeature(ft);
                                                                flowImpl./* setOutEnd */ setInEnd(
                                                                        inEnd);
                                                                break;
                                                            }
                                                        }

                                                        for (String mtuFlow : vlTomtu.keySet()) {
                                                            if (flowName.contains(mtuFlow)) {
                                                                if (vlTomtu.get(
                                                                                /* flowName.replaceAll("\\.", "_").split("_")[0] */ mtuFlow)
                                                                        != null) {
                                                                    PropertyAssociation pae2e =
                                                                            flowImpl
                                                                                    .createOwnedPropertyAssociation();
                                                                    Property propertye2e =
                                                                            props.get("mtu");
                                                                    pae2e.setProperty(propertye2e);
                                                                    ModalPropertyValue propVale2e =
                                                                            pae2e
                                                                                    .createOwnedValue();
                                                                    IntegerLiteral vale2e =
                                                                            (IntegerLiteral)
                                                                                    propVale2e
                                                                                            .createOwnedValue(
                                                                                                    Aadl2Package
                                                                                                            .eINSTANCE
                                                                                                            .getIntegerLiteral());
                                                                    vale2e.setValue(
                                                                            vlTomtu.get(
                                                                                    /* flowName.replaceAll("\\.", "_").split("_")[0] */ mtuFlow));
                                                                    break;
                                                                }
                                                            }
                                                        }

                                                        for (String bagFlow : vlTomtu.keySet()) {
                                                            if (flowName.contains(bagFlow)) {
                                                                if (vlTobag.get(
                                                                                /* flowName.replaceAll("\\.", "_").split("_")[0] */ bagFlow)
                                                                        != null) {
                                                                    PropertyAssociation pae2e2 =
                                                                            flowImpl
                                                                                    .createOwnedPropertyAssociation();
                                                                    Property propertye2e2 =
                                                                            props.get("bag");
                                                                    pae2e2.setProperty(
                                                                            propertye2e2);
                                                                    ModalPropertyValue propVale2e2 =
                                                                            pae2e2
                                                                                    .createOwnedValue();
                                                                    IntegerLiteral vale2e2 =
                                                                            (IntegerLiteral)
                                                                                    propVale2e2
                                                                                            .createOwnedValue(
                                                                                                    Aadl2Package
                                                                                                            .eINSTANCE
                                                                                                            .getIntegerLiteral());
                                                                    vale2e2.setValue(
                                                                            vlTobag.get(
                                                                                    /* flowName.replaceAll("\\.", "_").split("_")[0] */ bagFlow));
                                                                }
                                                                break;
                                                            }
                                                        }

                                                        for (FlowSpecification flowSpec :
                                                                sysImpl.getType()
                                                                        .getAllFlowSpecifications()) {
                                                            if (flowSpec.getName()
                                                                    .contains(
                                                                            flowName
                                                                                    + "_ccrsink_"
                                                                                    + ccrComp)) {
                                                                flowImpl.setSpecification(flowSpec);
                                                                break;
                                                            }
                                                        }

                                                        i = /* 0 */ ccrBoundary + 1;
                                                        while (
                                                        /* i < ccrBoundary */ i
                                                                < flowSegments.size()) {
                                                            String currentSegment =
                                                                    flowSegments.get(i);
                                                            if (!currentSegment.contains(".")) {
                                                                // current segment is a connection,
                                                                // subcomponent of toplevel
                                                                for (Connection conn :
                                                                        sysImpl
                                                                                .getAllConnections()) {

                                                                    if (conn.getName()
                                                                            .equals(
                                                                                    currentSegment)) {
                                                                        FlowSegment segment =
                                                                                flowImpl
                                                                                        .createOwnedFlowSegment();
                                                                        segment.setFlowElement(
                                                                                conn);
                                                                        break;
                                                                    }
                                                                }
                                                                i++;
                                                                continue;
                                                            }

                                                            String currentComponent =
                                                                    currentSegment.split("\\.")[0];

                                                            for (Subcomponent sub :
                                                                    sysImpl.getAllSubcomponents()) {
                                                                if (sub.getName()
                                                                                .contains(
                                                                                        currentComponent)
                                                                        || currentComponent
                                                                                .contains(
                                                                                        sub
                                                                                                .getName())) {
                                                                    for (FlowSpecification
                                                                            flowSpec :
                                                                                    sub.getComponentType()
                                                                                            .getAllFlowSpecifications()) {
                                                                        if (flowSpec.getName()
                                                                                .equals(
                                                                                        flowName
                                                                                                + "_"
                                                                                                + currentComponent)) {
                                                                            FlowSegment segment =
                                                                                    flowImpl
                                                                                            .createOwnedFlowSegment();
                                                                            segment.setFlowElement(
                                                                                    flowSpec);
                                                                            segment.setContext(sub);
                                                                            break;
                                                                        }
                                                                    }
                                                                }
                                                            }

                                                            if (i + 1
                                                                    <
                                                                    /* ccrBoundary */ flowSegments
                                                                            .size()) {
                                                                String nextSegment =
                                                                        flowSegments.get(i + 1);
                                                                if (nextSegment.contains(".")) {
                                                                    String nextComponent =
                                                                            nextSegment
                                                                                    .split("\\.")[
                                                                                    0];
                                                                    String nextPort =
                                                                            nextSegment
                                                                                    .split("\\.")[
                                                                                    1];
                                                                    if (currentComponent.equals(
                                                                            nextComponent)) {
                                                                        // i, i+1 are the same
                                                                        // component, their flow
                                                                        // path spec is already
                                                                        // processed, moving to next
                                                                        // port or connection
                                                                        i += 2;
                                                                    } else {
                                                                        // move to next component
                                                                        // (component port or
                                                                        // connection)
                                                                        i += 1;
                                                                    }
                                                                } else {
                                                                    // next segment is a connection
                                                                    i += 1;
                                                                }
                                                            } else {
                                                                break;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        });
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), createCCRFlowImplSink);

        BiConsumer<String, XtextResource> topLevelEndToEndFlow =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {
                                                org.osate.aadl2.SystemImplementation sysImpl =
                                                        (org.osate.aadl2.SystemImplementation) obj;
                                                if (sysImpl.getName().equals(synthName)) {
                                                    // create end to end flow ending at valve
                                                    for (String flowName : vlflowconMap.keySet()) {
                                                        List<String> flowSegments =
                                                                removeDuplicates(
                                                                        vlflowconMap.get(flowName));
                                                        int i = 0;
                                                        String currentSegment = flowSegments.get(i);

                                                        EndToEndFlow e2eFlow =
                                                                sysImpl.createOwnedEndToEndFlow();

                                                        if (ccrSource.containsKey(flowName)) {
                                                            while (!currentSegment.contains(
                                                                    "CCR")) {
                                                                i++;
                                                                currentSegment =
                                                                        flowSegments.get(i);
                                                            }
                                                            i++;
                                                            String ccrComp =
                                                                    ccrSource
                                                                            .get(flowName)
                                                                            .getFirst();

                                                            for (Subcomponent sub :
                                                                    sysImpl.getAllSubcomponents()) {
                                                                if (sub.getName().contains(ccrComp)
                                                                        || ccrComp.contains(
                                                                                sub.getName())) {
                                                                    for (FlowSpecification
                                                                            flowSpec :
                                                                                    sub.getComponentType()
                                                                                            .getAllFlowSpecifications()) {
                                                                        if (flowSpec.getName()
                                                                                .equals(
                                                                                        flowName
                                                                                                + "_ccrsource_"
                                                                                                + ccrComp)) {
                                                                            EndToEndFlowSegment
                                                                                    segment =
                                                                                            e2eFlow
                                                                                                    .createOwnedEndToEndFlowSegment();
                                                                            segment.setFlowElement(
                                                                                    flowSpec);
                                                                            segment.setContext(sub);
                                                                            break;
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }

                                                        for (String mtuFlow : vlTomtu.keySet()) {
                                                            if (flowName.contains(mtuFlow)) {
                                                                if (vlTomtu.get(
                                                                                /* flowName.replaceAll("\\.", "_").split("_")[0] */ mtuFlow)
                                                                        != null) {
                                                                    PropertyAssociation pae2e =
                                                                            e2eFlow
                                                                                    .createOwnedPropertyAssociation();
                                                                    Property propertye2e =
                                                                            props.get("mtu");
                                                                    pae2e.setProperty(propertye2e);
                                                                    ModalPropertyValue propVale2e =
                                                                            pae2e
                                                                                    .createOwnedValue();
                                                                    IntegerLiteral vale2e =
                                                                            (IntegerLiteral)
                                                                                    propVale2e
                                                                                            .createOwnedValue(
                                                                                                    Aadl2Package
                                                                                                            .eINSTANCE
                                                                                                            .getIntegerLiteral());
                                                                    vale2e.setValue(
                                                                            vlTomtu.get(
                                                                                    /* flowName.replaceAll("\\.", "_").split("_")[0] */ mtuFlow));
                                                                    break;
                                                                }
                                                            }
                                                        }

                                                        for (String bagFlow : vlTomtu.keySet()) {
                                                            if (flowName.contains(bagFlow)) {
                                                                if (vlTobag.get(
                                                                                /* flowName.replaceAll("\\.", "_").split("_")[0] */ bagFlow)
                                                                        != null) {
                                                                    PropertyAssociation pae2e2 =
                                                                            e2eFlow
                                                                                    .createOwnedPropertyAssociation();
                                                                    Property propertye2e2 =
                                                                            props.get("bag");
                                                                    pae2e2.setProperty(
                                                                            propertye2e2);
                                                                    ModalPropertyValue propVale2e2 =
                                                                            pae2e2
                                                                                    .createOwnedValue();
                                                                    IntegerLiteral vale2e2 =
                                                                            (IntegerLiteral)
                                                                                    propVale2e2
                                                                                            .createOwnedValue(
                                                                                                    Aadl2Package
                                                                                                            .eINSTANCE
                                                                                                            .getIntegerLiteral());
                                                                    vale2e2.setValue(
                                                                            vlTobag.get(
                                                                                    /* flowName.replaceAll("\\.", "_").split("_")[0] */ bagFlow));
                                                                }
                                                            }
                                                        }

                                                        e2eFlow.setName(flowName + "toplevel_e2e");

                                                        while (i < flowSegments.size()) {

                                                            currentSegment = flowSegments.get(i);

                                                            if (!currentSegment.contains(".")) {
                                                                // current segment is a
                                                                // connection, subcomponent of
                                                                // toplevel
                                                                for (Connection conn :
                                                                        sysImpl
                                                                                .getAllConnections()) {

                                                                    if (conn.getName()
                                                                            .equals(
                                                                                    currentSegment)) {
                                                                        EndToEndFlowSegment
                                                                                segment =
                                                                                        e2eFlow
                                                                                                .createOwnedEndToEndFlowSegment();
                                                                        segment.setFlowElement(
                                                                                conn);
                                                                        break;
                                                                    }
                                                                }
                                                                i++;
                                                                continue;
                                                            }
                                                            String currentComponent =
                                                                    currentSegment.split("\\.")[0];

                                                            for (Subcomponent sub :
                                                                    sysImpl.getAllSubcomponents()) {
                                                                if (sub.getName()
                                                                                .contains(
                                                                                        currentComponent)
                                                                        || currentComponent
                                                                                .contains(
                                                                                        sub
                                                                                                .getName())) {
                                                                    String flowSpecName =
                                                                            flowName
                                                                                    + "_"
                                                                                    + currentComponent;
                                                                    if (sub.getComponentType()
                                                                            .getName()
                                                                            .equals("CCR")) {
                                                                        flowSpecName =
                                                                                getFlowName(
                                                                                        flowName,
                                                                                        sub);
                                                                    }
                                                                    for (FlowSpecification
                                                                            flowSpec :
                                                                                    sub.getComponentType()
                                                                                            .getAllFlowSpecifications()) {
                                                                        if (flowSpec.getName()
                                                                                .equals(
                                                                                        flowSpecName)) {
                                                                            EndToEndFlowSegment
                                                                                    segment =
                                                                                            e2eFlow
                                                                                                    .createOwnedEndToEndFlowSegment();
                                                                            segment.setFlowElement(
                                                                                    flowSpec);
                                                                            segment.setContext(sub);
                                                                            break;
                                                                        }
                                                                    }
                                                                }
                                                            }

                                                            if (ccrSink.containsKey(flowName)) {
                                                                if (ccrSink.get(flowName)
                                                                        .getFirst()
                                                                        .equals(currentComponent)) {
                                                                    String ccrComp =
                                                                            ccrSink.get(flowName)
                                                                                    .getFirst();

                                                                    /*
                                                                     * for (Subcomponent sub : sysImpl.getAllSubcomponents()) { if
                                                                     * (sub.getName().contains(ccrComp) || ccrComp.contains(sub.getName())) {
                                                                     * for (FlowSpecification flowSpec : sub.getComponentType()
                                                                     * .getAllFlowSpecifications()) { if (flowSpec.getName() .equals(flowName +
                                                                     * "_ccrsink_" + ccrComp)) { EndToEndFlowSegment segment = e2eFlow
                                                                     * .createOwnedEndToEndFlowSegment(); segment.setFlowElement(flowSpec);
                                                                     * segment.setContext(sub); break; } } } }
                                                                     */
                                                                    break;
                                                                }
                                                            }

                                                            if (flowSegments
                                                                    .get(i)
                                                                    .contains("CCR")) {
                                                                if (!isCCRSource(
                                                                                getSubcomponentByName(
                                                                                        currentComponent),
                                                                                flowName)
                                                                        && !isCCRSink(
                                                                                getSubcomponentByName(
                                                                                        currentComponent),
                                                                                flowName)) {
                                                                    while (!flowSegments
                                                                            .get(i + 1)
                                                                            .contains("CCR")) {
                                                                        i++;
                                                                    }
                                                                }
                                                            }

                                                            if (i + 1 < flowSegments.size()) {
                                                                String nextSegment =
                                                                        flowSegments.get(i + 1);
                                                                if (nextSegment.contains(".")) {
                                                                    String nextComponent =
                                                                            nextSegment
                                                                                    .split("\\.")[
                                                                                    0];
                                                                    String nextPort =
                                                                            nextSegment
                                                                                    .split("\\.")[
                                                                                    1];

                                                                    if (currentComponent.equals(
                                                                            nextComponent)) {
                                                                        // i, i+1 are the same
                                                                        // component, their flow
                                                                        // path spec is already
                                                                        // processed, moving to
                                                                        // next port or
                                                                        // connection
                                                                        i += 2;

                                                                    } else {
                                                                        // move to next
                                                                        // component (component
                                                                        // port or connection)
                                                                        i += 1;
                                                                    }
                                                                } else {
                                                                    // next segment is a
                                                                    // connection
                                                                    i += 1;
                                                                }
                                                            } else {
                                                                break;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        });
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), topLevelEndToEndFlow);

        // add optimal network bandwidth as OYSTER properties in top-level system
        // component
        if (fsbBandwidthYes) {
            BiConsumer<String, XtextResource> addNetBandwidth =
                    (file, resource) -> {
                        if (!Objects.isNull(resource)) {
                            TreeIterator<EObject> iterator = resource.getAllContents();
                            while (iterator.hasNext()) {
                                EObject cur = iterator.next();
                                if (cur instanceof org.osate.aadl2.SystemType) {
                                    org.osate.aadl2.SystemType s = (org.osate.aadl2.SystemType) cur;
                                    if (s.getName().equals(/* topLevelComponentType */ "IMA")) {
                                        for (PropertyAssociation p :
                                                s.getAllPropertyAssociations()) {
                                            // remove previously given bandwidth information
                                            if (p.getProperty().getName() != null
                                                    && p.getProperty()
                                                            .getName()
                                                            .equals("totalBandwidth")) {
                                                s.removePropertyAssociations(p.getProperty());
                                            } else if (p.getProperty().getName() != null
                                                    && p.getProperty()
                                                            .getName()
                                                            .equals("maxBandwidthPercentage")) {
                                                s.removePropertyAssociations(p.getProperty());
                                            }
                                        }

                                        // add newly computed feasible/optimal network bandwidth
                                        int bandwidth = Z3ModelReader.getNetBandwidth(z3Model);
                                        PropertyAssociation pa = s.createOwnedPropertyAssociation();
                                        Property property = props.get("networkBandwidth");
                                        pa.setProperty(property);
                                        ModalPropertyValue propVal = pa.createOwnedValue();
                                        IntegerLiteral val =
                                                (IntegerLiteral)
                                                        propVal.createOwnedValue(
                                                                Aadl2Package.eINSTANCE
                                                                        .getIntegerLiteral());
                                        val.setValue(bandwidth);
                                        break;
                                    }
                                }
                            }
                        }
                    };

            modifyAadlDocument(project, copOfOrig.getName(), addNetBandwidth);
        }

        HashMap<String, HashMap<String, Integer>> resourceUtilization =
                Z3ModelReader.readConst_ResourceUtilizations(z3Model);

        BiConsumer<String, XtextResource> addUtilizationProperties =
                (file, resource) -> {
                    if (!Objects.isNull(resource)) {
                        resource.getAllContents()
                                .forEachRemaining(
                                        obj -> {
                                            if (obj
                                                    instanceof
                                                    org.osate.aadl2.SystemImplementation) {
                                                org.osate.aadl2.SystemImplementation sysImpl =
                                                        (org.osate.aadl2.SystemImplementation) obj;
                                                for (Subcomponent sub :
                                                        sysImpl.getAllSubcomponents()) {
                                                    for (String comp :
                                                            resourceUtilization.keySet()) {
                                                        if (sub.getName().equals(comp)) {
                                                            HashMap<String, Integer>
                                                                    compUtilizations =
                                                                            resourceUtilization.get(
                                                                                    comp);

                                                            for (String property :
                                                                    compUtilizations.keySet()) {
                                                                boolean hasPropertyDefined = false;
                                                                for (PropertyAssociation pa :
                                                                        sub
                                                                                .getOwnedPropertyAssociations()) {
                                                                    if (pa.getProperty()
                                                                            .getName()
                                                                            .equals(property)) {
                                                                        hasPropertyDefined = true;
                                                                        break;
                                                                    }
                                                                }

                                                                if (hasPropertyDefined) {
                                                                    continue;
                                                                }
                                                                PropertyAssociation
                                                                        oysterPropAssociation =
                                                                                sub
                                                                                        .createOwnedPropertyAssociation();
                                                                Property oysterProperty =
                                                                        props.get(property);
                                                                oysterPropAssociation.setProperty(
                                                                        oysterProperty);
                                                                ModalPropertyValue value =
                                                                        oysterPropAssociation
                                                                                .createOwnedValue();
                                                                IntegerLiteral concreteVal =
                                                                        (IntegerLiteral)
                                                                                value
                                                                                        .createOwnedValue(
                                                                                                Aadl2Package
                                                                                                        .eINSTANCE
                                                                                                        .getIntegerLiteral());
                                                                concreteVal.setValue(
                                                                        compUtilizations.get(
                                                                                property));
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        });
                    }
                };

        modifyAadlDocument(project, copOfOrig.getName(), addUtilizationProperties);

        // remove the redundant top-level system type implementation
        removeRedundantAadlImpl(
                copOfOrig.getAbsolutePath(), implNames.get(0), packageName.split("\\.")[0]);
        List<EObject> synAadlObjects = aadlFile2Object(copOfOrig.getAbsolutePath());
        return synAadlObjects;
    }

    private static DataPort getDataPort(org.osate.aadl2.SystemType system, String port) {
        List<DataPort> dataPorts = system.getOwnedDataPorts();

        for (DataPort dataPort : dataPorts) {
            if (dataPort.getName().equals(port.split("\\.")[1])) {
                return dataPort;
            }
        }
        return null;
    }

    private static Feature getFeatureByName(
            org.osate.aadl2.SystemImplementation systemImpl, String name) {
        List<Feature> features = systemImpl.getAllFeatures();
        for (Feature feature : features) {
            if (feature.getName().equals(name)) {
                return feature;
            }
        }

        return null;
    }

    private static Connection getConnectionByName(
            org.osate.aadl2.SystemImplementation systemImpl, String name) {
        List<Connection> connections = systemImpl.getAllConnections();
        for (Connection connection : connections) {
            if (connection.getName().equals(name)) {
                return connection;
            }
        }

        return null;
    }

    private static String getParentImplName(String name) {
        for (org.osate.aadl2.SystemImplementation sysImpl : sysImpls) {
            for (Subcomponent subcomp : sysImpl.getAllSubcomponents()) {
                if (subcomp.getName().equals(name)
                        && !sysImpl.getName().equals("IMA.Synthesis")
                        && !sysImpl.getName().equals("IMA.Impl")) {
                    return sysImpl.getName();
                }
            }
        }
        return "";
    }

    private static org.osate.aadl2.SystemImplementation getParentImplementation(String comp) {
        for (org.osate.aadl2.SystemImplementation sysImpl : sysImpls) {
            List<Subcomponent> subcomponents = sysImpl.getAllSubcomponents();
            for (Subcomponent sub : subcomponents) {
                if (sub.getName().equals(comp)) {
                    return sysImpl;
                }
            }
        }
        return null;
    }

    private static org.osate.aadl2.SystemType getSystemTypeByName(String name) {
        for (org.osate.aadl2.SystemType sysType : sysTypes) {
            if (name.equals(sysType.getName())) {
                return sysType;
            }
        }
        return null;
    }

    private static org.osate.aadl2.SystemType getSystemType(Subcomponent comp) {
        for (org.osate.aadl2.SystemType sysType : sysTypes) {
            if (comp.getComponentType().getName().equals(sysType.getName())) {
                return sysType;
            }
        }
        return null;
    }

    private static org.osate.aadl2.Connection getConnection(Subcomponent comp, String name) {
        List<Feature> features = comp.getAllFeatures();
        for (Feature feature : features) {
            if (feature instanceof org.osate.aadl2.Connection) {
                org.osate.aadl2.Connection conn = (org.osate.aadl2.Connection) feature;
                if (conn.getName().equals(name)) {
                    return conn;
                }
            }
        }
        return null;
    }

    private static boolean hasConnection(Subcomponent comp, String name) {
        List<Feature> features = comp.getAllFeatures();
        for (Feature feature : features) {
            if (feature instanceof org.osate.aadl2.Connection) {
                org.osate.aadl2.Connection conn = (org.osate.aadl2.Connection) feature;
                if (conn.getName().equals(name)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static Subcomponent getSubcomponentByName(String name) {
        for (Subcomponent comp : subComps) {
            if (comp.getName().equals(name)) {
                return comp;
            }
        }
        return null;
    }

    private static Subcomponent getSubcomponentByConnection(String name) {
        for (Subcomponent comp : subComps) {
            if (hasConnection(comp, name)) {
                return comp;
            }
        }
        return null;
    }

    // modifies the existing aadl file with some actions
    private static void modifyAadlDocument(
            IProject project, String fileName, BiConsumer<String, XtextResource> modifier) {
        Injector injector =
                Aadl2Activator.getInstance()
                        .getInjector(Aadl2Activator.ORG_OSATE_XTEXT_AADL2_AADL2);
        XtextDocumentProvider provider = injector.getInstance(XtextDocumentProvider.class);

        try {
            FileEditorInput file = new FileEditorInput(project.getFile(new Path(fileName)));

            provider.connect(file);
            IDocument document = provider.getDocument(file);
            if (document instanceof XtextDocument) {
                XtextDocument xtextDocument = (XtextDocument) document;

                xtextDocument.modify(
                        resource -> {
                            modifier.accept(fileName, resource);
                            return null;
                        });
            }
            provider.saveDocument(null, file, document, true);
            // don't leak the document
            provider.disconnect(file);
        } catch (CoreException e) {
            e.printStackTrace();
        }
    }

    public static List<String> removeDuplicates(List<String> list) {
        List<String> finalList = new ArrayList<>();
        for (String entry : list) {
            if (!finalList.contains(entry)) {
                finalList.add(entry);
            }
        }
        return finalList;
    }

    // converts the AADL model to create a map between component and subcomponents
    private Map<String, List<String>> readFLCmapping(com.microsoft.z3.Model model) {
        Map<String, List<String>> componentMap = new HashMap<String, List<String>>();
        Map<String, List<String>> res = new HashMap<String, List<String>>();

        for (FuncDecl<?> func : model.getFuncDecls()) {
            // handle location related constraints (e.g., fixed location)
            if (func.getName().toString().contains("_to_")) {
                String domainType = func.getName().toString().split("_to_")[0];
                String rangeType = func.getName().toString().split("_to_")[1];
                Map<String, List<String>> temp =
                        Z3ModelReader.readFunc_FLCmapping(model, domainType, rangeType);

                for (String key : temp.keySet()) {
                    if (res.get(key) != null) {
                        List<String> prevElms = res.get(key);
                        List<String> newElms = temp.get(key);
                        prevElms.addAll(newElms);
                    } else {
                        List<String> newElms = temp.get(key);
                        res.put(key, newElms);
                    }
                }
            }
        }

        return res;
    }

    private static Pair<String, String> getBoundaryPorts(String comp, List<String> flowSegments) {
        boolean inFeature = false;
        String in = null;
        String out = null;
        for (String segment : flowSegments) {
            if (segment.contains(comp) && inFeature == false) {
                inFeature = true;
                in = segment.split("\\.")[1];
                continue;
            }
            if (segment.contains(comp) && inFeature == true) {
                out = segment.split("\\.")[1];
                return new Pair<String, String>(in, out);
            }
        }
        return null;
    }

    private static String getFlowName(String flowName, Subcomponent comp) {
        List<String> flowSegments = removeDuplicates(vlflowconMap.get(flowName));
        if (isCCRSource(comp, flowName) && Odm2Z3.vlStartsFromGPM.get(flowName) == true) {
            return flowName + "_ccrsource_" + comp.getName();
        }
        if (isCCRSink(comp, flowName) && Odm2Z3.vlStartsFromGPM.get(flowName) == false) {
            return flowName + "_ccrsink_" + comp.getName();
        }

        if (!isCCRSource(comp, flowName) && !isCCRSource(comp, flowName)) {
            // check if it is a a simple flow path or an e2e flow
            for (int i = 0; i < flowSegments.size(); i++) {
                String segment = flowSegments.get(i);
                if (segment.contains(comp.getName())) {
                    String segmentNext = flowSegments.get(i + 1);
                    if (segmentNext != null && segmentNext.contains(comp.getName())) {
                        // return default flow name
                        return flowName + "_" + comp.getName();
                    }
                }
            }
        }

        // we have an e2e flow
        return flowName + "_ccre2e_" + comp.getName();
    }

    private static boolean presentInFlow(String comp, List<String> flowSegments) {
        for (String segment : flowSegments) {
            if (segment.contains(comp)) {
                return true;
            }
        }
        return false;
    }

    private static boolean isCCRSource(Subcomponent comp, String flowName) {
        if (comp == null) {
            return false;
        }
        List<String> flowSegments = removeDuplicates(vlflowconMap.get(flowName));
        // get the corresponding sysImpl
        org.osate.aadl2.SystemImplementation sysImpl = null;
        for (org.osate.aadl2.SystemImplementation impl : sysImpls) {
            if (impl.getName().contains(comp.getName())) {
                sysImpl = impl;
                break;
            }
        }
        if (sysImpl == null) {
            return false;
        }

        for (int i = 0; i < flowSegments.size(); i++) {
            String segment = flowSegments.get(i);
            if (segment.contains("CCR")) {
                if (segment.contains(comp.getName())) {
                    int index = i;
                    for (int j = 0; j < index; j++) {
                        // check if all the prefix elements are contained within CCR
                        // only then we have a flow source
                        String prefixSegment = flowSegments.get(j);
                        if (prefixSegment.contains(".")) {
                            String subComp = prefixSegment.split("\\.")[0];
                            boolean bSubcompPresent = false;
                            for (Subcomponent sub : sysImpl.getAllSubcomponents()) {
                                if (sub.getName().equals(subComp)) {
                                    bSubcompPresent = true;
                                    break;
                                }
                            }

                            if (bSubcompPresent == false) {
                                return false;
                            }

                        } else {
                            // a connection
                            boolean bConnectionPresent = false;
                            for (Connection con : sysImpl.getAllConnections()) {
                                if (con.getName().equals(prefixSegment)) {
                                    bConnectionPresent = true;
                                    break;
                                }
                            }
                            if (bConnectionPresent == false) {
                                return false;
                            }
                        }
                    }
                    // entire prefix is contained within subcomponent, it is indeed a flow source
                    ccrSource.put(flowName, new Pair(comp.getName(), true));
                    return true;
                } else {
                    return false;
                }
            }
        }
        return false;
    }

    private static boolean isCCRSink(Subcomponent comp, String flowName) {
        if (comp == null) {
            return false;
        }
        List<String> flowSegments = removeDuplicates(vlflowconMap.get(flowName));
        // get the corresponding sysImpl
        org.osate.aadl2.SystemImplementation sysImpl = null;
        for (org.osate.aadl2.SystemImplementation impl : sysImpls) {
            if (impl.getName().contains(comp.getName())) {
                sysImpl = impl;
                break;
            }
        }
        if (sysImpl == null) {
            return false;
        }

        for (int i = flowSegments.size() - 1; i >= 0; i--) {
            String segment = flowSegments.get(i);
            if (segment.contains("CCR")) {
                if (segment.contains(comp.getName())) {
                    int index = i;
                    for (int j = flowSegments.size() - 1; j > index; j--) {
                        // check if all the suffix elements are contained within CCR
                        // only then we have a flow sink
                        String prefixSegment = flowSegments.get(j);
                        if (prefixSegment.contains(".")) {
                            String subComp = prefixSegment.split("\\.")[0];
                            boolean bSubcompPresent = false;
                            for (Subcomponent sub : sysImpl.getAllSubcomponents()) {
                                if (sub.getName().equals(subComp)) {
                                    bSubcompPresent = true;
                                    break;
                                }
                            }

                            if (bSubcompPresent == false) {
                                return false;
                            }

                        } else {
                            // a connection
                            boolean bConnectionPresent = false;
                            for (Connection con : sysImpl.getAllConnections()) {
                                if (con.getName().equals(prefixSegment)) {
                                    bConnectionPresent = true;
                                    break;
                                }
                            }
                            if (bConnectionPresent == false) {
                                return false;
                            }
                        }
                    }
                    // entire suffix is contained within subcomponent, it is indeed a flow sink
                    ccrSink.put(flowName, new Pair(comp.getName(), true));
                    return true;
                } else {
                    return false;
                }
            }
        }
        return false;
    }

    private static String getCCRBoundary(boolean bFromGPM, List<String> flowSegments) {
        if (bFromGPM) {
            for (String segment : flowSegments) {
                if (segment.startsWith("CCR") && segment.contains(".")) {
                    return segment.split("\\.")[1];
                }
            }
        } else {
            int i = flowSegments.size() - 1;
            while (i > 0) {
                String segment = flowSegments.get(i);
                if (segment.startsWith("CCR") && segment.contains(".")) {
                    return segment.split("\\.")[1];
                }
                i--;
            }
        }
        return "";
    }

    private static String getCCRFlowPathPort(boolean bFromGPM, List<String> flowSegments) {
        if (bFromGPM) {
            for (int i = 0; i < flowSegments.size(); i++) {
                String segment = flowSegments.get(i);
                if (segment.startsWith("CCR") && segment.contains(".")) {
                    String ccrComp1 = segment.split("\\.")[0];
                    String ccrPort1 = segment.split("\\.")[1];
                    if (i + 1 < flowSegments.size()) {
                        String segment2 = flowSegments.get(i + 1);
                        if (segment2.startsWith("CCR") && segment2.contains(".")) {
                            String ccrComp2 = segment2.split("\\.")[0];
                            String ccrPort2 = segment2.split("\\.")[1];
                            if (ccrComp1.equals(ccrComp2) && !ccrPort1.equals(ccrPort2)) {
                                return ccrPort2;
                            }
                        }
                    }
                }
            }
        } else {
            for (int i = flowSegments.size() - 1; i >= 0; i--) {
                String segment = flowSegments.get(i);
                if (segment.startsWith("CCR") && segment.contains(".")) {
                    String ccrComp1 = segment.split("\\.")[0];
                    String ccrPort1 = segment.split("\\.")[1];
                    if (i - 1 >= 0) {
                        String segment2 = flowSegments.get(i - 1);
                        if (segment2.startsWith("CCR") && segment2.contains(".")) {
                            String ccrComp2 = segment2.split("\\.")[0];
                            String ccrPort2 = segment2.split("\\.")[1];
                            if (ccrComp1.equals(ccrComp2) && !ccrPort1.equals(ccrPort2)) {
                                return ccrPort2;
                            }
                        }
                    }
                }
            }
        }

        return null;
    }

    private static boolean isFlowSource(ArrayList<String> flow, String component) {
        return false;
    }

    // returns the correct AADL filename from odm file
    String getCorretAadlFileNameFromODM(String odmFileName) {
        String aadlFileName = "";
        try {
            File odmFile = new File(odmFileName);
            Scanner myReader = new Scanner(odmFile);
            while (myReader.hasNextLine()) {
                String data = myReader.nextLine();
                if (data.contains("package=")) {
                    String[] splitData = data.split(" ");
                    for (String word : splitData) {
                        if (word.startsWith("package=")) {
                            Pattern pattern = Pattern.compile("package=\"(\\S+)\"");
                            Matcher match = pattern.matcher(word);
                            if (match.find()) {
                                aadlFileName = match.group(1) + ".aadl";
                                myReader.close();
                                return aadlFileName;
                            }
                        }
                    }
                }
            }

            myReader.close();
        } catch (Exception e) {
            System.err.println("Error: failed to read odm.xml file");
            e.printStackTrace();
        }

        return aadlFileName;
    }

    int getIndexOfLookupElement(String elem, List<Resource> res) {
        int index = 0;
        for (Resource r : res) {
            if (r.getURI().toFileString().contains(elem)) {
                return index;
            }

            index++;
        }

        return index;
    }

    private List<String> addBaseSystemImpl(String name) {
        List<String> res = new ArrayList<String>();
        res.add("system implementation " + name);
        res.add("end " + name + ";");
        return res;
    }

    // removes the AADL implementations which are redundant
    private void removeRedundantAadlImpl(String filename, String implName, String packageName) {
        try {
            BufferedReader file = new BufferedReader(new FileReader(filename));
            List<String> buffer = new ArrayList();
            String line;

            while ((line = file.readLine()) != null) {
                if (line.strip().matches("system\\s+implementation\\s+" + implName)) {
                    break;
                } else {
                    buffer.add(line);
                }
            }

            while (!file.readLine().strip().matches("end\\s+" + implName + "\\S+")) {
                continue;
            }

            while ((line = file.readLine()) != null) {
                buffer.add(line);
            }

            file.close();

            buffer.remove(0);
            buffer.add(0, "package " + packageName + "_synthesized");
            buffer.remove(buffer.size() - 1);
            buffer.add("end " + packageName + "_synthesized;");

            FileOutputStream fileOut = new FileOutputStream(filename);
            for (String inp : buffer) {
                fileOut.write(inp.getBytes());
                fileOut.write("\n".getBytes());
            }

            fileOut.close();
        } catch (Exception e) {
            System.err.println("Problem reading file.");
        }
    }

    // reads the AADL file to create in-memory data structure
    private List<EObject> aadlFile2Object(String filename) {
        final Injector injector = new Aadl2StandaloneSetup().createInjectorAndDoEMFRegistration();
        final XtextResourceSet rs = injector.getInstance(XtextResourceSet.class);
        List<EObject> objects = new ArrayList<>();
        final Resource resource = rs.getResource(URI.createFileURI(filename), true);

        // Load the resource
        try {
            resource.load(null);
        } catch (final IOException e) {
            System.err.println("ERROR LOADING RESOURCE: " + e.getMessage());
        }

        // Load all objects from resource
        resource.getAllContents().forEachRemaining(objects::add);
        return objects;
    }

    private boolean isCCRType(SystemType sysType) {
        for (PropertyAssociation pa : sysType.getAllPropertyAssociations()) {
            if (pa.getProperty().getName().equals("componentType")) {
                PropertyExpression pexp = pa.getProperty().getDefaultValue();
                if (pexp instanceof NamedValueImpl) {
                    AbstractNamedValue value = ((NamedValueImpl) pexp).getNamedValue();
                    if (value instanceof EnumerationLiteralImpl) {
                        String componentyType = ((EnumerationLiteralImpl) value).getFullName();
                        if (componentyType.equals("Common_Compute_Resource")) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }
}
