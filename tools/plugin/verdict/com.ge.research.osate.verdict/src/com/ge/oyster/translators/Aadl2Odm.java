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

import com.ge.oyster.odm.OdmTranslator;
import com.ge.research.osate.oyster.dsl.OysterUtils;
import com.ge.research.osate.oyster.dsl.oyster.CLCConstraint;
import com.ge.research.osate.oyster.dsl.oyster.Constraint;
import com.ge.research.osate.oyster.dsl.oyster.Constraints;
import com.ge.research.osate.oyster.dsl.oyster.FLCConstraint;
import com.ge.research.osate.oyster.dsl.oyster.Oyster;
import com.ge.research.osate.oyster.dsl.oyster.PortConnectionConstraint;
import com.ge.research.osate.oyster.dsl.oyster.SCConstraint;
import com.ge.research.osate.oyster.dsl.oyster.Statement;
import com.ge.research.osate.oyster.dsl.oyster.Statements;
import com.ge.research.osate.oyster.dsl.oyster.UCConstraint;
import com.ge.research.osate.oyster.dsl.oyster.VLConstraint;
import com.google.inject.Injector;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.xml.namespace.QName;
import org.apache.commons.lang3.tuple.ImmutablePair;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.plugin.EcorePlugin;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;
import org.osate.aadl2.AnnexSubclause;
import org.osate.aadl2.BooleanLiteral;
import org.osate.aadl2.IntegerLiteral;
import org.osate.aadl2.ModalPropertyValue;
import org.osate.aadl2.PropertyAssociation;
import org.osate.aadl2.PropertyExpression;
import org.osate.aadl2.RealLiteral;
import org.osate.aadl2.StringLiteral;
import org.osate.aadl2.Subcomponent;
import org.osate.aadl2.SystemImplementation;
import org.osate.aadl2.SystemType;
import org.osate.aadl2.impl.BooleanLiteralImpl;
import org.osate.aadl2.impl.EnumerationLiteralImpl;
import org.osate.aadl2.impl.NamedValueImpl;
import org.osate.pluginsupport.PluginSupportUtil;
import org.osate.xtext.aadl2.Aadl2StandaloneSetup;
import oyster.odm.odm_data.Attribute;
import oyster.odm.odm_model.ArOpList;
import oyster.odm.odm_model.ComponentImpl;
import oyster.odm.odm_model.ComponentInstance;
import oyster.odm.odm_model.ComponentType;
import oyster.odm.odm_model.EntityList;
import oyster.odm.odm_model.Model;

public class Aadl2Odm {

    // this function is the entry point for AADL to ODM translation. It
    // pre-processes AADL files
    // to create in-memory objects of the AADL components. Then, translates the AADL
    // objects to
    // an intermediate data structure ODM (Oyster Data Model).
    public ImmutablePair<oyster.odm.odm_model.Model, List<EObject>> execute(File inputDir) {
        Model odmModel = new Model();

        // reads the AADL files to create AADL objects
        List<EObject> objectsAADL = preprocessAadlFiles(inputDir);

        odmModel.setName(inputDir.getName());

        // translates AADL objects to ODM objects
        odmModel = populateODMFromAADLObjects(objectsAADL, odmModel);
        OdmTranslator.marshalToXml(odmModel, new File(inputDir + "/odm.xml"));

        ImmutablePair<oyster.odm.odm_model.Model, List<EObject>> res =
                new ImmutablePair<>(odmModel, objectsAADL);
        return res;
    }

    // generates ODM data by reading the AADL objects
    public Model populateODMFromAADLObjects(List<EObject> allObjects, Model odmModel) {
        List<SystemType> sysTypes = new ArrayList<>();
        List<SystemImplementation> sysImpls = new ArrayList<>();
        Map<String, ComponentType> qnameToCompType = new HashMap<>();
        Map<String, ComponentImpl> qnameToCompImpl = new HashMap<>();

        // extracting data from the AADLObject
        for (EObject obj : allObjects) {
            if (obj instanceof SystemType) {
                sysTypes.add((SystemType) obj);
            } else if (obj instanceof SystemImplementation) {
                sysImpls.add((SystemImplementation) obj);
            }
        }

        // enumerate over system types to create ODM component types
        for (SystemType sysType : sysTypes) {
            ComponentType odmCompType = new ComponentType();
            String qualifiedName = sysType.getQualifiedName();
            String nameSpace = sysType.getNamespace().getName();
            int index = nameSpace.lastIndexOf('_');
            String packageName = nameSpace.substring(0, index);
            String visibility = nameSpace.substring(index + 1);

            if (packageName == null || packageName.equals("")) {
                // The name space is expected to be in the form of "package_visibility"
                throw new RuntimeException(
                        "Unexpected package and visibility declaration in AADL!");
            }

            if (visibility == null || visibility.equals("")) {
                // The name space is expected to be in the form of "package_visibility"
                throw new RuntimeException(
                        "Unexpected package and visibility declaration in AADL!");
            }

            odmCompType.setPackage(packageName);
            odmCompType.setId(qualifiedName);
            odmCompType.setName(sysType.getName());

            // assosciate system type properties to ODM component type
            for (PropertyAssociation propAssoc : sysType.getOwnedPropertyAssociations()) {
                String propName = propAssoc.getProperty().getName();
                EList<ModalPropertyValue> propVals = propAssoc.getOwnedValues();

                if (propVals.size() == 0 || propVals.size() > 1) {
                    throw new RuntimeException(
                            "Unexpected number for values for the property of " + propName);
                }
                PropertyExpression propVal = propVals.get(0).getOwnedValue();
                Attribute attribute = new Attribute();
                attribute.setName(propName);
                translatePropVal(propVal, attribute);
                odmCompType.getAttribute().add(attribute);
            }

            qnameToCompType.put(qualifiedName, odmCompType);
            odmModel.getComponentType().add(odmCompType);
        }

        // enumerate over system implementations to create ODM component implementations
        for (SystemImplementation sysImpl : sysImpls) {
            String nameSpace = sysImpl.getNamespace().getName();
            int index = nameSpace.lastIndexOf('_');
            String packageName = nameSpace.substring(0, index);
            String visibility = nameSpace.substring(index + 1);

            if (packageName == null || packageName.equals("")) {
                // The name space is expected to be in the form of "package_visibility"
                throw new RuntimeException(
                        "Unexpected package and visibility declaration in AADL!");
            }

            if (visibility == null || visibility.equals("")) {
                // The name space is expected to be in the form of "package_visibility"
                throw new RuntimeException(
                        "Unexpected package and visibility declaration in AADL!");
            }

            String qualifiedName = sysImpl.getQualifiedName();
            ComponentImpl odmCompImpl = new ComponentImpl();

            odmCompImpl.setName(sysImpl.getName());
            odmCompImpl.setId(qualifiedName);
            odmCompImpl.setPackage(packageName);
            odmCompImpl.setType(qnameToCompType.get(sysImpl.getType().getQualifiedName()));

            // assosciate system implementation properties to ODM component implementations
            for (PropertyAssociation propAssoc : sysImpl.getOwnedPropertyAssociations()) {
                String propName = propAssoc.getProperty().getName();
                EList<ModalPropertyValue> propVals = propAssoc.getOwnedValues();

                if (propVals.size() == 0 || propVals.size() > 1) {
                    throw new RuntimeException(
                            "Unexpected number for values for the property of " + propName);
                }
                PropertyExpression propVal = propVals.get(0).getOwnedValue();
                Attribute attribute = new Attribute();
                attribute.setName(propName);
                translatePropVal(propVal, attribute);
                odmCompImpl.getAttribute().add(attribute);
            }

            qnameToCompImpl.put(qualifiedName, odmCompImpl);
            odmModel.getComponentImpl().add(odmCompImpl);
        }

        // Populate subcomponents and oyster annex
        for (SystemImplementation sysImpl : sysImpls) {
            ComponentImpl odmCompImpl = qnameToCompImpl.get(sysImpl.getQualifiedName());
            Map<String, ComponentInstance> nameToCompInst = new HashMap<>();

            // Populate subcomponents to ODM component
            for (Subcomponent subcomp : sysImpl.getAllSubcomponents()) {
                ComponentInstance odmCompInst = new ComponentInstance();

                odmCompInst.setId(subcomp.getQualifiedName());
                odmCompInst.setName(subcomp.getName());

                if (subcomp.getComponentType() != null) {
                    String subcompTypeQName = subcomp.getComponentType().getQualifiedName();

                    if (qnameToCompType.containsKey(subcompTypeQName)) {
                        odmCompInst.setType(qnameToCompType.get(subcompTypeQName));
                    } else {
                        throw new RuntimeException(
                                "Unexpected: the subcomponent "
                                        + subcomp.getName()
                                        + " type does not exist!");
                    }
                }
                if (subcomp.getComponentImplementation() != null) {
                    String subcompImplQName =
                            subcomp.getComponentImplementation().getQualifiedName();
                    if (qnameToCompImpl.containsKey(subcompImplQName)) {
                        odmCompInst.setImplementation(qnameToCompImpl.get(subcompImplQName));
                    } else {
                        throw new RuntimeException(
                                "Unexpected: the subcomponent "
                                        + subcomp.getName()
                                        + " implementation does not exist!");
                    }
                }

                // associate properties of subcomponents in ODM object
                for (PropertyAssociation propAssoc : subcomp.getOwnedPropertyAssociations()) {
                    String propName = propAssoc.getProperty().getName();
                    EList<ModalPropertyValue> propVals = propAssoc.getOwnedValues();

                    if (propVals.size() == 0 || propVals.size() > 1) {
                        throw new RuntimeException(
                                "Unexpected number for values for the property of " + propName);
                    }

                    PropertyExpression propVal = propVals.get(0).getOwnedValue();
                    Attribute attribute = new Attribute();
                    attribute.setName(propName);
                    translatePropVal(propVal, attribute);
                    odmCompInst.getAttribute().add(attribute);
                }

                odmCompImpl.getSubcomponents().add(odmCompInst);
                nameToCompInst.put(subcomp.getName(), odmCompInst);
            }

            // Populate oyster annex to ODM data
            for (AnnexSubclause annex : sysImpl.getOwnedAnnexSubclauses()) {
                if (annex.getName().equalsIgnoreCase("oyster")) {
                    Oyster oysterAnnex = OysterUtils.getOyster(annex);
                    Statements statments = oysterAnnex.getElement();

                    for (Statement statement : statments.getElements()) {

                        if (statement instanceof Constraint) {
                            Constraint constraint = (Constraint) statement;
                            populateODMWithConstraint(
                                    nameToCompInst, odmCompImpl, constraint, qnameToCompType);
                        }

                        if (statement instanceof Constraints) {

                            for (Constraint constraint :
                                    ((Constraints) statement).getConstraints()) {
                                populateODMWithConstraint(
                                        nameToCompInst, odmCompImpl, constraint, qnameToCompType);
                            }
                        }
                    }
                }
            }
        }

        return odmModel;
    }

    // the functions converts each type of Oyster constraints to ODM
    private void populateODMWithConstraint(
            Map<String, ComponentInstance> nameToCompInst,
            ComponentImpl odmCompImpl,
            Constraint constraint,
            Map<String, ComponentType> qnameToCompType) {

        if (constraint.getFlcConstraint() != null) { // fixed location constraint
            oyster.odm.odm_model.Constraint odmConstraint = new oyster.odm.odm_model.Constraint();
            oyster.odm.odm_model.Specification odmSpec = new oyster.odm.odm_model.Specification();
            EntityList srcEntityList = new EntityList();
            EntityList destEntityList = new EntityList();

            FLCConstraint flc = constraint.getFlcConstraint();
            String item = flc.getItem();
            String loc = flc.getLocation();

            if (nameToCompInst.containsKey(item)) {
                srcEntityList.getEntities().add(nameToCompInst.get(item));
                odmSpec.setSrcEntities(srcEntityList);
            } else {
                throw new RuntimeException(
                        "Unexpected: cannot find source entity in subcomponents!");
            }

            if (nameToCompInst.containsKey(loc)) {
                destEntityList.getEntities().add(nameToCompInst.get(loc));
                odmSpec.setDestEntities(destEntityList);
            } else {
                throw new RuntimeException(
                        "Unexpected: cannot find destination entity in subcomponents!");
            }

            odmSpec.setConstraintName(flc.getConName());
            odmConstraint.setSpecification(odmSpec);
            odmConstraint.setType(oyster.odm.odm_model.ConstraintType.FIXED_LOCATION_CONSTRAINT);
            odmCompImpl.getOysterConstraint().add(odmConstraint);

        } else if (constraint.getScConstraint() != null) { // separation constraint
            oyster.odm.odm_model.Constraint odmConstraint = new oyster.odm.odm_model.Constraint();
            oyster.odm.odm_model.Specification odmSpec = new oyster.odm.odm_model.Specification();
            EntityList srcEntityList = new EntityList();
            SCConstraint sc = constraint.getScConstraint();

            for (String item : sc.getItems().replaceAll("\\s", "").split(",")) {
                if (nameToCompInst.containsKey(item)) {
                    srcEntityList.getEntities().add(nameToCompInst.get(item));
                    odmSpec.setSrcEntities(srcEntityList);
                } else {
                    throw new RuntimeException(
                            "Unexpected: cannot find source entity in subcomponents!");
                }
            }

            odmSpec.setConstraintName(sc.getConName());
            odmSpec.setToComponent(sc.getLocationType());
            odmConstraint.setSpecification(odmSpec);
            odmConstraint.setType(oyster.odm.odm_model.ConstraintType.SEPARATION_CONSTRAINT);
            odmCompImpl.getOysterConstraint().add(odmConstraint);

        } else if (constraint.getClcConstraint() != null) { // co-location constraint
            oyster.odm.odm_model.Constraint odmConstraint = new oyster.odm.odm_model.Constraint();
            oyster.odm.odm_model.Specification odmSpec = new oyster.odm.odm_model.Specification();
            EntityList srcEntityList = new EntityList();

            CLCConstraint clc = constraint.getClcConstraint();
            String items1 = clc.getItems1();
            String items2 = clc.getItems2();

            for (String item : items1.replaceAll("\\s", "").split(",")) {
                if (nameToCompInst.containsKey(item)) {
                    srcEntityList.getEntities().add(nameToCompInst.get(item));
                    odmSpec.setSrcEntities(srcEntityList);
                } else {
                    throw new RuntimeException(
                            "Unexpected: cannot find source entity in subcomponents!");
                }
            }

            for (String item : items2.replaceAll("\\s", "").split(",")) {
                if (nameToCompInst.containsKey(item)) {
                    srcEntityList.getEntities().add(nameToCompInst.get(item));
                    odmSpec.setSrcEntities(srcEntityList);
                } else {
                    throw new RuntimeException(
                            "Unexpected: cannot find source entity in subcomponents!");
                }
            }

            odmSpec.setConstraintName(clc.getConName());
            odmSpec.setToComponent(clc.getLocationType());
            odmConstraint.setSpecification(odmSpec);
            odmConstraint.setType(oyster.odm.odm_model.ConstraintType.CO_LOCATION_CONSTRAINT);
            odmCompImpl.getOysterConstraint().add(odmConstraint);

        } else if (constraint.getPortConConstraint() != null) { // port-connection constraint
            PortConnectionConstraint pcc = constraint.getPortConConstraint();

            String src = pcc.getSrc();
            String srcPort = pcc.getSrcPort();
            String dest = pcc.getDest();
            String destPort = pcc.getDestPort();
            String bandwidth = pcc.getBandwidth();

            oyster.odm.odm_model.Connection packConn = new oyster.odm.odm_model.Connection();
            packConn.setConnectionKind(oyster.odm.odm_model.ConnectionKind.PORT);

            // ports are assumed bi-directional
            oyster.odm.odm_model.PortType srcPortTypeName = oyster.odm.odm_model.PortType.IN_OUT;
            oyster.odm.odm_model.PortType destPortTypeName = oyster.odm.odm_model.PortType.IN_OUT;

            oyster.odm.odm_data.DataType srcPortDtype = new oyster.odm.odm_data.DataType();
            srcPortDtype.setPlainType(oyster.odm.odm_data.PlainType.INT); // TODO: make generic

            oyster.odm.odm_data.DataType destPortDtype = new oyster.odm.odm_data.DataType();
            destPortDtype.setPlainType(oyster.odm.odm_data.PlainType.INT); // TODO: make generi

            // to pack source
            oyster.odm.odm_model.ConnectionEnd packSrcEnd =
                    new oyster.odm.odm_model.ConnectionEnd();
            oyster.odm.odm_model.Port packSrcEndPort =
                    createOdmConnectionPort(
                            srcPort, srcPortTypeName, srcPortDtype, src + "." + srcPort);

            // to pack destination
            oyster.odm.odm_model.ConnectionEnd packDestEnd =
                    new oyster.odm.odm_model.ConnectionEnd();
            oyster.odm.odm_model.Port packDestEndPort =
                    createOdmConnectionPort(
                            destPort, destPortTypeName, destPortDtype, dest + "." + destPort);

            // setting name
            packConn.setName(pcc.getConName());

            packSrcEnd.setComponentPort(packSrcEndPort);
            packDestEnd.setComponentPort(packDestEndPort);

            packConn.setSource(packSrcEnd);
            packConn.setDestination(packDestEnd);
            packConn.setDirection(oyster.odm.odm_model.Direction.BIDIRECTIONAL);

            // assigns user given bandwidth for the port-to-port physical link
            if (bandwidth != null) {
                packConn.setBandwidth(Integer.parseInt(bandwidth));
            } else {
                packConn.setBandwidth(0);
            }

            odmCompImpl.getConnections().add(packConn);
        } else if (constraint.getVlConstraint() != null) { // virtual-link constraint
            VLConstraint sc = constraint.getVlConstraint();
            String[] dests = sc.getDest().split(",");
            String[] msgGroups = sc.getMsgs().split("#");

            // for each message in a set of message (msgGroup), for each destination entity
            // entity, we create individual flow
            if (dests.length == msgGroups.length) {
                for (int i = 0; i < dests.length; i++) {
                    String[] msgs =
                            msgGroups[i]
                                    .trim()
                                    .substring(1, msgGroups[i].trim().length() - 1)
                                    .split(",");
                    int j = 0;
                    for (String msg : msgs) {
                        oyster.odm.odm_model.Constraint odmConstraint =
                                new oyster.odm.odm_model.Constraint();
                        oyster.odm.odm_model.Specification odmSpec =
                                new oyster.odm.odm_model.Specification();
                        odmSpec.setConstraintName(sc.getConName() + ".flow" + i + "@m" + j);
                        odmSpec.setFromComponent(sc.getSrc());
                        odmSpec.setToComponent(dests[i].trim());
                        odmSpec.setMsgSize(Integer.parseInt(msg.split("@")[0].trim()));
                        odmSpec.setRefreshPeriod(Integer.parseInt(msg.split("@")[1].trim()));
                        odmConstraint.setSpecification(odmSpec);
                        odmConstraint.setType(
                                oyster.odm.odm_model.ConstraintType.VIRTUAL_LINK_CONSTRAINT);
                        odmCompImpl.getOysterConstraint().add(odmConstraint);
                        j++;
                    }
                }
            }
        } else if (constraint.getUcConstraint() != null) { // utilization constraint
            oyster.odm.odm_model.Constraint odmConstraint = new oyster.odm.odm_model.Constraint();
            oyster.odm.odm_model.Specification odmSpec = new oyster.odm.odm_model.Specification();
            EntityList srcEntityList = new EntityList();
            EntityList destEntityList = new EntityList();

            UCConstraint uc = constraint.getUcConstraint();
            String resType = uc.getResType();
            String src = uc.getSrc();
            String sink = uc.getSink();
            List<String> otherSinks;

            if (uc.getOtherSinks() != null) {
                otherSinks = uc.getOtherSinks().getSinks();
            } else {
                otherSinks = new ArrayList<String>();
            }

            otherSinks.add(0, sink);

            if (nameToCompInst.containsKey(src)) {
                srcEntityList.getEntities().add(nameToCompInst.get(src));
                odmSpec.setSrcEntities(srcEntityList);
            } else {
                throw new RuntimeException(
                        "Unexpected: cannot find source entity in subcomponents!");
            }

            for (String item : otherSinks) {
                if (nameToCompInst.containsKey(item)) {
                    destEntityList.getEntities().add(nameToCompInst.get(item));
                    odmSpec.setDestEntities(destEntityList);
                } else {
                    throw new RuntimeException(
                            "Unexpected: cannot find destination entity in subcomponents!");
                }
            }

            // add comparison operator and arithmetic operators in ODM model
            String compOp = uc.getCompOp();
            ArOpList arOpList = new ArOpList();
            List<String> arrOps;

            if (uc.getOtherSinks() != null) {
                arrOps = uc.getOtherSinks().getArOps();
            } else {
                arrOps = new ArrayList<String>();
            }

            if (compOp.equals("==")) {
                odmSpec.setSrcEntitiesCompOp(oyster.odm.odm_model.ComparisonOperator.EQ);
            } else if (compOp.equals("!=")) {
                odmSpec.setSrcEntitiesCompOp(oyster.odm.odm_model.ComparisonOperator.NEQ);
            } else if (compOp.equals(">")) {
                odmSpec.setSrcEntitiesCompOp(oyster.odm.odm_model.ComparisonOperator.GT);
            } else if (compOp.equals("<")) {
                odmSpec.setSrcEntitiesCompOp(oyster.odm.odm_model.ComparisonOperator.LT);
            } else if (compOp.equals(">=")) {
                odmSpec.setSrcEntitiesCompOp(oyster.odm.odm_model.ComparisonOperator.GTE);
            } else if (compOp.equals("<=")) {
                odmSpec.setSrcEntitiesCompOp(oyster.odm.odm_model.ComparisonOperator.LTE);
            }

            for (String arrOp : arrOps) {
                if (arrOp.equals("+")) {
                    arOpList.getSign().add(oyster.odm.odm_model.ArithmaticOperator.PLUS);
                } else if (arrOp.equals("-")) {
                    arOpList.getSign().add(oyster.odm.odm_model.ArithmaticOperator.MINUS);
                } else if (arrOp.equals("*")) {
                    arOpList.getSign().add(oyster.odm.odm_model.ArithmaticOperator.MUL);
                } else if (arrOp.equals("/")) {
                    arOpList.getSign().add(oyster.odm.odm_model.ArithmaticOperator.DIV);
                }
            }

            odmSpec.setConstraintName(uc.getConName());
            odmSpec.setCharacteristicProperty(resType);
            odmSpec.setDestEntitiesSigns(arOpList);
            odmConstraint.setSpecification(odmSpec);
            odmConstraint.setType(oyster.odm.odm_model.ConstraintType.UTILIZATION_CONSTRAINT);
            odmCompImpl.getOysterConstraint().add(odmConstraint);
        }
    }

    // translates property value to ODM data types
    public void translatePropVal(PropertyExpression propVal, Attribute attribute) {
        if (propVal instanceof BooleanLiteral) {
            attribute.setValue(((BooleanLiteralImpl) propVal).getValue());
            attribute.setType(new QName("Bool"));
        } else if (propVal instanceof StringLiteral) {
            attribute.setValue(((StringLiteral) propVal).getValue());
            attribute.setType(new QName("String"));
        } else if (propVal instanceof IntegerLiteral) {
            attribute.setValue(((IntegerLiteral) propVal).getValue());
            attribute.setType(new QName("Int"));
        } else if (propVal instanceof NamedValueImpl) {
            NamedValueImpl namedValue = ((NamedValueImpl) propVal);

            if (namedValue.getNamedValue() instanceof EnumerationLiteralImpl) {
                EnumerationLiteralImpl enu = ((EnumerationLiteralImpl) namedValue.getNamedValue());
                attribute.setValue(enu.getName());
                attribute.setType(new QName("Enum"));
            } else {
                throw new RuntimeException(
                        "Unsupported property value for property " + attribute.getName());
            }
        } else if (propVal instanceof RealLiteral) {
            attribute.setValue(((RealLiteral) propVal).getValue());
            attribute.setType(new QName("Real"));
        } else {
            throw new RuntimeException(
                    "Unsupported property value for property " + attribute.getName());
        }
    }

    /**
     * Method to parse the AADL files in the project 1. load all AADL files in the directory and the
     * imported contributed AADL files as Resources 2. get contents from the loaded resources and
     * create/return them as list of objects NOTE: this method is different from preprocessAadlFiles
     * in Aadl2Vdm, here imported contributed AADL files are also loaded as Resources
     *
     * @param project directory
     * @return list of objects
     */
    // method that processes all aadl files in the directory and the imported
    // contributed aadl files
    public List<EObject> preprocessAadlFiles(File dir) {
        final Injector injector = new Aadl2StandaloneSetup().createInjectorAndDoEMFRegistration();
        final XtextResourceSet rs = injector.getInstance(XtextResourceSet.class);
        rs.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);

        EcorePlugin.ExtensionProcessor.process(null);
        // getting aadl imported files
        final List<URI> contributed = PluginSupportUtil.getContributedAadl();
        for (final URI uri : contributed) {
            rs.getResource(uri, true);
        }

        List<String> aadlFileNames = new ArrayList<>();
        // Obtain all AADL files contents in the project
        List<EObject> objects = new ArrayList<>();
        List<File> dirs = collectAllDirs(dir);

        for (File subdir : dirs) {
            for (File file : subdir.listFiles()) {
                if (file.getAbsolutePath().endsWith("_synthesized.aadl")) {
                    file.delete();
                } else if (file.getAbsolutePath().endsWith(".aadl")) {
                    aadlFileNames.add(file.getAbsolutePath());
                }
            }
        }

        for (int i = 0; i < aadlFileNames.size(); i++) {
            rs.getResource(URI.createFileURI(aadlFileNames.get(i)), true);
        }

        // Load the resources
        Map<String, Boolean> options = new HashMap<String, Boolean>();
        options.put(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);
        for (final Resource resource : rs.getResources()) {
            try {
                resource.load(options);
                IResourceValidator validator =
                        ((XtextResource) resource)
                                .getResourceServiceProvider()
                                .getResourceValidator();
                List<Issue> issues =
                        validator.validate(resource, CheckMode.FAST_ONLY, CancelIndicator.NullImpl);
                for (Issue issue : issues) {
                    System.out.println(issue.getMessage());
                }
            } catch (final IOException e) {
                System.err.println("ERROR LOADING RESOURCE: " + e.getMessage());
            }
        }
        for (final Resource resource : rs.getResources()) {
            resource.getAllContents().forEachRemaining(objects::add);
        }
        return objects;
    }

    /**
     * Process an event corresponding to a selection of AADL project Translate an AADL project into
     * objects
     */
    public List<EObject> preprocessAadlFilesInProject(File dir) {
        final Injector injector = new Aadl2StandaloneSetup().createInjectorAndDoEMFRegistration();
        final XtextResourceSet rs = injector.getInstance(XtextResourceSet.class);
        List<String> aadlFileNames = new ArrayList<>();

        // Set scenario name
        // scenario = dir.getName();

        // Obtain all AADL files contents in the project
        List<EObject> objects = new ArrayList<>();

        List<File> dirs = collectAllDirs(dir);

        for (File subdir : dirs) {
            for (File file : subdir.listFiles()) {
                if (file.getAbsolutePath().endsWith(".aadl")) {
                    aadlFileNames.add(file.getAbsolutePath());
                }
            }
        }

        final Resource[] resources = new Resource[aadlFileNames.size()];
        for (int i = 0; i < aadlFileNames.size(); i++) {
            resources[i] = rs.getResource(URI.createFileURI(aadlFileNames.get(i)), true);
        }

        // Load the resources
        for (final Resource resource : resources) {
            try {
                resource.load(null);
            } catch (final IOException e) {
                System.err.println("ERROR LOADING RESOURCE: " + e.getMessage());
            }
        }

        // Load all objects from resources
        for (final Resource resource : resources) {
            resource.getAllContents().forEachRemaining(objects::add);
        }
        return objects;
    }

    /**
     * The following two functions are used to get lists of all aadl files from directories
     *
     * @param dir
     * @return
     */
    List<File> collectAllDirs(File dir) {
        List<File> allDirs = new ArrayList<File>();
        allDirs.add(dir);
        for (File file : dir.listFiles()) {
            if (file.isDirectory()) {
                allDirs.add(file);
                collectDir(file, allDirs);
            }
        }
        return allDirs;
    }

    void collectDir(File dir, List<File> allDirs) {
        for (File file : dir.listFiles()) {
            if (file.isDirectory()) {
                allDirs.add(file);
                collectDir(file, allDirs);
            }
        }
    }

    /**
     * Creates a new Odm Port object and returns Populates "name"
     *
     * @param portName
     * @return odm port
     */
    oyster.odm.odm_model.Port createOdmConnectionPort(
            String portName,
            oyster.odm.odm_model.PortType PortTypeName,
            oyster.odm.odm_data.DataType portDataType,
            String qualifiedname) {
        // fetching data type information
        oyster.odm.odm_model.Port newPort = new oyster.odm.odm_model.Port();
        newPort.setProbe(false);
        newPort.setId(qualifiedname);
        newPort.setName(portName);
        newPort.setMode(PortTypeName);
        newPort.setType(portDataType);
        return newPort;
    }
}
