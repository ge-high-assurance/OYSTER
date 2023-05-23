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
package com.ge.research.osate.oyster.dsl.validation;

import com.ge.research.osate.oyster.dsl.oyster.CLCConstraint;
import com.ge.research.osate.oyster.dsl.oyster.Constraint;
import com.ge.research.osate.oyster.dsl.oyster.Constraints;
import com.ge.research.osate.oyster.dsl.oyster.FLCConstraint;
import com.ge.research.osate.oyster.dsl.oyster.OysterPackage;
import com.ge.research.osate.oyster.dsl.oyster.PortConnectionConstraint;
import com.ge.research.osate.oyster.dsl.oyster.SCConstraint;
import com.ge.research.osate.oyster.dsl.oyster.Statement;
import com.ge.research.osate.oyster.dsl.oyster.Statements;
import com.ge.research.osate.oyster.dsl.oyster.UCConstraint;
import com.ge.research.osate.oyster.dsl.oyster.VLConstraint;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.xtext.validation.Check;
import org.eclipse.xtext.validation.CheckType;
import org.osate.aadl2.AadlPackage;
import org.osate.aadl2.PropertyAssociation;
import org.osate.aadl2.PublicPackageSection;
import org.osate.aadl2.Subcomponent;
import org.osate.aadl2.SystemImplementation;
import org.osate.aadl2.SystemSubcomponent;
import org.osate.aadl2.SystemType;

/**
 * This class contains custom validation rules.
 *
 * <p>See https://www.eclipse.org/Xtext/documentation/303_runtime_concepts.html#validation
 */
public class OysterValidator extends AbstractOysterValidator {
    private Set<String> systemIds;
    private Set<String> systemImplementationIds;
    private Map<String, String> locMap;
    private Map<String, String> compNameandType;
    private Map<String, Set<String>> subcompProperties;
    private Set<String> conNames;

    @Override
    public List<EPackage> getEPackages() {
        List<EPackage> result = new ArrayList<>(super.getEPackages());
        result.add(OysterPackage.eINSTANCE);
        result.add(EPackage.Registry.INSTANCE.getEPackage("http://aadl.info/AADL/2.0"));
        return result;
    }

    @Override
    public boolean isResponsible(Map<Object, Object> context, EObject object) {
        return (object.eClass().getEPackage() == OysterPackage.eINSTANCE)
                || object instanceof AadlPackage;
    }

    private class Ids {
        private Set<String> systemIds;
        private Set<String> systemImplementationIds;

        private Ids(Set<String> a, Set<String> b) {
            this.systemIds = a;
            this.systemImplementationIds = b;
        }

        protected Set<String> getSystemIds() {
            return systemIds;
        }

        protected Set<String> getSystemImplementationIds() {
            return systemImplementationIds;
        }
    }
    ;

    // This function returns the Set of System Types and System Implementations
    protected Ids getIds(Statements statements) {
        EObject container;
        Set<String> systemIds = new HashSet<String>();
        Set<String> systemImplementationIds = new HashSet<String>();
        compNameandType = new HashMap<String, String>();
        subcompProperties = new HashMap<String, Set<String>>();

        if (statements.getElements().size() > 0) {
            container = statements.getElements().get(0);
        } else {
            return new Ids(systemIds, systemImplementationIds);
        }

        while (container != null) {
            if (container instanceof SystemImplementation) {
                SystemImplementation si = (SystemImplementation) container;
                for (Subcomponent sc : si.getAllSubcomponents()) {
                    if (sc instanceof SystemSubcomponent) {
                        SystemSubcomponent ssc = (SystemSubcomponent) sc;
                        systemImplementationIds.add(ssc.getName());
                        compNameandType.put(
                                ssc.getName(), ssc.getSystemSubcomponentType().getName());

                        Set<String> props = new HashSet<String>();
                        if (ssc.getOwnedPropertyAssociations().size() > 0) {
                            for (PropertyAssociation item : ssc.getOwnedPropertyAssociations()) {
                                props.add(item.getProperty().getName());
                            }
                        }

                        subcompProperties.put(ssc.getName(), props);
                    }
                }
            } else if (container instanceof PublicPackageSection) {
                EList<EObject> ppsContainer = container.eContents();
                for (EObject obj : ppsContainer) {
                    if (obj instanceof SystemType) {
                        SystemType st = (SystemType) obj;
                        systemIds.add(st.getName());
                    }
                }
            }

            container = container.eContainer();
        }

        return new Ids(systemIds, systemImplementationIds);
    }

    @Check(CheckType.FAST)
    public void checkStatements(Statements statements) {
        // connectionNames = new HashSet<String>();
        systemImplementationIds = getIds(statements).getSystemImplementationIds();
        systemIds = getIds(statements).getSystemIds();
        locMap = new HashMap<String, String>();
        conNames = new HashSet<String>();
    }

    @Check(CheckType.FAST)
    public void checkStatement(Statement s) {
        if (!(s instanceof Constraints)) {
            throw new RuntimeException("Statement is not a valid constraint");
        }
    }

    public void checkConstraint(Constraint c) {

        // Check if its is an FLC
        if (c.getFlcConstraint() != null) {
            checkFLCConstraint(c.getFlcConstraint());
        }

        // Check if its a SC
        else if (c.getScConstraint() != null) {
            checkSCConstraint(c.getScConstraint());
        }

        // Check if its a CLC
        else if (c.getClcConstraint() != null) {
            checkCLCConstraint(c.getClcConstraint());
        }

        // Check if its a UC
        else if (c.getUcConstraint() != null) {
            checkUCConstraint(c.getUcConstraint());
        }

        // Check if its a port connection constraint
        else if (c.getPortConConstraint() != null) {
            checkPortConConstraint(c.getPortConConstraint());
        }

        // Check if its a VL constraint
        else if (c.getVlConstraint() != null) {
            checkVLConstraint(c.getVlConstraint());
        }
    }

    @Check(CheckType.FAST)
    public void checkFLCConstraint(FLCConstraint flc) {
        String item = flc.getItem();
        String location = flc.getLocation();

        // checks if item is already mapped to a different location
        checkLocMap(item, location);

        // checks if valid instances
        checkValidImplId(item);
        checkValidImplId(location);

        // check Constraint name if used before
        checkConName(flc.getConName());
    }

    @Check(CheckType.FAST)
    public void checkSCConstraint(SCConstraint sc) {
        String[] items = sc.getItems().replaceAll("\\s", "").split(",");
        String itemsType = sc.getItemsType();
        String locationType = sc.getLocationType();

        for (String item : items) {
            // checks if valid instances
            checkValidImplId(item);

            // checks type consistency with expected type
            typeConsistency(item, itemsType);
        }

        checkValidTypeId(itemsType);
        checkValidTypeId(locationType);

        // enforce no duplicate items
        checkDuplicates(items);

        // ensure different types
        checkNotEqualType(itemsType, locationType);

        // at least two items
        if (items.length < 2) {
            error("At least two instances are required");
        }

        // check Constraint name if used before
        checkConName(sc.getConName());
    }

    @Check(CheckType.FAST)
    public void checkCLCConstraint(CLCConstraint clc) {
        String[] items1 = clc.getItems1().replaceAll("\\s", "").split(",");
        String itemsType1 = clc.getItemsType1();
        String[] items2 = clc.getItems2().replaceAll("\\s", "").split(",");
        String itemsType2 = clc.getItemsType2();
        String locationType = clc.getLocationType();

        for (String item : items1) {
            // checks if valid instances
            checkValidImplId(item);

            // checks type consistency with expected type
            typeConsistency(item, itemsType1);
        }

        for (String item : items2) {
            // checks if valid instances
            checkValidImplId(item);

            // checks type consistency with expected type
            typeConsistency(item, itemsType2);
        }

        checkValidTypeId(itemsType1);
        checkValidTypeId(itemsType2);
        checkValidTypeId(locationType);

        // enforce no duplicate items
        checkDuplicates(items1);
        checkDuplicates(items2);

        // ensure different types
        checkNotEqualType(itemsType1, itemsType2);
        checkNotEqualType(itemsType1, locationType);
        checkNotEqualType(itemsType2, locationType);

        // check Constraint name if used before
        checkConName(clc.getConName());
    }

    @Check(CheckType.FAST)
    public void checkPortConConstraint(PortConnectionConstraint cc) {
        String src = cc.getSrc();
        String dest = cc.getDest();

        // checks if valid instances
        checkValidImplId(src);
        checkValidImplId(dest);

        if (src.equals(dest)) {
            error("Self-loop connection is not allowed");
        }

        // check Constraint name if used before
        checkConName(cc.getConName());
    }

    @Check(CheckType.FAST)
    public void checkVLConstraint(VLConstraint cc) {
        String src = cc.getSrc();
        String[] dest = cc.getDest().split(",");
        String[] msgGroups = cc.getMsgs().split("#");

        if (dest.length != msgGroups.length) {
            error("Incorrect number of message groups, expected " + dest.length);
        }

        // checks if valid instances
        checkValidImplId(src);

        for (String d : dest) {
            // checks if valid instances
            checkValidImplId(d.trim());

            if (src.equals(d.trim())) {
                error("Self-loop connection is not allowed");
            }
        }

        // check Constraint name if used before
        checkConName(cc.getConName());
    }

    @Check(CheckType.FAST)
    public void checkUCConstraint(UCConstraint uc) {
        String resType = uc.getResType();
        String srcType = uc.getSrcType();
        String src = uc.getSrc();
        String srcProp = uc.getSrcProp();
        String sinkType = uc.getSinkType();
        String sink = uc.getSink();
        String sinkProp = uc.getSinkProp();
        List<String> otherSinkTypes = uc.getOtherSinks().getSinkTypes();
        List<String> otherSinks = uc.getOtherSinks().getSinks();
        List<String> otherSinkProps = uc.getOtherSinks().getSinkProps();

        // checks if valid instances and type consistency
        checkValidImplId(src);
        checkValidImplId(sink);
        checkValidTypeId(srcType);
        checkValidTypeId(sinkType);
        typeConsistency(src, srcType);
        typeConsistency(sink, sinkType);

        for (int i = 0; i < otherSinks.size(); i++) {
            checkValidImplId(otherSinks.get(i));
            checkValidTypeId(otherSinkTypes.get(i));
            typeConsistency(otherSinks.get(i), otherSinkTypes.get(i));
        }

        // checks if resource properties are valid
        checkResPropertyValidity(src, srcProp);
        checkResPropertyValidity(sink, sinkProp);

        for (int i = 0; i < otherSinks.size(); i++) {
            checkResPropertyValidity(otherSinks.get(i), otherSinkProps.get(i));
        }

        // check Constraint name if used before
        checkConName(uc.getConName());

        // check if Utilization properties are consistent
        otherSinkProps.add(sinkProp);
        checkUCpropMapping(resType, srcProp, otherSinkProps);
    }

    // creates a one-to-one mapping of an item to a location
    protected void checkLocMap(String item, String location) {
        if (item.equals(location)) {
            error("Mapping to same component is not allowed");
        }

        if (locMap.containsKey(item)) {
            String prevLocation = locMap.get(item);

            if (!(prevLocation.equals(location))) {
                error(item + " is already mapped to " + prevLocation);
            }
        } else {
            locMap.put(item, location);
        }
    }

    // checks if constraint name is repeated
    protected void checkConName(String item) {
        if (conNames.contains(item)) {
            error("The name " + item + " is already used for another constraint");
        } else {
            conNames.add(item);
        }
    }

    // ensures impl ID is already defined
    protected void checkValidImplId(String ID) {
        if (!(systemImplementationIds.contains(ID))) {
            error(ID + " is not a defined instance");
        }
    }

    // ensures type is already defined
    protected void checkValidTypeId(String ID) {
        if (!(systemIds.contains(ID))) {
            error(ID + " is not a defined system type");
        }
    }

    // ensures two types are not equal
    protected void checkNotEqualType(String ID1, String ID2) {
        if (ID1.equals(ID2)) {
            error("Not allowed to map instances of same type");
        }
    }

    // checks if the type of an instance matches the expected type
    protected void typeConsistency(String elem, String expType) {
        String elemTypeFromMap = compNameandType.get(elem);
        if (!(elemTypeFromMap.equals(expType))) {
            error("Inconsistency in component types; expected " + expType + " type only");
        }
    }

    // checks if there is any duplicate elements in the list
    protected void checkDuplicates(String[] elems) {
        Set<String> uniqElems = new HashSet<String>();

        for (String elem : elems) {
            if (uniqElems.contains(elem)) {
                error(elem + " is already used here");
            } else {
                uniqElems.add(elem);
            }
        }
    }

    // checks if resource properties are valid
    protected void checkResPropertyValidity(String id, String query) {
        if (!(subcompProperties.get(id).contains(query))) {
            error(query + " is not defined for this instance " + id);
        }
    }

    // checks utilization constraint property mapping
    protected void checkUCpropMapping(String restype, String srcProp, List<String> sinkProps) {
        if (restype.equals("CPU")) {
            if (!(srcProp.equals("cpuProvided"))) {
                error(
                        "We only support \"cpuProvided\" property for CPU resource provider instance");
            }

            for (String p : sinkProps) {
                if (!(p.equals("cpuUsed"))) {
                    error(
                            "We only support \"cpuUsed\" property for CPU resource consumer instance");
                }
            }
        } else if (restype.equals("RAM")) {
            if (!(srcProp.equals("ramProvided"))) {
                error(
                        "We only support \"ramProvided\" property for RAM resource provider instance");
            }

            for (String p : sinkProps) {
                if (!(p.equals("ramUsed"))) {
                    error(
                            "We only support \"ramUsed\" property for RAM resource consumer instance");
                }
            }
        } else if (restype.equals("ROM")) {
            if (!(srcProp.equals("romProvided"))) {
                error(
                        "We only support \"romProvided\" property for ROM resource provider instance");
            }

            for (String p : sinkProps) {
                if (!(p.equals("romUsed"))) {
                    error(
                            "We only support \"romUsed\" property for ROM resource consumer instance");
                }
            }
        } else if (restype.equals("MEM")) {
            if (!(srcProp.equals("memProvided"))) {
                error(
                        "We only support \"memProvided\" property for Memory resource provider instance");
            }

            for (String p : sinkProps) {
                if (!(p.equals("memUsed"))) {
                    error(
                            "We only support \"memUsed\" property for Memory resource consumer instance");
                }
            }
        }
    }
}
