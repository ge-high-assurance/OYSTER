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
import com.ge.research.osate.verdict.gui.UnsatCoreView;
import com.ge.research.osate.verdict.gui.ViewUtils;
import com.ge.research.osate.verdict.handlers.VerdictLogger;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Constructor;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Optimize;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;

import org.apache.commons.math3.util.Pair;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.osate.aadl2.AbstractNamedValue;
import org.osate.aadl2.ModalPropertyValue;
import org.osate.aadl2.PropertyAssociation;
import org.osate.aadl2.PropertyExpression;
import org.osate.aadl2.Subcomponent;
import org.osate.aadl2.SystemImplementation;
import org.osate.aadl2.SystemType;
import org.osate.aadl2.impl.EnumerationLiteralImpl;
import org.osate.aadl2.impl.NamedValueImpl;

import oyster.odm.odm_data.Attribute;
import oyster.odm.odm_model.ArithmaticOperator;
import oyster.odm.odm_model.ComparisonOperator;
import oyster.odm.odm_model.ComponentImpl;
import oyster.odm.odm_model.ComponentInstance;
import oyster.odm.odm_model.ComponentType;
import oyster.odm.odm_model.Connection;
import oyster.odm.odm_model.Constraint;
import oyster.odm.odm_model.ConstraintType;
import oyster.odm.odm_model.Model;
import oyster.odm.odm_model.Specification;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

public class Odm2Z3 {

    Map<String, Sort> typeToSort = new HashMap<String, Sort>();
    public static Map<String, Boolean> vlStartsFromGPM = new HashMap<>();
    public static Map<String, Boolean> vlEndsAtGPM = new HashMap<>();
    public static Map<String, PortConnection> PortConnectionMap =
            new HashMap<String, PortConnection>();
    public static Map<String, PortConnection> PortConnectionMapForZ3 =
            new HashMap<String, PortConnection>();
    Map<String, List<Pair<String, String>>> network =
            new HashMap<String, List<Pair<String, String>>>();
    Map<String, Pair<String, String>> network1 = new HashMap<String, Pair<String, String>>();
    List<Expr> assumptions = new ArrayList<>();
    Map<String, Integer> connectionToBandwidth = new HashMap<String, Integer>();
    Map<String, Set<String>> instanceToConnections = new HashMap<String, Set<String>>();
    Map<String, Pair<String, String>> flowNamesToSrcDestInstance =
            new HashMap<String, Pair<String, String>>();
    Map<String, List<Expr>> vlNamesToMsgSizes = new HashMap<String, List<Expr>>();
    Map<String, List<Expr>> vlNamesToMsgPeriods = new HashMap<String, List<Expr>>();
    List<String> vlNames = new ArrayList<String>();
    Map<String, String> softwareToHardwareMap = new HashMap<String, String>();

    Map<String, Integer> app_periods = new HashMap<String, Integer>();
    Map<String, Integer> app_durations = new HashMap<String, Integer>();
    Map<String, Integer> app_priorities = new HashMap<String, Integer>();
    List<String> app_ids = new ArrayList<String>();

    Map<String, Integer> app_rates = new HashMap<String, Integer>();
    Map<String, Integer> proc_slots = new HashMap<String, Integer>();
    List<String> proc_ids = new ArrayList<String>();

    private static List<String> unsatCore = new ArrayList<>();
    private static Map<String, Constraint> unsatConstraint = new HashMap<>();
    private static Map<String, Constraint> constraintMap = new HashMap<>();

    boolean optBandwidthYes = IMASynthesisSettingsPanel.optBandwidthYes;
    boolean opte2eFlowYes = IMASynthesisSettingsPanel.opte2eFlowYes;
    boolean fsbBandwidthYes = IMASynthesisSettingsPanel.fsbBandwidthYes;
    boolean fsbe2eFlowYes = IMASynthesisSettingsPanel.fsbe2eFlowYes;
    boolean fsbAppScheduleYes = IMASynthesisSettingsPanel.fsbAppScheduleYes;
    boolean useUnsatCore = false;
    String hostCompName = IMASynthesisSettingsPanel.hostCompName;
    List<String> instanceBoundTohostCompName = new ArrayList<String>();
    List<EObject> aadlObjects = new ArrayList<>();
    Model odm;

    // this is the entry point to ODM to Z3 translation
    public Odm2Z3Result execute(
            Model odm, List<EObject> aadlObjects, boolean bUseVLE2E, boolean useUnsatCore) {

        // reads odm to make list of system types and implementations
        // also, makes a map between a type and all of it's instances

        Set<String> systemTypes = new HashSet<String>();
        Map<String, List<String>> typeToInstances = new HashMap<String, List<String>>();
        
        
        constraintMap.clear();
        this.odm = odm;
        this.useUnsatCore = useUnsatCore;
        this.aadlObjects = aadlObjects;
        for (ComponentType odmType : odm.getComponentType()) {
            if (!systemTypes.contains(odmType.getName())) {
                systemTypes.add(odmType.getName());
            }
        }

        for (ComponentImpl odmImpl : odm.getComponentImpl()) {
            for (ComponentInstance ci : odmImpl.getSubcomponents()) {
                String typeName = ci.getType().getName();
                String insName = ci.getName();

                if (typeToInstances.containsKey(typeName)) {
                    List<String> updatedInsList = typeToInstances.get(typeName);
                    if (!updatedInsList.contains(insName)) {
                        updatedInsList.add(insName);
                    }
                    typeToInstances.put(typeName, updatedInsList);
                } else {
                    List<String> newInsList = new ArrayList<String>();
                    newInsList.add(insName);
                    typeToInstances.put(typeName, newInsList);
                }
            }

            for (Connection con : odmImpl.getConnections()) {

                PortConnection pcon2 =
                        new PortConnection(
                                con.getName(),
                                con.getConnectionKind().name(),
                                con.getDirection().name(),
                                con.getSource().getComponentPort().getId(),
                                con.getSource().getComponentPort().getName(),
                                con.getSource().getComponentPort().getMode().name(),
                                con.getSource()
                                        .getComponentPort()
                                        .getType()
                                        .getPlainType()
                                        .toString(),
                                con.getDestination().getComponentPort().getId(),
                                con.getDestination().getComponentPort().getName(),
                                con.getDestination().getComponentPort().getMode().name(),
                                con.getDestination()
                                        .getComponentPort()
                                        .getType()
                                        .getPlainType()
                                        .toString(),
                                con.getBandwidth());

                String source = con.getSource().getComponentPort().getId().split("\\.")[0];
                String dest = con.getDestination().getComponentPort().getId().split("\\.")[0];

                Set<String> s = new HashSet<String>();
                s.add(source);
                s.add(dest);

                String src =
                        (source.contains("CCR"))
                                ? con.getSource().getComponentPort().getId()
                                : source + ".portXX";
                String srcPort =
                        (source.contains("CCR"))
                                ? con.getSource().getComponentPort().getName()
                                : "portXX";
                String desti =
                        (dest.contains("CCR"))
                                ? con.getDestination().getComponentPort().getId()
                                : dest + ".portXX";
                String destiPort =
                        (dest.contains("CCR"))
                                ? con.getDestination().getComponentPort().getName()
                                : "portXX";

                //				String src = (source.contains("CCR")) ?  source + ".portXX" : source +
                // ".portXX";
                //				String srcPort = (source.contains("CCR")) ? "portXX" :  "portXX";
                //				String desti = (dest.contains("CCR")) ?   dest + ".portXX" : dest + ".portXX";
                //				String destiPort = (dest.contains("CCR")) ? "portXX" :  "portXX";
                //

                PortConnection pcon =
                        new PortConnection(
                                con.getName(),
                                con.getConnectionKind().name(),
                                con.getDirection().name(),
                                src,
                                srcPort,
                                con.getSource().getComponentPort().getMode().name(),
                                con.getSource()
                                        .getComponentPort()
                                        .getType()
                                        .getPlainType()
                                        .toString(),
                                desti,
                                destiPort,
                                con.getDestination().getComponentPort().getMode().name(),
                                con.getDestination()
                                        .getComponentPort()
                                        .getType()
                                        .getPlainType()
                                        .toString(),
                                con.getBandwidth());
                PortConnectionMap.put(con.getName(), pcon2);
                PortConnectionMapForZ3.put(con.getName(), pcon);
            }
        }

        // initializes the SMT solver
        Map<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        Context ctx = new Context(cfg);
        Optimize sol = ctx.mkOptimize();

        // creates smtlib datatypes and constants based on system types and their
        // instances
        sol = createSmtlibVars(sol, ctx, systemTypes, typeToInstances);

        // creates smtlib datatypes and constants based on port connection information
        if (PortConnectionMapForZ3.entrySet().size() > 0) {
            addConnectionInfoSmt(sol, ctx);
        }

        // translates Oyster constraints to smtlib
        for (ComponentImpl odmImpl : odm.getComponentImpl()) {
            for (Constraint ci : odmImpl.getOysterConstraint()) {
            	ConstraintType constType = ci.getType();
                String constraintName = ci.getSpecification().getConstraintName();
                constraintMap.put(constraintName, ci);
                if (constType.equals(
                        oyster.odm.odm_model.ConstraintType.FIXED_LOCATION_CONSTRAINT)) {
                    sol = handleFLC(sol, ctx, ci);
                } else if (constType.equals(
                        oyster.odm.odm_model.ConstraintType.SEPARATION_CONSTRAINT)) {
                    sol = handleSC(sol, ctx, ci);

                } else if (constType.equals(
                        oyster.odm.odm_model.ConstraintType.CO_LOCATION_CONSTRAINT)) {
                    sol = handleCLC(sol, ctx, ci);
                } else if (constType.equals(
                        oyster.odm.odm_model.ConstraintType.UTILIZATION_CONSTRAINT)) {
                    sol = handleUC(sol, ctx, ci);
                } else if (constType.equals(
                        oyster.odm.odm_model.ConstraintType.VIRTUAL_LINK_CONSTRAINT)) {
                    sol = handleVLC(sol, ctx, ci);
                }
            }
        }

        // generate constraints for app scheduling
        if (fsbAppScheduleYes) {
            for (ComponentImpl odmImpl : odm.getComponentImpl()) {
                for (ComponentInstance ci : odmImpl.getSubcomponents()) {
                    // find application duration, period, priority, rate, processor information,
                    // etc. if given by the user in OYSTER
                    // properties
                    for (Attribute attr : ci.getAttribute()) {
                        if (attr.getName().equals("period")
                                && instanceBoundTohostCompName.contains(ci.getName())) {
                            app_periods.put(
                                    ci.getName(), Integer.parseInt(attr.getValue().toString()));
                        } else if (attr.getName().equals("duration")
                                && instanceBoundTohostCompName.contains(ci.getName())) {
                            app_durations.put(
                                    ci.getName(), Integer.parseInt(attr.getValue().toString()));
                            app_ids.add(ci.getName());
                        } else if (attr.getName().equals("priority")
                                && instanceBoundTohostCompName.contains(ci.getName())) {
                            app_priorities.put(
                                    ci.getName(), Integer.parseInt(attr.getValue().toString()));
                        } else if (attr.getName().equals("rate")
                                && instanceBoundTohostCompName.contains(ci.getName())) {
                            app_rates.put(
                                    ci.getName(), Integer.parseInt(attr.getValue().toString()));
                        } else if (attr.getName().equals("slots_per_cycle")
                                && instanceBoundTohostCompName.contains(ci.getName())) {
                            proc_slots.put(
                                    ci.getName(), Integer.parseInt(attr.getValue().toString()));
                            proc_ids.add(ci.getName());
                        }
                    }
                }
            }

            // we throw error if nothing is bound to the host component
            if (hostCompName == null || hostCompName.equals("")) {
                throw new java.lang.RuntimeException(
                        "No GPM component instance is provided for applications scheduling!");
            }
            if (app_ids.size() == 0) {
                throw new java.lang.RuntimeException(
                        "Error: No application is bound to the component instance " + hostCompName);
            }

            int decision = checkAppScheduleCompatibility();
            if (decision == 1) {
                sol = (!bUseVLE2E) ? createScheduleConstraintsSingleCore(ctx, sol) : sol;
            } else if (decision == 2) {
                sol = (!bUseVLE2E) ? createScheduleConstraintsMultiCore(ctx, sol) : sol;
            } else {
                throw new java.lang.RuntimeException(
                        "Error: cannot schedule apps because not enough information is given.");
            }
        }

        // creates smtlib constants based on VL information gathered from the oyster
        // constraints

        if (vlNames.size() > 0) {
            if (fsbBandwidthYes && !bUseVLE2E) {
                sol = createVLSmtlibConstraints(sol, ctx);
            }

            if (fsbe2eFlowYes && bUseVLE2E) {
                sol = createE2EFlowSmt(sol, ctx);
            }
        }

        // System.out.println("Info: Optimize Network Bandwidth: " + optBandwidthYes);
        if (bUseVLE2E) {
            System.out.println("Info: Optimize Virtual-Link Flows: " + opte2eFlowYes);
            System.out.println("Info: Feasible Virtual-Link Flows: " + fsbe2eFlowYes);
            System.out.println("Info: Feasible Network Bandwidth: " + fsbBandwidthYes);
            System.out.println("Info: Feasible Application Schedule: " + fsbAppScheduleYes);

            // System.out.println("\n\nInput SMTLIB Encoding:");
            // System.out.println(sol);
            System.out.println("\n\nInfo: Running Z3 SMT Solver...");
        }
        int q = assumptions.size();
        Expr assumptionsArr[] = new Expr[q];
        System.arraycopy(assumptions.toArray(), 0, assumptionsArr, 0, q);
        Pair<Odm2Z3Result, Odm2Z3Result> result = null;
        if (sol.Check(assumptionsArr).equals(Status.SATISFIABLE)) {

            // System.out.println("Info: Architecture is satisfiable");
            com.microsoft.z3.Model modelRes = sol.getModel();
            // System.out.println("Info: A feasible solution found by the SMT Solver");
            // Sysftem.out.println(modelRes);
            Odm2Z3Result res =
                    new Odm2Z3Result(
                            modelRes, ctx, flowNamesToSrcDestInstance, instanceBoundTohostCompName);
            return res;

        } else {
            // System.out.println(sol);
            VerdictLogger.info("The input architecture model is UNSAT!");
            if (useUnsatCore) {
                unsatCore.clear();
                unsatConstraint.clear();
                VerdictLogger.info("UNSAT CORE:");
                BoolExpr[] assertions = sol.getAssertions();
                for (Expr c : sol.getUnsatCore()) {
                    for (BoolExpr assertion : assertions) {
                        if (assertion.getArgs()[0].toString().equals(c.toString())) {
                            String assertionName = assertion.getArgs()[1].toString();
                            String oysterConstraint = assertionName.split("_xyz_")[0];
                            unsatCore.add(oysterConstraint);
                            VerdictLogger.info(oysterConstraint);
                        }
                    }
                    // System.out.println(c.getBoolValue().toString());
                }

                // show the unsat core
                Display.getDefault()
                        .asyncExec(
                                () -> {
                                    UnsatCoreView.unsatCore = unsatCore;
                                    UnsatCoreView.constraintMap = constraintMap;
                                    org.apache.commons.lang3.tuple.Pair<IWorkbenchPage, IViewPart>
                                            pair =
                                                    ViewUtils.getPageAndViewByViewId(
                                                            UnsatCoreView.ID);
                                    if (pair != null
                                            && pair.getLeft() != null
                                            && pair.getRight() != null) {
                                        pair.getLeft().hideView(pair.getRight());
                                        try {
                                            pair.getLeft().showView(UnsatCoreView.ID);
                                        } catch (PartInitException e) {
                                            // TODO Auto-generated catch block
                                            e.printStackTrace();
                                        }
                                    }
                                });
            }
            ctx.close();
            return null;
        }
    }

    // this function create smt-lib datatypes based on the instances of any type.
    // also, it creates some maps to keep the information related to ports and
    // connections to easily read the model returned by the solver
    protected Optimize createSmtlibVars(
            Optimize sol,
            Context ctx,
            Set<String> systemTypes,
            Map<String, List<String>> typeToInstances) {
        for (String type : systemTypes) {
            if (typeToInstances.containsKey(type)) {
                List<Constructor> cons = new ArrayList<Constructor>();
                int i = 1;
                for (String ins : typeToInstances.get(type)) {
                    Constructor c =
                            ctx.mkConstructor(type + "_" + i, type + "_" + i, null, null, null);
                    cons.add(c);
                    i++;
                }

                int n = cons.size();
                Constructor consArr[] = new Constructor[n];
                System.arraycopy(cons.toArray(), 0, consArr, 0, n);

                Sort sysSort = ctx.mkDatatypeSort(type, consArr);
                typeToSort.put(type, sysSort);
                List<Expr> exprs = new ArrayList<Expr>();

                int j = 0;
                for (String ins : typeToInstances.get(type)) {
                    Expr exp = ctx.mkConst(ins, sysSort);
                    exprs.add(exp);

                    FuncDecl c = consArr[j].ConstructorDecl();
                    Expr tmp = ctx.mkEq(ctx.mkApp(c), exp);
                    Expr tmpTrack = ctx.mkBoolConst("application_" + c.getName().toString());
                    // sol.Add(tmp);
                    addConstraint(tmpTrack, tmp, sol);
                    j++;
                }

                n = exprs.size();
                Expr exprArr[] = new Expr[n];
                System.arraycopy(exprs.toArray(), 0, exprArr, 0, n);

                // sol.Add(ctx.mkDistinct(exprArr));
                Expr exprArrTrack = ctx.mkBoolConst("distinct_system_types");
                addConstraint(exprArrTrack, ctx.mkDistinct(exprArr), sol);
                i++;
            }
        }

        for (Map.Entry<String, PortConnection> entry : PortConnectionMapForZ3.entrySet()) {
            PortConnection value = entry.getValue();
            String node1 = value.generateSourceInfo();
            String node2 = value.generateDestInfo();
            String name = value.name;
            Integer bandwidth = value.bandwidth;

            network1.put(node1, new Pair(node2, name));
            network1.put(node2, new Pair(node1, name));
            List<Pair<String, String>> node1List = network.get(node1);
            List<Pair<String, String>> node2List = network.get(node2);

            if (node1List == null) {
                node1List = new ArrayList<>();
            }
            node1List.add(new Pair(node2, name));

            if (node2List == null) {
                node2List = new ArrayList<>();
            }
            node2List.add(new Pair(node1, name));
            network.put(node1, node1List);
            network.put(node2, node2List);

            connectionToBandwidth.put(name, bandwidth);

            String ins1 = node1.split("\\.")[0];
            String ins2 = node2.split("\\.")[0];

            if (instanceToConnections.get(ins1) == null) {
                Set<String> temp = new HashSet<>();
                Set<String> temp2 = new HashSet<>();
                temp.add(node1);
                temp2.add(name);
                instanceToConnections.put(ins1, temp2);
            } else {
                instanceToConnections.get(ins1).add(name);
            }

            if (instanceToConnections.get(ins2) == null) {
                Set<String> temp = new HashSet<>();
                Set<String> temp2 = new HashSet<>();
                temp.add(node2);
                temp2.add(name);
                instanceToConnections.put(ins2, temp2);
            } else {
                instanceToConnections.get(ins2).add(name);
            }
        }

        return sol;
    }

    // this function creates smt-lib constraints for virtual link
    // it also considers bag, mtu, msgSize, and msg refresh periods
    // based on the optimization paper
    protected Optimize createVLSmtlibConstraints(Optimize sol, Context ctx) {
        Expr[] mtuVars = new Expr[vlNamesToMsgSizes.size()];
        Expr[] bagVars = new Expr[vlNamesToMsgSizes.size()];
        Expr[] constraint_2 = new Expr[vlNamesToMsgSizes.size()];
        int i = 0;

        for (String vlname : vlNamesToMsgSizes.keySet()) {
            mtuVars[i] = ctx.mkConst(vlname + "_mtu", ctx.mkIntSort());
            bagVars[i] = ctx.mkConst(vlname + "_bag", ctx.mkIntSort());
            constraint_2[i] = ctx.mkDiv(ctx.mkAdd(mtuVars[i], ctx.mkReal(67)), bagVars[i]);

            // constraint on range of values for bag of each VL
            Expr bagRangeTrack = ctx.mkBoolConst("range_of_bag_0_to_128");
            addConstraint(
                    bagRangeTrack,
                    ctx.mkOr(
                            ctx.mkEq(bagVars[i], ctx.mkInt(1)),
                            ctx.mkEq(bagVars[i], ctx.mkInt(2)),
                            ctx.mkEq(bagVars[i], ctx.mkInt(4)),
                            ctx.mkEq(bagVars[i], ctx.mkInt(8)),
                            ctx.mkEq(bagVars[i], ctx.mkInt(16)),
                            ctx.mkEq(bagVars[i], ctx.mkInt(32)),
                            ctx.mkEq(bagVars[i], ctx.mkInt(64)),
                            ctx.mkEq(bagVars[i], ctx.mkInt(128))),
                    sol);

            // constraint on range of values for mtu of each VL
            Expr mtuRangeTrack = ctx.mkBoolConst("range_of_mtu_1_to_1471");
            addConstraint(
                    mtuRangeTrack,
                    ctx.mkAnd(
                            ctx.mkGe(mtuVars[i], ctx.mkInt(1)),
                            ctx.mkLe(mtuVars[i], ctx.mkInt(1471))),
                    sol);

            Expr[] constraint_1 = new Expr[vlNamesToMsgSizes.get(vlname).size()];
            for (int k = 0; k < vlNamesToMsgSizes.get(vlname).size(); k++) {
                Expr msgSizeVar = vlNamesToMsgSizes.get(vlname).get(k);
                Expr refPeriodVar = vlNamesToMsgPeriods.get(vlname).get(k);
                constraint_1[k] = ctx.mkDiv(ceilDivExpr(msgSizeVar, mtuVars[i], ctx), refPeriodVar);
            }

            // message constraint on each VL(constraint 1)
            // forall(j = 1, n_i) sum(ceil(l_ij / mtu_i) / p_ij) <= (1 / bag_i)
            Expr vlConstraint_1Track = ctx.mkBoolConst("vl_constraint_1_for_" + vlname);
            addConstraint(
                    vlConstraint_1Track,
                    ctx.mkLe(ctx.mkAdd(constraint_1), ctx.mkDiv(ctx.mkReal(1), bagVars[i])),
                    sol);
            i++;
        }

        // bandwidth constraint for all VLs(constraint 2)
        // 8000 * forall(i = 1, n) sum((mtu_i + 67) / bag_i) <= B
        Expr vlConstraint_2Track = ctx.mkBoolConst("vl_constraint_2");
        addConstraint(
                vlConstraint_2Track,
                ctx.mkLe(
                        ctx.mkMul(ctx.mkAdd(constraint_2), ctx.mkInt(8000)),
                        ctx.mkIntConst("Bandwidth")),
                sol);

        // jitter constraint for all VLs (constraint 3)
        // 40 + 8 * forall(i = 1, n) sum((mtu_i + 67) / B) <= 500
        Expr jitterConstraintTrack = ctx.mkBoolConst("jitter_constraint");
        addConstraint(
                jitterConstraintTrack,
                ctx.mkLe(
                        ctx.mkAdd(
                                ctx.mkReal(40),
                                ctx.mkDiv(
                                        ctx.mkAdd(
                                                ctx.mkMul(ctx.mkReal(8), ctx.mkAdd(mtuVars)),
                                                ctx.mkReal(67)),
                                        ctx.mkIntConst("Bandwidth"))),
                        ctx.mkReal(500)),
                sol);

        // compute bandwidth
        Expr computeBandwidthTrack = ctx.mkBoolConst("compute_bandwidth_constraint");
        addConstraint(
                computeBandwidthTrack,
                ctx.mkEq(
                        ctx.mkIntConst("NetworkBandwidthComputed"),
                        ctx.mkMul(ctx.mkAdd(constraint_2), ctx.mkInt(8000))),
                sol);

        // assign Upper limit of network bandwidth
        Expr upperLimitBandwidthTrack = ctx.mkBoolConst("upper_limit_for_bandwidth");
        addConstraint(
                upperLimitBandwidthTrack,
                ctx.mkEq(ctx.mkIntConst("Bandwidth"), ctx.mkInt(getTotalNetBandwidth())),
                sol);

        // to minimize network bandwidth, we minimize LHS of constraint 2
        if (optBandwidthYes) {
            sol.MkMinimize(ctx.mkIntConst("NetworkBandwidthComputed"));
        }

        return sol;
    }

    // this function creates smtlib functions to map subcomponents in a component
    // based on the fixed-location constraint
    protected Optimize handleFLC(Optimize sol, Context ctx, Constraint ci) {
        Specification spec = ci.getSpecification();
        String constraintName = spec.getConstraintName();
        ComponentInstance from = spec.getSrcEntities().getEntities().get(0);
        ComponentInstance to = spec.getDestEntities().getEntities().get(0);
        String funcName = from.getType().getName() + "_to_" + to.getType().getName();
        FuncDecl<Sort> funcDecl =
                ctx.mkFuncDecl(
                        funcName,
                        typeToSort.get(from.getType().getName()),
                        typeToSort.get(to.getType().getName()));

        Expr fromExpr = ctx.mkConst(from.getName(), typeToSort.get(from.getType().getName()));
        Expr toExpr = ctx.mkConst(to.getName(), typeToSort.get(to.getType().getName()));

        Random random = new Random();
        Expr flcTrack = ctx.mkBoolConst(constraintName + "_xyz_" + random.nextInt());
        addConstraint(flcTrack, ctx.mkEq(ctx.mkApp(funcDecl, fromExpr), toExpr), sol);

        // TODO : softwareToHardwareMap needs to be more strict
        softwareToHardwareMap.put(from.getName(), to.getName());

        // tracking apps for scheduling
        if (to.getName().equals(hostCompName)) {
            instanceBoundTohostCompName.add(from.getName());
        }

        return sol;
    }

    // this function creates smtlib constraint to ensure some instances are mapped
    // to different types
    protected Optimize handleSC(Optimize sol, Context ctx, Constraint sc) {
        Specification spec = sc.getSpecification();
        String constraintName = spec.getConstraintName();
        List<ComponentInstance> items = spec.getSrcEntities().getEntities();
        String to = spec.getToComponent();
        String funcName = items.get(0).getType().getName() + "_to_" + to;
        FuncDecl<Sort> funcDecl =
                ctx.mkFuncDecl(
                        funcName,
                        typeToSort.get(items.get(0).getType().getName()),
                        typeToSort.get(to));
        List<Expr> exprs = new ArrayList<Expr>();

        for (ComponentInstance item : items) {
            Expr exp =
                    ctx.mkApp(
                            funcDecl,
                            ctx.mkConst(item.getName(), typeToSort.get(item.getType().getName())));
            exprs.add(exp);
        }

        int n = exprs.size();
        Expr exprArr[] = new Expr[n];
        System.arraycopy(exprs.toArray(), 0, exprArr, 0, n);
        Random random = new Random();
        Expr scTrack = ctx.mkBoolConst(constraintName + "_xyz_" + random.nextInt());
        addConstraint(scTrack, ctx.mkDistinct(exprArr), sol);
        return sol;
    }

    // this function creates smtlib constraint to ensure some instances are mapped
    // to same type
    protected Optimize handleCLC(Optimize sol, Context ctx, Constraint sc) {
        Specification spec = sc.getSpecification();
        String constraintName = spec.getConstraintName();
        List<ComponentInstance> items = spec.getSrcEntities().getEntities();
        String to = spec.getToComponent();

        List<Expr> exprs = new ArrayList<Expr>();
        List<Expr> clcTrackList = new ArrayList<Expr>();
        for (ComponentInstance item : items) {
            String funcName = item.getType().getName() + "_to_" + to;
            FuncDecl<Sort> funcDecl =
                    ctx.mkFuncDecl(
                            funcName, typeToSort.get(item.getType().getName()), typeToSort.get(to));
            Expr exp =
                    ctx.mkApp(
                            funcDecl,
                            ctx.mkConst(item.getName(), typeToSort.get(item.getType().getName())));
            exprs.add(exp);
            Random random = new Random();

            Expr clcTrack = ctx.mkBoolConst(constraintName + "_xyz_" + random.nextInt());
            clcTrackList.add(clcTrack);
        }

        for (int i = 0; i < exprs.size() - 1; i++) {
            addConstraint(clcTrackList.get(i), ctx.mkEq(exprs.get(i), exprs.get(i + 1)), sol);
        }

        return sol;
    }

    // this function creates smtlib constraint to ensure utilization constraint is
    // satisfied for some resources
    // the arithmetic operation has precedence from left to right operators
    // TODO : enrich the arithmetic operation for standard operator precedence
    protected Optimize handleUC(Optimize sol, Context ctx, Constraint ci) {
        Specification spec = ci.getSpecification();
        ComponentInstance src = spec.getSrcEntities().getEntities().get(0);
        List<ComponentInstance> dests = spec.getDestEntities().getEntities();
        String restType = spec.getCharacteristicProperty();
        ComparisonOperator compOp = spec.getSrcEntitiesCompOp();
        List<ArithmaticOperator> arSigns = spec.getDestEntitiesSigns().getSign();
        String releVantSrcAttr = "";
        String releVantDestAttr = "";
        int srcValue = 0;
        if (restType.equals("CPU")) {
            releVantSrcAttr = "cpuProvided";
            srcValue = getAttributeValue(src, "cpuProvided");
            if (srcValue != -1) {
                releVantSrcAttr = "cpuProvided";
            }
            srcValue = getAttributeValue(src, "cpuUsed");
            if (srcValue != -1) {
                releVantSrcAttr = "cpuUsed";
            }
            releVantDestAttr = "cpuUsed";
        } else if (restType.equals("RAM")) {
            releVantSrcAttr = "ramProvided";
            srcValue = getAttributeValue(src, "ramProvided");
            if (srcValue != -1) {
                releVantSrcAttr = "ramProvided";
            }
            srcValue = getAttributeValue(src, "ramUsed");
            if (srcValue != -1) {
                releVantSrcAttr = "ramUsed";
            }
            releVantDestAttr = "ramUsed";
        } else if (restType.equals("ROM")) {
            releVantSrcAttr = "romProvided";
            srcValue = getAttributeValue(src, "romProvided");
            if (srcValue != -1) {
                releVantSrcAttr = "romProvided";
            }
            srcValue = getAttributeValue(src, "romUsed");
            if (srcValue != -1) {
                releVantSrcAttr = "romUsed";
            }
            releVantDestAttr = "romUsed";
        } else if (restType.equals("MEM")) {
            releVantSrcAttr = "memProvided";
            releVantDestAttr = "memUsed";
        }

        Expr srcExpVar = ctx.mkConst(src.getName() + "_" + releVantSrcAttr, ctx.mkIntSort());
        Expr srcExp = ctx.mkEq(srcExpVar, ctx.mkInt(getAttributeValue(src, releVantSrcAttr)));
        sol.Add(srcExp);

        List<Expr> dstExpsVar = new ArrayList<Expr>();
        for (ComponentInstance comp : dests) {
            Expr destExpVar = ctx.mkConst(comp.getName() + "_" + releVantDestAttr, ctx.mkIntSort());
            Expr destExp =
                    ctx.mkEq(destExpVar, ctx.mkInt(getAttributeValue(comp, releVantDestAttr)));
            dstExpsVar.add(destExpVar);
            sol.Add(destExp);
        }

        int n = dstExpsVar.size();
        Expr destexprArr[] = new Expr[n];
        System.arraycopy(dstExpsVar.toArray(), 0, destexprArr, 0, n);
        Random random = new Random();

        Expr ciTrack =
                ctx.mkBoolConst(
                        ci.getSpecification().getConstraintName() + "_xyz_" + random.nextInt());
        if (destexprArr.length == 1) {
            if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.EQ)) {
                addConstraint(ciTrack, ctx.mkEq(srcExpVar, destexprArr[0]), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.NEQ)) {
                addConstraint(ciTrack, ctx.mkNot(ctx.mkEq(srcExpVar, destexprArr[0])), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.GT)) {
                addConstraint(ciTrack, ctx.mkGt(srcExpVar, destexprArr[0]), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.LT)) {
                addConstraint(ciTrack, ctx.mkLt(srcExpVar, destexprArr[0]), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.GTE)) {
                addConstraint(ciTrack, ctx.mkGe(srcExpVar, destexprArr[0]), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.LTE)) {
                addConstraint(ciTrack, ctx.mkLe(srcExpVar, destexprArr[0]), sol);
            }
        } else if (destexprArr.length > 1) {
            Expr temp = createArrExp(destexprArr, arSigns, ctx);
            if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.EQ)) {
                addConstraint(ciTrack, ctx.mkEq(srcExpVar, temp), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.NEQ)) {
                addConstraint(ciTrack, ctx.mkNot(ctx.mkEq(srcExpVar, temp)), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.GT)) {
                addConstraint(ciTrack, ctx.mkGt(srcExpVar, temp), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.LT)) {
                addConstraint(ciTrack, ctx.mkLt(srcExpVar, temp), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.GTE)) {
                addConstraint(ciTrack, ctx.mkGe(srcExpVar, temp), sol);
            } else if (compOp.equals(oyster.odm.odm_model.ComparisonOperator.LTE)) {
                addConstraint(ciTrack, ctx.mkLe(srcExpVar, temp), sol);
            }
        }

        return sol;
    }

    // handles the VL constraints from the ODM
    // one source, can have multiple destination for a VL (leads to multiple flow)
    protected Optimize handleVLC(Optimize sol, Context ctx, Constraint fc) {
        Specification spec = fc.getSpecification();
        String constraintName = spec.getConstraintName();
        Random random = new Random();
        String src = softwareToHardwareMap.get(spec.getFromComponent());
        String dest = softwareToHardwareMap.get(spec.getToComponent());

        String vlName = spec.getConstraintName().split("\\.")[0];
        String flowName = spec.getConstraintName().split("\\.")[1].split("@")[0];
        String vl_flow_Name = vlName + "_" + flowName;
        String msgName = spec.getConstraintName().split("@")[1];

        if (src != null && dest != null) {
            if (fsbBandwidthYes) {
                // creates smtlib vars for msgSize and msg refreshPeriod
                Integer msgSize = spec.getMsgSize();
                Integer refPeriod = spec.getRefreshPeriod();

                Expr exp1Temp =
                        ctx.mkConst(vl_flow_Name + "_" + msgName + "_msgSize", ctx.mkIntSort());
                Expr exp2Temp =
                        ctx.mkConst(vl_flow_Name + "_" + msgName + "_refperiod", ctx.mkRealSort());
                Expr exp1 = ctx.mkEq(exp1Temp, ctx.mkInt(msgSize));
                Expr exp2 = ctx.mkEq(exp2Temp, ctx.mkReal(refPeriod));

                Expr vlBwConstraint = ctx.mkAnd(exp1, exp2);

                Expr vlBwConstraintTrack =
                        ctx.mkBoolConst(constraintName + "_xyz_" + random.nextInt());
                addConstraint(vlBwConstraintTrack, vlBwConstraint, sol);

                if (vlNamesToMsgSizes.get(vlName) != null) {
                    vlNamesToMsgSizes.get(vlName).add(exp1Temp);
                } else {
                    List<Expr> temp = new ArrayList<Expr>();
                    temp.add(exp1Temp);
                    vlNamesToMsgSizes.put(vlName, temp);
                }

                if (vlNamesToMsgPeriods.get(vlName) != null) {
                    vlNamesToMsgPeriods.get(vlName).add(exp2Temp);
                } else {
                    List<Expr> temp = new ArrayList<Expr>();
                    temp.add(exp2Temp);
                    vlNamesToMsgPeriods.put(vlName, temp);
                }
            }

            flowNamesToSrcDestInstance.put(vl_flow_Name, new Pair<>(src, dest));
            vlNames.add(vlName);
        }

        return sol;
    }

    protected int getAttributeValue(ComponentInstance item, String attName) {
        for (Attribute attr : item.getAttribute()) {
            if (attr.getName().equals(attName)) {
                return Integer.parseInt(attr.getValue().toString());
            }
        }

        return -1;
    }

    // this used by the Utilization constraint handler for creating Arithmetic
    // expression ins SMT // TODO : check the division operation later
    protected Expr createArrExp(Expr[] destexprArr, List<ArithmaticOperator> arSigns, Context ctx) {
        if (destexprArr.length == 1) {
            return destexprArr[0];
        } else {
            if (arSigns.get(0).equals(oyster.odm.odm_model.ArithmaticOperator.PLUS)) {
                Expr exp =
                        ctx.mkAdd(
                                destexprArr[0],
                                createArrExp(
                                        Arrays.copyOfRange(destexprArr, 1, destexprArr.length),
                                        arSigns.subList(1, arSigns.size()),
                                        ctx));
                return exp;
            } else if (arSigns.get(0).equals(oyster.odm.odm_model.ArithmaticOperator.MINUS)) {
                Expr exp =
                        ctx.mkSub(
                                destexprArr[0],
                                createArrExp(
                                        Arrays.copyOfRange(destexprArr, 1, destexprArr.length),
                                        arSigns.subList(1, arSigns.size()),
                                        ctx));
                return exp;
            } else if (arSigns.get(0).equals(oyster.odm.odm_model.ArithmaticOperator.MUL)) {
                Expr exp =
                        ctx.mkMul(
                                destexprArr[0],
                                createArrExp(
                                        Arrays.copyOfRange(destexprArr, 1, destexprArr.length),
                                        arSigns.subList(1, arSigns.size()),
                                        ctx));
                return exp;
            } else {
                Expr exp =
                        ctx.mkDiv(
                                destexprArr[0],
                                createArrExp(
                                        Arrays.copyOfRange(destexprArr, 1, destexprArr.length),
                                        arSigns.subList(1, arSigns.size()),
                                        ctx));
                return exp;
            }
        }
    }

    // this is a generic function to perform ceil of two terms after division
    protected Expr ceilDivExpr(Expr term1, Expr term2, Context ctx) {
        Expr mod = ctx.mkEq(ctx.mkMod(term1, term2), ctx.mkInt(0));
        Expr div = ctx.mkDiv(term1, term2);
        Expr divPlusOne = ctx.mkAdd(ctx.mkDiv(term1, term2), ctx.mkInt(1));
        Expr res = ctx.mkITE(mod, div, divPlusOne);
        return res;
    }

    protected void calculateConnectionsAndCreateConnectionSorts(
            Optimize sol, com.microsoft.z3.Context ctx) {
        Set<String> ghostConnections = new HashSet<>();
        HashMap<String, Boolean> processedNode = new HashMap<>();
        HashMap<String, Boolean> processedComponent = new HashMap<>();

        Set<String> nodes = new HashSet<>();

        for (String key : network.keySet()) {
            for (Pair<String, String> ele : network.get(key)) {
                nodes.add(key);
                nodes.add(ele.getFirst());
            }
        }

        /*
         * for (String node : nodes) { // String insName =
         * entry.getKey().split("\\.")[0]; if (!processedNode.containsKey(node)) { if
         * (!isCCRType(node, aadlObjects)) { String component = node.split("\\.")[0];
         * ArrayList<String> seenNodes = new ArrayList<>();
         *
         * for (String key : network.keySet()) { List<Pair<String, String>> pairs =
         * network.get(key); for (Pair<String, String> pair : pairs) { if
         * (pair.getFirst().split("\\.")[0].equals(component)) { if
         * (!seenNodes.contains(pair.getFirst())) { seenNodes.add(pair.getFirst()); } }
         * }
         *
         * if (key.split("\\.")[0].equals(component)) { if (!seenNodes.contains(key)) {
         * seenNodes.add(key); } } }
         *
         * // create ghost connections for (String node2 : seenNodes) { Set<String>
         * endpoints = new HashSet<>(); if (!node.equals(node2) &&
         * !processedNode.containsKey(node2)) { ghostConnections.add("ghost" +
         * ghostCount); endpoints.add(node); endpoints.add(node2);
         * ghostConnectionEndPoints.put("ghost" + ghostCount, endpoints); ghostCount++;
         * } } } processedNode.put(node, true); } }
         */

        List<Constructor> conns = new ArrayList<Constructor>();
        int i = 1;
        for (String conNameKey : PortConnectionMapForZ3.keySet()) {
            Constructor c =
                    ctx.mkConstructor("Connection_" + i, "Connection_" + i, null, null, null);
            conns.add(c);
            i++;
        }

        /*
         * for (String conNameKey : ghostConnections) { Constructor c =
         * ctx.mkConstructor("Connection_" + i, "Connection_" + i, null, null, null);
         * conns.add(c); i++; }
         */

        int n = conns.size();
        Constructor consArrConnections[] = new Constructor[n];
        System.arraycopy(conns.toArray(), 0, consArrConnections, 0, n);

        Sort sysSort = ctx.mkDatatypeSort("Connection", consArrConnections);
        typeToSort.put("Connection", sysSort);
        List<Expr> exprsConnections = new ArrayList<Expr>();

        int j = 0;
        for (Map.Entry<String, PortConnection> entry : PortConnectionMapForZ3.entrySet()) {
            Expr exp = ctx.mkConst(entry.getValue().name, sysSort);
            exprsConnections.add(exp);

            FuncDecl c = consArrConnections[j].ConstructorDecl();
            Expr tmp = ctx.mkEq(ctx.mkApp(c), exp);
            sol.Add(tmp);

            j++;
        }

        /*
         * for (String entry : ghostConnections) { Expr exp = ctx.mkConst(entry,
         * sysSort); exprsConnections.add(exp);
         *
         * FuncDecl c = consArrConnections[j].ConstructorDecl(); Expr tmp =
         * ctx.mkEq(ctx.mkApp(c), exp); sol.Add(tmp);
         *
         * j++; }
         */
        n = exprsConnections.size();
        Expr exprArrConnections[] = new Expr[n];
        System.arraycopy(exprsConnections.toArray(), 0, exprArrConnections, 0, n);

        sol.Add(ctx.mkDistinct(exprArrConnections));
    }

    // this function encodes connection and port information in SMTLIB
    protected void addConnectionInfoSmt(Optimize sol, Context ctx) {

        // process connections
        /*
         * List<Constructor> cons = new ArrayList<Constructor>(); int i = 1; for (String
         * conNameKey : PortConnectionMap.keySet()) { Constructor c =
         * ctx.mkConstructor("Connection_" + i, "Connection_" + i, null, null, null);
         * cons.add(c); i++; }
         *
         * int n = cons.size(); Constructor consArrConnections[] = new Constructor[n];
         * System.arraycopy(cons.toArray(), 0, consArrConnections, 0, n);
         *
         * Sort sysSort = ctx.mkDatatypeSort("Connection", consArrConnections);
         * typeToSort.put("Connection", sysSort); List<Expr> exprsConnections = new
         * ArrayList<Expr>();
         *
         * int j = 0; for (Map.Entry<String, PortConnection> entry :
         * PortConnectionMap.entrySet()) { Expr exp = ctx.mkConst(entry.getValue().name,
         * sysSort); exprsConnections.add(exp);
         *
         * FuncDecl c = consArrConnections[j].ConstructorDecl(); Expr tmp =
         * ctx.mkEq(ctx.mkApp(c), exp); sol.Add(tmp); j++; }
         *
         * //n = exprs.size(); Expr exprArrConnections[] = new Expr[n];
         * System.arraycopy(exprsConnections.toArray(), 0, exprArrConnections, 0, n);
         *
         * sol.Add(ctx.mkDistinct(exprArrConnections));
         */
        // process ports

        calculateConnectionsAndCreateConnectionSorts(sol, ctx);

        List<Constructor> cons = new ArrayList<Constructor>();
        int i = 1;
        for (String conNameKey : PortConnectionMapForZ3.keySet()) {
            Constructor p1 = ctx.mkConstructor("Port_" + i, "Port_" + i, null, null, null);
            Constructor p2 =
                    ctx.mkConstructor("Port_" + (i + 1), "Port_" + (i + 1), null, null, null);
            cons.add(p1);
            cons.add(p2);
            i = i + 2;
        }

        int n = cons.size();
        Constructor[] consArr = new Constructor[n];
        System.arraycopy(cons.toArray(), 0, consArr, 0, n);

        Sort sysSort = ctx.mkDatatypeSort("Port", consArr);
        typeToSort.put("Port", sysSort);
        List<Expr> exprs = new ArrayList<Expr>();

        int j = 0;

        HashSet<String> portConstCreated = new HashSet<>();
        for (Map.Entry<String, PortConnection> entry : PortConnectionMapForZ3.entrySet()) {
            if (!portConstCreated.contains(entry.getValue().sourceEntityName)) {
                Expr exp1 = ctx.mkConst(entry.getValue().sourceEntityName, sysSort);
                exprs.add(exp1);
                FuncDecl c1 = consArr[j].ConstructorDecl();
                Expr tmp1 = ctx.mkEq(ctx.mkApp(c1), exp1);
                sol.Add(tmp1);
                portConstCreated.add(entry.getValue().sourceEntityName);
                j++;
            }

            if (!portConstCreated.contains(entry.getValue().destEntityName)) {
                Expr exp2 = ctx.mkConst(entry.getValue().destEntityName, sysSort);
                exprs.add(exp2);
                FuncDecl c2 = consArr[j].ConstructorDecl();
                Expr tmp2 = ctx.mkEq(ctx.mkApp(c2), exp2);
                sol.Add(tmp2);
                portConstCreated.add(entry.getValue().destEntityName);
                j++;
            }
        }

        n = exprs.size();
        Expr[] exprArr = new Expr[n];
        System.arraycopy(exprs.toArray(), 0, exprArr, 0, n);

        Expr distinctPortsTrack = ctx.mkBoolConst("distinct_ports");
        addConstraint(distinctPortsTrack, ctx.mkDistinct(exprArr), sol);

        // create function for port to port via connection
        // port1 -> connection -> port2
        Sort[] inputs = new Sort[] {typeToSort.get("Port"), typeToSort.get("Connection")};
        FuncDecl<Sort> func =
                ctx.mkFuncDecl("Port_Connection_Port", inputs, typeToSort.get("Port"));

        for (Map.Entry<String, PortConnection> entry : PortConnectionMapForZ3.entrySet()) {
            Expr port1 = ctx.mkConst(entry.getValue().sourceEntityName, typeToSort.get("Port"));
            Expr port2 = ctx.mkConst(entry.getValue().destEntityName, typeToSort.get("Port"));
            Expr connection = ctx.mkConst(entry.getValue().name, typeToSort.get("Connection"));
            Expr pccTrack =
                    ctx.mkBoolConst(
                            "port_connection_"
                                    + entry.getValue().sourceEntityName
                                    + "_to_"
                                    + entry.getValue().destEntityName);
            addConstraint(pccTrack, ctx.mkEq(ctx.mkApp(func, port1, connection), port2), sol);
        }

        // create function for connection to bandwidth
        // connection -> bandwidth
        FuncDecl<Sort> func2 =
                ctx.mkFuncDecl(
                        "Connection_bandwidth", typeToSort.get("Connection"), ctx.mkIntSort());

        for (Map.Entry<String, Integer> entry : connectionToBandwidth.entrySet()) {
            Expr connection = ctx.mkConst(entry.getKey(), typeToSort.get("Connection"));
            Expr bandwidth = ctx.mkInt(entry.getValue());
            Expr bandwidthConstraintTrack =
                    ctx.mkBoolConst("bandwidth_constraint_for_connection_" + entry.getKey());
            addConstraint(
                    bandwidthConstraintTrack,
                    ctx.mkEq(ctx.mkApp(func2, connection), bandwidth),
                    sol);
        }
    }

    // this function creates the SMTLIB constraints to generate feasible end-to-end
    // flow
    protected Optimize createE2EFlowSmt(Optimize sol, Context ctx) {
        // create vlflow datatypes first
        List<Constructor> cons = new ArrayList<Constructor>();
        int i = 1;
        for (String vlflownameKey : flowNamesToSrcDestInstance.keySet()) {
            Constructor c = ctx.mkConstructor("VLFlow_" + i, "VLFlow_" + i, null, null, null);
            String src = flowNamesToSrcDestInstance.get(vlflownameKey).getFirst();
            String dest = flowNamesToSrcDestInstance.get(vlflownameKey).getSecond();
            if (src.contains("GPM")) { // TODO: refine GPMApp sort detection

                vlStartsFromGPM.put(vlflownameKey, true);
            } else {
                vlStartsFromGPM.put(vlflownameKey, false);
            }
            if (dest.contains("GPM")) { // TODO: refine GPMApp sort detection
                vlEndsAtGPM.put(vlflownameKey, true);
            } else {
                vlEndsAtGPM.put(vlflownameKey, false);
            }

            cons.add(c);
            i++;
        }

        int n = cons.size();
        Constructor consArr[] = new Constructor[n];
        System.arraycopy(cons.toArray(), 0, consArr, 0, n);

        Sort sysSort = ctx.mkDatatypeSort("VLFlow", consArr);
        typeToSort.put("VLFlow", sysSort);
        List<Expr> exprs = new ArrayList<Expr>();

        int j = 0;
        for (String vlflownameKey : flowNamesToSrcDestInstance.keySet()) {
            Expr exp = ctx.mkConst(vlflownameKey, sysSort);
            exprs.add(exp);

            FuncDecl c = consArr[j].ConstructorDecl();
            Expr tmp = ctx.mkEq(ctx.mkApp(c), exp);
            sol.Add(tmp);
            j++;
        }

        n = exprs.size();
        Expr exprArr[] = new Expr[n];
        System.arraycopy(exprs.toArray(), 0, exprArr, 0, n);

        sol.Add(ctx.mkDistinct(exprArr));

        // now, create the vlflow -> source function
        String funcName = "VLFlow_Source";
        FuncDecl<Sort> funcDeclSrc =
                ctx.mkFuncDecl(funcName, typeToSort.get("VLFlow"), typeToSort.get("Port"));

        // now, create the vlflow -> destination function
        funcName = "VLFlow_Destination";
        FuncDecl<Sort> funcDeclDest =
                ctx.mkFuncDecl(funcName, typeToSort.get("VLFlow"), typeToSort.get("Port"));

        // no port, only instance

        // now, create the vlflow function
        // vlflow -> connection -> (0/1)
        funcName = "VLFlow_Connection";
        Sort[] inputs = new Sort[] {typeToSort.get("VLFlow"), typeToSort.get("Connection")};
        FuncDecl<Sort> funcDecl = ctx.mkFuncDecl(funcName, inputs, ctx.mkIntSort());

        // add entries to the function
        for (String vlflowname : flowNamesToSrcDestInstance.keySet()) {
            List<Expr> srcNbrs = new ArrayList();
            List<Expr> destNbrs = new ArrayList();
            String src = flowNamesToSrcDestInstance.get(vlflowname).getFirst();
            String dest = flowNamesToSrcDestInstance.get(vlflowname).getSecond();
            String vlName = vlflowname.split("_")[0];
            String flowName = vlflowname.split("_")[1];
            Set<Expr> allExprConnection = new HashSet<Expr>();
            HashMap<String, Boolean> processedNode = new HashMap<>();
            HashMap<String, Boolean> processedComponent = new HashMap<>();

            Set<String> nodes = new HashSet<>();
            // we create boolean variable (0 or 1) for each connection in the network
            // (network)
            boolean bSrcDone = false;
            boolean bDestDone = false;
            for (Map.Entry<String, Pair<String, String>> entry : network1.entrySet()) {
                if (entry.getKey().startsWith(src) && !bSrcDone) {
                    Expr srcNbr =
                            ctx.mkApp(
                                    funcDecl,
                                    ctx.mkConst(vlflowname, typeToSort.get("VLFlow")),
                                    ctx.mkConst(
                                            entry.getValue().getSecond(),
                                            typeToSort.get("Connection")));
                    srcNbrs.add(srcNbr);
                    sol.Add(
                            ctx.mkOr(
                                    ctx.mkEq(srcNbr, ctx.mkInt(0)),
                                    ctx.mkEq(srcNbr, ctx.mkInt(1))));
                    allExprConnection.add(srcNbr);
                    bSrcDone = true;
                } else if (entry.getKey().startsWith(dest) && !bDestDone) {
                    Expr destNbr =
                            ctx.mkApp(
                                    funcDecl,
                                    ctx.mkConst(vlflowname, typeToSort.get("VLFlow")),
                                    ctx.mkConst(
                                            entry.getValue().getSecond(),
                                            typeToSort.get("Connection")));
                    destNbrs.add(destNbr);
                    sol.Add(
                            ctx.mkOr(
                                    ctx.mkEq(destNbr, ctx.mkInt(0)),
                                    ctx.mkEq(destNbr, ctx.mkInt(1))));
                    allExprConnection.add(destNbr);
                    bDestDone = true;
                }
            }

            for (String key : network.keySet()) {
                for (Pair<String, String> ele : network.get(key)) {
                    nodes.add(key);
                    nodes.add(ele.getFirst());
                }
            }

            for (String node : nodes) {
                // String insName = entry.getKey().split("\\.")[0];
                if (node.contains(src) || node.contains(dest)) {
                    continue;
                }

                ArrayList<String> nbrConnections = new ArrayList<>();
                if (!processedNode.containsKey(node)) {
                    for (String key : network.keySet()) {
                        List<Pair<String, String>> pairs = network.get(key);
                        for (Pair<String, String> pair : pairs) {
                            if (pair.getFirst().equals(node)) {
                                if (!nbrConnections.contains(pair.getSecond())) {
                                    nbrConnections.add(pair.getSecond());
                                }
                            }
                        }
                        if (key.equals(node)) {
                            for (Pair<String, String> pair : pairs) {
                                if (!nbrConnections.contains(pair.getSecond())) {
                                    nbrConnections.add(pair.getSecond());
                                }
                            }
                        }
                    }

                    /*
                     * if (!isType(node, IMATypes.CCR, aadlObjects)) {
                     *
                     * for (String ghostConnection : ghostConnectionEndPoints.keySet()) { if
                     * (ghostConnectionEndPoints.get(ghostConnection).contains(node)) {
                     * nbrConnections.add(ghostConnection); } } }
                     */
                    processedNode.put(node, true);
                }

                Expr[] nbrCons = new Expr[nbrConnections.size()];
                j = 0;

                for (String nbr : nbrConnections) {
                    nbrCons[j] =
                            ctx.mkApp(
                                    funcDecl,
                                    ctx.mkConst(vlflowname, typeToSort.get("VLFlow")),
                                    ctx.mkConst(nbr, typeToSort.get("Connection")));
                    sol.Add(
                            ctx.mkOr(
                                    ctx.mkEq(nbrCons[j], ctx.mkInt(0)),
                                    ctx.mkEq(nbrCons[j], ctx.mkInt(1))));
                    allExprConnection.add(nbrCons[j]);
                    j++;
                }

                // for a feasible flow, in any intermediate instance, only two connection (2)
                // will be active
                // otherwise, the flow does not use this instance (0)

                if (nbrConnections.size() > 1) {
                    Expr exp3 =
                            ctx.mkOr(
                                    ctx.mkEq(ctx.mkAdd(nbrCons), ctx.mkInt(2)),
                                    (ctx.mkEq(ctx.mkAdd(nbrCons), ctx.mkInt(0))));
                    sol.Add(exp3);
                } else {
                    Expr exp3 =
                            ctx.mkOr(
                                    ctx.mkEq(ctx.mkAdd(nbrCons), ctx.mkInt(0)),
                                    (ctx.mkEq(ctx.mkAdd(nbrCons), ctx.mkInt(0))));
                    sol.Add(exp3);
                }
            }

            Expr[] srcNbrsArr = new Expr[srcNbrs.size()];
            srcNbrsArr = srcNbrs.toArray(srcNbrsArr);

            Expr[] destNbrsArr = new Expr[destNbrs.size()];
            destNbrsArr = destNbrs.toArray(destNbrsArr);

            // for a feasible flow, only one connection from src is 1
            Expr srcVlTrack = ctx.mkBoolConst("src_constraint_for_" + vlName);
            addConstraint(srcVlTrack, ctx.mkEq(ctx.mkAdd(srcNbrsArr), ctx.mkInt(1)), sol);

            // for a feasible flow, only one connection to dest is 1
            Expr destVlTrack = ctx.mkBoolConst("dest_constraint_for_" + vlName);
            addConstraint(destVlTrack, ctx.mkEq(ctx.mkAdd(destNbrsArr), ctx.mkInt(1)), sol);

            // minimize to get the path with minimum hop
            if (opte2eFlowYes) {
                n = allExprConnection.size();
                Expr allExprConnectionArr[] = new Expr[n];
                System.arraycopy(allExprConnection.toArray(), 0, allExprConnectionArr, 0, n);
                sol.MkMinimize(ctx.mkAdd(allExprConnectionArr));
            }
        }
        return sol;
    }

    // this method tries to read the network bandwidth info given by the users,
    // otherwise it uses default value
    protected long getTotalNetBandwidth() {
        // default values
        long totalBandwidth = 5000000000L;
        int maxBandwidthPercentage = 80;

        // checks if user has provided the bandwidth information as OYSTER property
        for (ComponentType odmType : odm.getComponentType()) {
            for (Attribute attr : odmType.getAttribute()) {
                if (attr.getName().equals("totalBandwidth")) {
                    totalBandwidth = Long.parseLong(attr.getValue().toString());
                }

                if (attr.getName().equals("maxBandwidthPercentage")) {
                    int val = Integer.parseInt(attr.getValue().toString());
                    if (val >= 1 && val <= 100) {
                        maxBandwidthPercentage = val;
                    } else {
                        System.out.println(
                                "Invalid percentage for total bandwidth, using the default value 70%");
                    }
                }
            }
        }
        return ((totalBandwidth * maxBandwidthPercentage) / 100);
    }

    // this method creates constraints for single-core application schedule
    protected Optimize createScheduleConstraintsSingleCore(Context ctx, Optimize sol) {
        String funcName = "Single_core_scheduling_map";
        FuncDecl<Sort> funcDecl =
                ctx.mkFuncDecl(funcName, typeToSort.get("GPMApp"), ctx.mkIntSort());

        String funcName2 = "App_periods_single_core";
        FuncDecl<Sort> funcDecl2 =
                ctx.mkFuncDecl(funcName2, typeToSort.get("GPMApp"), ctx.mkIntSort());
        Random random = new Random();
        if (app_ids.size() == 1) {
            String app = app_ids.get(0);
            Expr p = ctx.mkIntConst(app + "_period");
            Expr p_min = ctx.mkGe(p, ctx.mkInt(1));
            Expr p_eq = ctx.mkEq(p, ctx.mkInt(app_periods.get(app)));
            Expr d = ctx.mkIntConst(app + "_duration");
            Expr d_min = ctx.mkGe(d, ctx.mkInt(1));
            Expr d_eq = ctx.mkEq(d, ctx.mkInt(app_durations.get(app)));
            Expr pr = ctx.mkIntConst(app + "_priority");
            Expr pr_min = ctx.mkGe(pr, ctx.mkInt(0));
            Expr pr_eq = ctx.mkEq(pr, ctx.mkInt(app_priorities.get(app)));
            Expr s = ctx.mkIntConst(app + "_start");
            Expr s_min = ctx.mkGe(s, ctx.mkInt(0));
            Expr schedSingleApp = ctx.mkAnd(p_eq, d_eq, pr_eq, p_min, d_min, pr_min, s_min);
            Expr singleAppTrack = ctx.mkBoolConst("sched_singlecore");
            addConstraint(singleAppTrack, schedSingleApp, sol);
        } else {
            // for each pair of apps
            for (int i = 0; i < app_ids.size() - 1; i++) {
                String app1 = app_ids.get(i);
                Expr p_i = ctx.mkIntConst(app1 + "_period");
                Expr p_i_min = ctx.mkGe(p_i, ctx.mkInt(1));
                Expr p_i_eq = ctx.mkEq(p_i, ctx.mkInt(app_periods.get(app1)));
                Expr d_i = ctx.mkIntConst(app1 + "_duration");
                Expr d_i_min = ctx.mkGe(d_i, ctx.mkInt(1));
                Expr d_i_eq = ctx.mkEq(d_i, ctx.mkInt(app_durations.get(app1)));
                Expr pr_i = ctx.mkIntConst(app1 + "_priority");
                Expr pr_i_min = ctx.mkGe(pr_i, ctx.mkInt(0));
                Expr pr_i_eq = ctx.mkEq(pr_i, ctx.mkInt(app_priorities.get(app1)));
                Expr s_i = ctx.mkIntConst(app1 + "_start");
                Expr s_i_min = ctx.mkGe(s_i, ctx.mkInt(0));
                for (int j = i + 1; j < app_ids.size(); j++) {
                    String app2 = app_ids.get(j);
                    Expr p_j = ctx.mkIntConst(app2 + "_period");
                    Expr p_j_min = ctx.mkGe(p_j, ctx.mkInt(1));
                    Expr p_j_eq = ctx.mkEq(p_j, ctx.mkInt(app_periods.get(app2)));
                    Expr d_j = ctx.mkIntConst(app2 + "_duration");
                    Expr d_j_min = ctx.mkGe(d_j, ctx.mkInt(1));
                    Expr d_j_eq = ctx.mkEq(d_j, ctx.mkInt(app_durations.get(app2)));
                    Expr pr_j = ctx.mkIntConst(app2 + "_priority");
                    Expr pr_j_min = ctx.mkGe(pr_j, ctx.mkInt(0));
                    Expr pr_j_eq = ctx.mkEq(pr_j, ctx.mkInt(app_priorities.get(app2)));
                    Expr s_j = ctx.mkIntConst(app2 + "_start");
                    Expr s_j_min = ctx.mkGe(s_j, ctx.mkInt(0));

                    Expr gcd_pi_pj = ctx.mkIntConst("sched" + "_" + app1 + "_" + app2 + "_periods");
                    Expr gcd_pi_pj_eq =
                            ctx.mkEq(
                                    gcd_pi_pj,
                                    ctx.mkInt(GCD(app_periods.get(app1), app_periods.get(app2))));

                    // s1 > s2
                    Expr expr2 = ctx.mkGt(s_i, s_j);
                    // s2 > s1
                    Expr expr3 = ctx.mkLt(s_i, s_j);
                    // d1 <= s2 − s1 <= gcd(p1,p2) − d2
                    Expr expr4 =
                            ctx.mkAnd(
                                    ctx.mkLe(d_i, ctx.mkSub(s_j, s_i)),
                                    ctx.mkLe(ctx.mkSub(s_j, s_i), ctx.mkSub(gcd_pi_pj, d_j)));
                    // d2 <= s1 − s2 <= gcd(p1,p2) − d1
                    Expr expr5 =
                            ctx.mkAnd(
                                    ctx.mkLe(d_j, ctx.mkSub(s_i, s_j)),
                                    ctx.mkLe(ctx.mkSub(s_i, s_j), ctx.mkSub(gcd_pi_pj, d_i)));

                    // (s2 > s1) && (d1 <= s2 − s1 <= gcd(p1,p2) − d2)
                    Expr con2 = ctx.mkAnd(expr3, expr4);
                    // (s1 > s2) && (d2 <= s1 − s2 <= gcd(p1,p2) − d1)
                    Expr con3 = ctx.mkAnd(expr2, expr5);

                    // if two apps have start time >= 0, they are schedulable
                    Expr con4 = ctx.mkImplies(ctx.mkAnd(s_i_min, s_j_min), ctx.mkOr(con2, con3));

                    // enforce priority on scheduling
                    // if priority is lower, start time is earlier.
                    // if any priority is 0, skip this rule
                    Expr expr6 = ctx.mkGt(pr_i, ctx.mkInt(0));
                    Expr expr7 = ctx.mkGt(pr_j, ctx.mkInt(0));
                    Expr expr8 = ctx.mkLt(pr_j, pr_i);
                    Expr expr9 = ctx.mkLt(pr_i, pr_j);
                    Expr expr81 = ctx.mkLt(s_j, s_i);
                    Expr expr91 = ctx.mkLt(s_i, s_j);
                    Expr con41 = ctx.mkImplies(ctx.mkAnd(expr6, expr7, expr8), expr81);
                    Expr con42 = ctx.mkImplies(ctx.mkAnd(expr6, expr7, expr9), expr91);

                    Expr scheduleIJ =
                            ctx.mkAnd(
                                    con4,
                                    con41,
                                    con42,
                                    p_i_eq,
                                    d_i_eq,
                                    pr_i_eq,
                                    p_j_eq,
                                    d_j_eq,
                                    pr_j_eq,
                                    gcd_pi_pj_eq,
                                    p_i_min,
                                    p_j_min,
                                    d_i_min,
                                    d_j_min,
                                    pr_i_min,
                                    pr_j_min);
                    Expr scheduleIJTrack = ctx.mkBoolConst("sched_" + app1 + "_and_" + app2);
                    addConstraint(scheduleIJTrack, scheduleIJTrack, sol);
                }
            }
        }

        // check all apps are schedulable in one core (all apps have start time >= 0)
        // applicable for single core
        for (int i = 0; i < app_ids.size(); i++) {
            String app = app_ids.get(i);
            Expr s_i = ctx.mkIntConst(app + "_start");
            Expr s_i_min = ctx.mkGe(s_i, ctx.mkInt(0));
            Expr pred = ctx.mkBoolConst(app + "_is_schedulable");

            assumptions.add(ctx.mkNot(pred));
            Expr predTrack = ctx.mkBoolConst("sched_" + app + "_is_schedulable");

            addConstraint(predTrack, ctx.mkOr(s_i_min, pred), sol);

            // fillup the function Single_core_scheduling_map
            Expr startTimeTrack = ctx.mkBoolConst("sched_" + app + "_has_starttime_scheduled");
            addConstraint(
                    startTimeTrack,
                    ctx.mkEq(
                            ctx.mkApp(funcDecl, ctx.mkConst(app, typeToSort.get("GPMApp"))),
                            ctx.mkIntConst(app + "_start")),
                    sol);

            // fillup the function App_periods_single_core
            Expr periodTrack = ctx.mkBoolConst("sched_" + app + "_has_valid_period_assigned");
            sol.Add(
                    periodTrack,
                    ctx.mkEq(
                            ctx.mkApp(funcDecl2, ctx.mkConst(app, typeToSort.get("GPMApp"))),
                            ctx.mkIntConst(app + "_period")));
        }

        return sol;
    }

    // this method creates constraints for multi-core application schedule
    protected Optimize createScheduleConstraintsMultiCore(Context ctx, Optimize sol) {
        String funcName = "Multi_core_scheduling_map";
        Sort[] inputs = new Sort[] {typeToSort.get("GPMApp"), typeToSort.get("ProcessorGPM")};
        FuncDecl<Sort> funcDecl = ctx.mkFuncDecl(funcName, inputs, ctx.mkIntSort());

        String funcName2 = "App_periods_multi_core";
        Sort[] inputs2 = new Sort[] {typeToSort.get("GPMApp"), typeToSort.get("ProcessorGPM")};
        FuncDecl<Sort> funcDecl2 = ctx.mkFuncDecl(funcName2, inputs, ctx.mkIntSort());

        // (<app, proc>) -> (<period, period_expr>)
        Map<Pair<String, String>, Pair<Integer, Expr>> app_periods =
                new HashMap<Pair<String, String>, Pair<Integer, Expr>>();

        for (int m = 0; m < proc_ids.size(); m++) {
            String proc = proc_ids.get(m);
            Expr proc_slot = ctx.mkIntConst(proc + "_slot");
            sol.Add(ctx.mkGe(proc_slot, ctx.mkInt(1)));
            sol.Add(ctx.mkEq(proc_slot, ctx.mkInt(proc_slots.get(proc))));

            for (int n = 0; n < app_ids.size(); n++) {
                String apps = app_ids.get(n);
                Expr app_rate = ctx.mkIntConst(app_ids.get(n) + "_rate");
                Expr period_expr = ctx.mkDiv(proc_slot, app_rate);

                // Currently, app rates must be multiple of proc slots per cycle
                // otherwise, we throw error
                if (proc_slots.get(proc) % app_rates.get(apps) != 0) {
                    throw new java.lang.RuntimeException(
                            "Error: Application rate must be multiple of Processor's slot per cycle");
                }

                int period = proc_slots.get(proc) / app_rates.get(apps);
                app_periods.put(
                        new Pair(app_ids.get(n), proc_ids.get(m)), new Pair(period, period_expr));

                sol.Add(ctx.mkGe(app_rate, ctx.mkInt(1)));
                sol.Add(ctx.mkEq(app_rate, ctx.mkInt(app_rates.get(apps))));
                sol.Add(ctx.mkGe(period_expr, ctx.mkInt(1)));
            }
        }

        if (app_ids.size() == 1) {
            String app = app_ids.get(0);
            Expr d = ctx.mkIntConst(app + "_duration");
            Expr d_min = ctx.mkGe(d, ctx.mkInt(1));
            Expr d_eq = ctx.mkEq(d, ctx.mkInt(app_durations.get(app)));
            Expr pr = ctx.mkIntConst(app + "_priority");
            Expr pr_min = ctx.mkGe(pr, ctx.mkInt(0));
            Expr pr_eq = ctx.mkEq(pr, ctx.mkInt(app_priorities.get(app)));

            for (int k = 0; k < proc_ids.size(); k++) {
                String proc = proc_ids.get(k);
                Expr s = ctx.mkIntConst(app + "_start_" + proc);
                Expr s_min = ctx.mkGe(s, ctx.mkInt(0));
                Expr p = ctx.mkIntConst(app + "_period_" + proc);
                Expr p_min = ctx.mkGe(p, ctx.mkInt(1));
                Expr p_eq = ctx.mkEq(p, ctx.mkInt(app_periods.get(new Pair(app, proc)).getFirst()));
                Expr singleSched = ctx.mkAnd(p_eq, d_eq, pr_eq, p_min, d_min, pr_min, s_min);
                Expr singleSchedTrack = ctx.mkBoolConst("single_sched_" + app);
                addConstraint(singleSchedTrack, singleSched, sol);
                break;
            }
        } else {
            // creates constraint to indicate that the a pair of apps are scheduable.
            // else, the two apps cannot be scheduled on the same core.
            for (int i = 0; i < app_ids.size() - 1; i++) {
                String app1 = app_ids.get(i);
                Expr d_i = ctx.mkIntConst(app1 + "_duration");
                Expr d_i_min = ctx.mkGe(d_i, ctx.mkInt(1));
                Expr d_i_eq = ctx.mkEq(d_i, ctx.mkInt(app_durations.get(app1)));
                Expr pr_i = ctx.mkIntConst(app1 + "_priority");
                Expr pr_i_min = ctx.mkGe(pr_i, ctx.mkInt(0));
                Expr pr_i_eq = ctx.mkEq(pr_i, ctx.mkInt(app_priorities.get(app1)));

                for (int j = i + 1; j < app_ids.size(); j++) {
                    String app2 = app_ids.get(j);
                    Expr d_j = ctx.mkIntConst(app2 + "_duration");
                    Expr d_j_min = ctx.mkGe(d_j, ctx.mkInt(1));
                    Expr d_j_eq = ctx.mkEq(d_j, ctx.mkInt(app_durations.get(app2)));
                    Expr pr_j = ctx.mkIntConst(app2 + "_priority");
                    Expr pr_j_min = ctx.mkGe(pr_j, ctx.mkInt(0));
                    Expr pr_j_eq = ctx.mkEq(pr_j, ctx.mkInt(app_priorities.get(app2)));

                    for (int k = 0; k < proc_ids.size(); k++) {
                        String proc = proc_ids.get(k);
                        Expr gcd_pi_pj =
                                ctx.mkIntConst("gcd_" + app1 + "_" + app2 + "_periods_" + proc);
                        Expr gcd_pi_pj_eq =
                                ctx.mkEq(
                                        gcd_pi_pj,
                                        ctx.mkInt(
                                                GCD(
                                                        app_periods
                                                                .get(new Pair(app1, proc))
                                                                .getFirst(),
                                                        app_periods
                                                                .get(new Pair(app2, proc))
                                                                .getFirst())));

                        Expr s_i = ctx.mkIntConst(app1 + "_start_" + proc);
                        Expr s_i_min = ctx.mkGe(s_i, ctx.mkInt(0));
                        Expr s_j = ctx.mkIntConst(app2 + "_start_" + proc);
                        Expr s_j_min = ctx.mkGe(s_j, ctx.mkInt(0));

                        Expr p_i = ctx.mkIntConst(app1 + "_period_" + proc);
                        Expr p_i_min = ctx.mkGe(p_i, ctx.mkInt(1));
                        Expr p_i_eq =
                                ctx.mkEq(
                                        p_i,
                                        ctx.mkInt(
                                                app_periods.get(new Pair(app1, proc)).getFirst()));
                        Expr p_j = ctx.mkIntConst(app2 + "_period_" + proc);
                        Expr p_j_min = ctx.mkGe(p_j, ctx.mkInt(1));
                        Expr p_j_eq =
                                ctx.mkEq(
                                        p_j,
                                        ctx.mkInt(
                                                app_periods.get(new Pair(app2, proc)).getFirst()));

                        // s1 > s2
                        Expr expr2 = ctx.mkGt(s_i, s_j);
                        // s2 > s1
                        Expr expr3 = ctx.mkLt(s_i, s_j);
                        // d1 <= s2 − s1 <= gcd(p1,p2) − d2
                        Expr expr4 =
                                ctx.mkAnd(
                                        ctx.mkLe(d_i, ctx.mkSub(s_j, s_i)),
                                        ctx.mkLe(ctx.mkSub(s_j, s_i), ctx.mkSub(gcd_pi_pj, d_j)));
                        // d2 <= s1 − s2 <= gcd(p1,p2) − d1
                        Expr expr5 =
                                ctx.mkAnd(
                                        ctx.mkLe(d_j, ctx.mkSub(s_i, s_j)),
                                        ctx.mkLe(ctx.mkSub(s_i, s_j), ctx.mkSub(gcd_pi_pj, d_i)));

                        // (s2 > s1) && (d1 <= s2 − s1 <= gcd(p1,p2) − d2)
                        Expr con2 = ctx.mkAnd(expr3, expr4);
                        // (s1 > s2) && (d2 <= s1 − s2 <= gcd(p1,p2) − d1)
                        Expr con3 = ctx.mkAnd(expr2, expr5);

                        // if two apps have start time >= 0, they are schedulable
                        Expr con4 =
                                ctx.mkImplies(ctx.mkAnd(s_i_min, s_j_min), ctx.mkOr(con2, con3));

                        // enforce priority on scheduling
                        // if priority is lower, start time is earlier.
                        // if any priority is 0, skip this rule
                        Expr expr6 = ctx.mkGt(pr_i, ctx.mkInt(0));
                        Expr expr7 = ctx.mkGt(pr_j, ctx.mkInt(0));
                        Expr expr8 = ctx.mkLt(pr_j, pr_i);
                        Expr expr9 = ctx.mkLt(pr_i, pr_j);
                        Expr expr81 = ctx.mkLt(s_j, s_i);
                        Expr expr91 = ctx.mkLt(s_i, s_j);
                        Expr con41 = ctx.mkImplies(ctx.mkAnd(expr6, expr7, expr8), expr81);
                        Expr con42 = ctx.mkImplies(ctx.mkAnd(expr6, expr7, expr9), expr91);

                        Expr schedIJ =
                                ctx.mkAnd(
                                        con4,
                                        con41,
                                        con42,
                                        p_i_eq,
                                        d_i_eq,
                                        pr_i_eq,
                                        p_j_eq,
                                        d_j_eq,
                                        pr_j_eq,
                                        gcd_pi_pj_eq,
                                        p_i_min,
                                        p_j_min,
                                        d_i_min,
                                        d_j_min,
                                        pr_i_min,
                                        pr_j_min);
                        Expr schedIJTrack = ctx.mkBoolConst("sched_" + app1 + "_and_" + app2);
                        addConstraint(schedIJTrack, schedIJ, sol);
                    }
                }
            }
        }

        // The start time are different for the apps on each core.
        for (int k = 0; k < proc_ids.size(); k++) {
            String proc = proc_ids.get(k);
            Expr[] startTimes = new Expr[app_ids.size()];

            for (int i = 0; i < app_ids.size(); i++) {
                String app = app_ids.get(i);
                startTimes[i] = ctx.mkIntConst(app + "_start_" + proc);
            }

            Expr uniqueStartTimesTrack = ctx.mkBoolConst("unique_start_times_multicore");
            addConstraint(uniqueStartTimesTrack, ctx.mkDistinct(startTimes), sol);
        }

        // For all apps, you can schedule 1 app in exactly 1 core
        for (int i = 0; i < app_ids.size(); i++) {
            String app = app_ids.get(i);
            Expr[] startTimesBool = new Expr[proc_ids.size()];

            for (int k = 0; k < proc_ids.size(); k++) {
                String proc = proc_ids.get(k);
                startTimesBool[k] =
                        ctx.mkITE(
                                ctx.mkGe(ctx.mkIntConst(app + "_start_" + proc), ctx.mkInt(0)),
                                ctx.mkInt(1),
                                ctx.mkInt(0));

                // fillup the function Multi_core_scheduling_map
                sol.Add(
                        ctx.mkEq(
                                ctx.mkApp(
                                        funcDecl,
                                        ctx.mkConst(app, typeToSort.get("GPMApp")),
                                        ctx.mkConst(proc, typeToSort.get("ProcessorGPM"))),
                                ctx.mkIntConst(app + "_start_" + proc)));

                // fillup the function App_periods_multi_core
                sol.Add(
                        ctx.mkEq(
                                ctx.mkApp(
                                        funcDecl2,
                                        ctx.mkConst(app, typeToSort.get("GPMApp")),
                                        ctx.mkConst(proc, typeToSort.get("ProcessorGPM"))),
                                ctx.mkIntConst(app + "_period_" + proc)));
            }

            Expr schedulable_app = ctx.mkEq(ctx.mkAdd(startTimesBool), ctx.mkInt(1));
            Expr pred = ctx.mkBoolConst(app + "_is_schedulable_in_a_core");

            assumptions.add(ctx.mkNot(pred));
            Expr schedUniqueCore = ctx.mkBoolConst("schedule_" + app + "_in_unique_core");
            addConstraint(schedUniqueCore, ctx.mkOr(schedulable_app, pred), sol);
        }

        return sol;
    }

    // returns gcd of two numbers
    protected int GCD(int n1, int n2) {
        int gcd = 1;
        for (int i = 1; i <= n1 && i <= n2; ++i) {
            if (n1 % i == 0 && n2 % i == 0) gcd = i;
        }

        return gcd;
    }

    // returns 2 if multi-core app scheduling is compatible (based on given OYSTER
    // properties)
    // returns 1 if single-core app scheduling is compatible (based on given OYSTER
    // properties)
    // returns 0 if no app scheduling is compatible (based on given OYSTER
    // properties)
    protected int checkAppScheduleCompatibility() {
        // check whether user provided correct properties for multi-core scheduling
        boolean flag1;
        // check if processor infos are consistent
        if (proc_ids.size() > 0) {
            flag1 = true;
            for (String proc : proc_ids) {
                if (proc_slots.get(proc) == null) {
                    flag1 = false;
                    break;
                }
            }
        } else {
            flag1 = false;
        }

        // check if app infos are consistent for multi-core (given processor infos are
        // consistent)
        if (flag1) {
            for (String app : app_ids) {
                if (app_rates.get(app) == null
                        || app_durations.get(app) == null
                        || app_priorities.get(app) == null) {
                    flag1 = false;
                    break;
                }
            }
        }

        if (flag1) {
            return 2;
        }

        boolean flag2 = true;
        // check if app infos are consistent for single core(given multi-core is not
        // compatible)
        if (!(flag1)) {
            for (String app : app_ids) {
                if (app_periods.get(app) == null
                        || app_durations.get(app) == null
                        || app_priorities.get(app) == null) {
                    flag2 = false;
                    break;
                }
            }
        }

        if (flag2) {
            return 1;
        } else {
            return 0;
        }
    }

    private boolean isType(String comp, IMATypes type, List<EObject> aadlObjects) {
        for (EObject object : aadlObjects) {
            if (object instanceof SystemImplementation) {
                SystemImplementation sysImpl = (SystemImplementation) object;
                if (sysImpl.getName().equals("IMA.Impl")) {
                    List<Subcomponent> subcomponents = sysImpl.getAllSubcomponents();
                    for (Subcomponent sub : subcomponents) {
                        if (sub.getName().equals(comp)) {
                            SystemType sysType = (SystemType) sub.getComponentType();
                            for (PropertyAssociation pa : sysType.getOwnedPropertyAssociations()) {
                                if (pa.getProperty().getName().equals("componentType")) {
                                    List<ModalPropertyValue> modalValues = pa.getOwnedValues();
                                    for (ModalPropertyValue modalValue : modalValues) {
                                        PropertyExpression pexp = modalValue.getOwnedValue();
                                        if (pexp instanceof NamedValueImpl) {
                                            AbstractNamedValue value =
                                                    ((NamedValueImpl) pexp).getNamedValue();
                                            if (value instanceof EnumerationLiteralImpl) {
                                                String componentyType =
                                                        ((EnumerationLiteralImpl) value)
                                                                .getFullName();
                                                if (componentyType.equals(type.getValue())) {
                                                    return true;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private Optimize addConstraint(Expr track, Expr constraint, Optimize sol) {
        if (useUnsatCore) {
            sol.AssertAndTrack(track, constraint);
        } else {
            sol.Add(constraint);
        }
        return sol;
    }
}
