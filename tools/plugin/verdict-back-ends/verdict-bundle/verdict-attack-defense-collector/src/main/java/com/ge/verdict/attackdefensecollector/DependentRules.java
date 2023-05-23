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
package com.ge.verdict.attackdefensecollector;

import com.ge.verdict.attackdefensecollector.adtree.ADOr;
import com.ge.verdict.attackdefensecollector.adtree.ADTree;
import com.ge.verdict.attackdefensecollector.adtree.DefenseCondition;
import com.ge.verdict.attackdefensecollector.model.Attackable;
import com.ge.verdict.attackdefensecollector.model.ConnectionModel;
import com.ge.verdict.attackdefensecollector.model.SystemModel;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * These are hardcoded rules that replicate parts of the STEM rules to encode the possibility of an
 * attack being dependent upon the presence of a defense. The hope is to replace these hardcoded
 * rules with some kind of output from STEM in the future.
 *
 * <p>Note that it is not necessary to encode the entirety of the predicate because all
 * component-attack pairs that STEM reports must already satisfy the non-defense property parts of
 * the predicate.
 */
public class DependentRules {
    public static Optional<ADTree> getComponentDependence(
            SystemModel component, String attackName) {
        List<ADTree> paths = new ArrayList<>();
        switch (attackName) {
            case "CAPEC-21":
                for (ConnectionModel connection : component.getIncomingConnections()) {
                    if ("Untrusted".equals(connection.getAttributes().get("connectionType"))) {
                        // Vul-CAPEC-21-1
                        paths.add(
                                new DefenseCondition(
                                        connection.getAttackable(), "deviceAuthentication", 1));
                    }
                }
                for (ConnectionModel connection : component.getOutgoingConnections()) {
                    if ("Untrusted".equals(connection.getAttributes().get("connectionType"))) {
                        // Vul-CAPEC-21-2
                        paths.add(
                                new DefenseCondition(
                                        connection.getAttackable(), "deviceAuthentication", 1));
                    }
                }
                return mkRet(component.getAttackable(), attackName, paths);
            case "CAPEC-112":
                for (ConnectionModel connection : component.getIncomingConnections()) {
                    // Vul-CAPEC-112-1, Vul-CAPEC-112-3, Vul-CAPEC-112-5
                    paths.add(
                            new DefenseCondition(
                                    connection.getAttackable(), "deviceAuthentication", 1));
                    // Vul-CAPEC-112-2, Vul-CAPEC-112-4, Vul-CAPEC-112-6
                    paths.add(
                            new DefenseCondition(
                                    connection.getAttackable(), "encryptedTransmission", 1));
                }
                return mkRet(component.getAttackable(), attackName, paths);
            case "CAPEC-114":
                for (ConnectionModel connection : component.getIncomingConnections()) {
                    // Vul-CAPEC-114-1, Vul-CAPEC-114-2, Vul-CAPEC-114-3
                    paths.add(
                            new DefenseCondition(
                                    connection.getAttackable(), "deviceAuthentication", 1));
                }
                return mkRet(component.getAttackable(), attackName, paths);
            case "CAPEC-115":
                for (ConnectionModel connection : component.getIncomingConnections()) {
                    // Vul-CAPEC-115-1, Vul-CAPEC-115-2, Vul-CAPEC-115-3
                    paths.add(
                            new DefenseCondition(
                                    connection.getAttackable(), "deviceAuthentication", 1));
                }
                return mkRet(component.getAttackable(), attackName, paths);
            case "CAPEC-390":
                paths.add(
                        new DefenseCondition(
                                component.getAttackable(), "physicalAccessControl", 1));
                return mkRet(component.getAttackable(), attackName, paths);
            default:
                return Optional.empty();
        }
    }

    public static Optional<ADTree> getConnectionDependence(
            ConnectionModel connection, String attackName) {
        List<ADTree> paths = new ArrayList<>();
        // There are currently no such rules
        switch (attackName) {
            default:
                return Optional.empty();
        }
    }

    /**
     * Helper for constructing the return value for the above functions.
     *
     * @param attackable
     * @param attackName
     * @param paths
     * @return
     */
    private static Optional<ADTree> mkRet(
            Attackable attackable, String attackName, List<ADTree> paths) {
        if (paths.isEmpty()) {
            System.err.println(
                    "Strange. Did not find a possible defense dependency for attack "
                            + attackName
                            + " on component/connection "
                            + attackable.getParentName());
            return Optional.empty();
        } else {
            return Optional.of(new ADOr(paths));
        }
    }
}
