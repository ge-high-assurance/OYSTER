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
package com.ge.verdict.test.instrumentor;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import verdict.vdm.vdm_lustre.ContractItem;
import verdict.vdm.vdm_lustre.Expression;
import verdict.vdm.vdm_model.ComponentImpl;
import verdict.vdm.vdm_model.ComponentInstance;
import verdict.vdm.vdm_model.ComponentType;
import verdict.vdm.vdm_model.Model;

public class VerdictTestInstrumentor {
    private Model model;

    public VerdictTestInstrumentor(Model model) {
        this.model = model;
    }

    /**
     * Note: presently only supports one top-level system. If there are multiple, prints a warning
     * and chooses the first one.
     *
     * <p>Also note that instrumentation generates additional system types. But these are added
     * after the one we want. In this case the warning is erroneous.
     *
     * @return the top-level system type in model
     */
    private ComponentType getTopLevelSystemType() {
        Set<ComponentType> subcomps = new HashSet<>();

        for (ComponentImpl impl : model.getComponentImpl()) {
            if (impl.getBlockImpl() != null) {
                for (ComponentInstance comp : impl.getBlockImpl().getSubcomponent()) {
                    if (comp.getSpecification() != null) {
                        subcomps.add(comp.getSpecification());
                    } else if (comp.getImplementation() != null) {
                        subcomps.add(comp.getImplementation().getType());
                    } else {
                        throw new RuntimeException(
                                "ComponentInstance has neither specification nor implementation");
                    }
                }
            }
        }

        List<ComponentType> topLevels = new ArrayList<>();

        for (ComponentType comp : model.getComponentType()) {
            if (!subcomps.contains(comp)) {
                topLevels.add(comp);
            }
        }

        if (topLevels.isEmpty()) {
            throw new RuntimeException("Verdict ATG error: No top-level component found");
        }

        if (topLevels.size() > 1) {
            System.out.println(
                    "Verdict ATG Warning: Multiple top-level systems found, using first one (may be caused by instrumentation)");
        }

        return topLevels.get(0);
    }

    /**
     * Produce one affirmative and one negated guarantee for every cyber requirement in the
     * top-level system of the model.
     */
    public void instrumentTests() {
        ComponentType topLevel = getTopLevelSystemType();
        List<ContractItem> guarantees = topLevel.getContract().getGuarantee();
        List<ContractItem> replaceWith = new ArrayList<>();

        // For every guarantee, produce one positive (equivalent to guarantee)
        // and one negative (logical not of guarantee)

        for (ContractItem guarantee : guarantees) {
            String name = guarantee.getName();

            // Build negated expression
            Expression negExpr = new Expression();
            negExpr.setNot(guarantee.getExpression());

            ContractItem pos = new ContractItem();
            pos.setExpression(guarantee.getExpression());
            pos.setName("pos_" + name);

            ContractItem neg = new ContractItem();
            neg.setExpression(negExpr);
            neg.setName("neg_" + name);

            replaceWith.add(pos);
            replaceWith.add(neg);
        }

        // Remove old guarantees and use our own
        guarantees.clear();
        guarantees.addAll(replaceWith);
    }
}
