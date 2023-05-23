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
package com.ge.verdict.synthesis.dtree;

import com.ge.verdict.attackdefensecollector.adtree.DefenseCondition;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import java.util.Objects;
import java.util.Optional;
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;

/**
 * Represents a conditional dependence on the implementation of a defense property. Used under an
 * AND with a defense, where the defense defends against an attack that is predicated on the
 * implementation of the defense within this node.
 *
 * <p>This node by itself represents something of the form (d >= x) in the encoded SMT, where d is
 * some defense property and x is a minimum DAL.
 *
 * <p>This node supports an arbitrary minimum DAL to "trigger" the defense condition, but in
 * practice we only ever use a minimum DAL of 1 (i.e. not zero).
 */
public class DCondition implements DTree {
    /** the encapsulated attack-defense tree defense condition node */
    public final DefenseCondition defenseCond;

    private DLeaf.ComponentDefense compDef;

    public DCondition(DefenseCondition defenseCond) {
        this.defenseCond = defenseCond;
    }

    /**
     * Connect this dcondition to a component-defense pair.
     *
     * @param compDef
     */
    public void setCompDef(DLeaf.ComponentDefense compDef) {
        if (this.compDef != null) {
            throw new RuntimeException("compDef has already been set");
        }
        if (!(compDef.component.equals(defenseCond.getAttackable().getParentName())
                && compDef.defenseProperty.equals(defenseCond.getDefenseProperty()))) {
            throw new RuntimeException("compDef and defenseCond do not match");
        }
        this.compDef = compDef;
    }

    @Override
    public String prettyPrint() {
        return "{"
                + defenseCond.getAttackable().getParentName()
                + ":"
                + defenseCond.getDefenseProperty()
                + " >= "
                + defenseCond.getMinImplDal()
                + "}";
    }

    @Override
    public BoolExpr toZ3(Context context) {
        throw new RuntimeException("DCondition only supported by Z3-multi");
    }

    @Override
    public BoolExpr toZ3Multi(Context context) {
        if (compDef != null) {
            // Note that we use < instead of >= because the defense tree is inverted
            // compared to the
            // attack-defense tree
            return context.mkLt(
                    compDef.toZ3Multi(context),
                    DLeaf.fractionToZ3(compDef.dalToRawCost(defenseCond.getMinImplDal()), context));
        } else {
            throw new RuntimeException("DCondition missing comp def: " + prettyPrint());
        }
    }

    @Override
    public Formula toLogicNG(FormulaFactory factory) {
        throw new RuntimeException("DCondition only supported by Z3-multi");
    }

    @Override
    public Optional<DTree> prepare() {
        return Optional.of(this);
    }

    @Override
    public int hashCode() {
        return Objects.hash(defenseCond);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof DCondition && defenseCond.equals(((DCondition) other).defenseCond);
    }
}
