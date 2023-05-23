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

import com.ge.verdict.attackdefensecollector.adtree.Attack;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import java.util.Objects;
import java.util.Optional;
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;

/**
 * A raw attack leaf in a defense tree. Each aleaf should have a corresponding dleaf, and if such a
 * corresponding dleaf is found then the aleaf is removed during preparation.
 *
 * <p>If there is no corresponding dleaf, then this aleaf represents an unmitigated attack. As a
 * result, the dtree may not be satisfiable.
 */
public class ALeaf implements DTree {
    /** the encapsulated attack-defense tree attack node */
    private Attack attack;
    /** is set to true when a corresponding dleaf is found */
    private boolean mitigated;

    public ALeaf(Attack attack) {
        this.attack = attack;
    }

    public void setMitigated() {
        mitigated = true;
    }

    public Attack getAttack() {
        return attack;
    }

    public boolean isMitigated() {
        return mitigated;
    }

    @Override
    public String prettyPrint() {
        return "attack(" + attack.toString() + ")";
    }

    @Override
    public BoolExpr toZ3(Context context) {
        if (isMitigated()) {
            throw new RuntimeException(
                    "mitigated ALeaf should not be present, did you call prepare?");
        }

        // an unmitigated attack is a thorn in our side
        return context.mkBool(false);
    }

    @Override
    public BoolExpr toZ3Multi(Context context) {
        return toZ3(context);
    }

    @Override
    public Formula toLogicNG(FormulaFactory factory) {
        if (isMitigated()) {
            throw new RuntimeException(
                    "mitigated ALeaf should not be present, did you call prepare?");
        }

        // an unmitigated attack is a thorn in our side
        return factory.constant(false);
    }

    @Override
    public Optional<DTree> prepare() {
        // remove from tree if mitigated
        return isMitigated() ? Optional.empty() : Optional.of(this);
    }

    @Override
    public String toString() {
        return prettyPrint();
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof ALeaf && ((ALeaf) other).attack.equals(attack);
    }

    @Override
    public int hashCode() {
        return Objects.hash(attack);
    }
}
