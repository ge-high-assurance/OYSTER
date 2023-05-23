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
package com.ge.verdict.attackdefensecollector.adtree;

import com.ge.verdict.attackdefensecollector.CutSetGenerator;
import com.ge.verdict.attackdefensecollector.IndentedStringBuilder;
import com.ge.verdict.attackdefensecollector.Prob;
import com.ge.verdict.attackdefensecollector.model.Attackable;
import com.ge.verdict.attackdefensecollector.model.CIA;
import java.util.Locale;
import java.util.Objects;
import org.logicng.formulas.FormulaFactory;
import org.logicng.formulas.Variable;

/** An attack on a system, a fundamental unit of the attack-defense tree. */
public class Attack extends ADTree {
    /** The attackable to which the attack applies. */
    private Attackable attackable;
    /** The name of the attack. */
    private String attackName;
    /** The description of the attack. */
    private String attackDescription;
    /** The probability of attack success. */
    private Prob prob;
    /** The CIA concern affected by the attack. */
    private CIA cia;

    /**
     * Construct an attack.
     *
     * @param system the system to which the attack applies
     * @param attackName the name of the attack
     * @param attackDescription the description of the attack
     * @param prob the probability of attack success
     * @param cia the CIA concern affected by the attack
     */
    public Attack(
            Attackable attackable,
            String attackName,
            String attackDescription,
            Prob prob,
            CIA cia) {
        this.attackable = attackable;
        this.attackName = attackName;
        this.attackDescription = attackDescription;
        this.prob = prob;
        this.cia = cia;
    }

    /**
     * @return the name of the attack
     */
    public String getName() {
        return attackName;
    }

    /**
     * @return the attackable to which the attack applies
     */
    public Attackable getAttackable() {
        return attackable;
    }

    /**
     * @return the description of the attack
     */
    public String getDescription() {
        return attackDescription;
    }

    /**
     * @return the CIA concern of the attack
     */
    public CIA getCia() {
        return cia;
    }

    @Override
    public ADTree crush() {
        // Fundamental, so no crushing to do
        return this;
    }

    @Override
    public Prob compute() {
        return prob;
    }

    @Override
    public void prettyPrint(IndentedStringBuilder builder) {
        // systemName:cia:attackName
        builder.append(
                String.format(
                        Locale.US,
                        "%s:%s:%s",
                        attackable.getParentName(),
                        cia.toString(),
                        attackName));
    }

    @Override
    public Variable toLogicNg(FormulaFactory factory, CutSetGenerator.Cache cache) {
        if (cache.attackToVar.containsKey(this)) {
            return cache.attackToVar.get(this);
        } else {
            String name = "attack_" + toString();
            Variable var = factory.variable(name);
            cache.attackToVar.put(this, var);
            cache.varToAttack.put(name, this);
            return var;
        }
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof Attack) {
            Attack otherAttack = (Attack) other;
            return otherAttack.attackable.isSystem() == attackable.isSystem()
                    && otherAttack.attackable.getParentName().equals(attackable.getParentName())
                    && otherAttack.attackName.equals(attackName)
                    && otherAttack.attackDescription.equals(attackDescription)
                    && otherAttack.prob.equals(prob)
                    && ((otherAttack.cia == null && cia == null)
                            || otherAttack.cia.equals(cia)); // can be bleached
        }

        return false;
    }

    @Override
    public int hashCode() {
        return Objects.hash(attackable.getParentName(), attackName, attackDescription, prob, cia);
    }
}
