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

import com.ge.verdict.attackdefensecollector.CutSetGenerator.Cache;
import com.ge.verdict.attackdefensecollector.IndentedStringBuilder;
import com.ge.verdict.attackdefensecollector.Prob;
import com.ge.verdict.attackdefensecollector.model.Attackable;
import java.util.Objects;
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;

/**
 * Represents the situation where an attack is dependent on the implementation of a defense. This
 * structure does not store the attack itself; instead, it is embedded in the attack-defense tree in
 * a conjunction next to the dependent attack.
 */
public class DefenseCondition extends ADTree {
    /** The attackable (component/defense) to which this defense condition applies. */
    private Attackable attackable;
    /** The defense property which, when implemented, triggers this defense condition. */
    private String defenseProperty;
    /** The minimum implemented DAL to trigger this defense condition. */
    private int minImplDal;

    public DefenseCondition(Attackable attackable, String defenseProperty, int minImplDal) {
        this.attackable = attackable;
        this.defenseProperty = defenseProperty;
        this.minImplDal = minImplDal;
    }

    public Attackable getAttackable() {
        return attackable;
    }

    public String getDefenseProperty() {
        return defenseProperty;
    }

    public int getMinImplDal() {
        return minImplDal;
    }

    /**
     * Retrieves the actual implemented DAL in the model.
     *
     * @return
     */
    public int getImplDal() {
        String dalStr = attackable.getParentAttributes().get(defenseProperty);
        if (dalStr != null) {
            try {
                return Integer.parseInt(dalStr);
            } catch (NumberFormatException e) {
                throw new RuntimeException(
                        "invalid DAL: "
                                + dalStr
                                + " for defense property "
                                + defenseProperty
                                + " on component/connection "
                                + attackable.getParentName());
            }
        } else {
            // if it's not in the attributes list, then it must be unimplemented
            return 0;
        }
    }

    @Override
    public Prob compute() {
        return getImplDal() >= minImplDal ? Prob.certain() : Prob.impossible();
    }

    @Override
    public ADTree crush() {
        return this;
    }

    @Override
    public void prettyPrint(IndentedStringBuilder builder) {
        builder.append("{");
        builder.append(attackable.getParentName());
        builder.append(":");
        builder.append(defenseProperty);
        builder.append(" >= ");
        builder.append(minImplDal);
        builder.append("}");
    }

    @Override
    public Formula toLogicNg(FormulaFactory factory, Cache cache) {
        return getImplDal() >= minImplDal ? factory.verum() : factory.falsum();
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof DefenseCondition) {
            DefenseCondition otherDefCond = (DefenseCondition) other;
            return attackable.getParentName().equals(otherDefCond.getAttackable().getParentName())
                    && defenseProperty.equals(otherDefCond.getDefenseProperty())
                    && minImplDal == otherDefCond.getMinImplDal();
        }
        return false;
    }

    @Override
    public int hashCode() {
        return Objects.hash(attackable.getParentName(), defenseProperty, minImplDal);
    }
}
