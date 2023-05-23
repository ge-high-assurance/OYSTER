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
import com.ge.verdict.attackdefensecollector.Pair;
import com.ge.verdict.attackdefensecollector.Prob;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Objects;
import java.util.Optional;
import org.logicng.formulas.FormulaFactory;
import org.logicng.formulas.Variable;

/**
 * A defense to an attack on a system, a fundamental unit of the attack-defense tree.
 *
 * <p>A single Defense object actually contains multiple "defenses" as produced by STEM. This object
 * encapsulates all defenses associated with a single attack on a given system (so the same attack
 * on a different system has a different Defense object).
 *
 * <p>A defense must always refer to an existing attack on the same system. It is not directly
 * connected to the attack in the attack-defense tree, however, but is instead joined by the
 * following structure: (NOT defense) AND attack
 */
public class Defense extends ADTree {
    /** The attack defended by this defense. */
    private Attack attack;
    /** The DNF of defense leaves (see DefenseLeaf below). */
    private List<List<DefenseLeaf>> defenseDnf;

    /**
     * Each leaf contains a defense name and, if the property is implemented, a pair of the
     * implemented property name and the DAL to which it is implemented.
     */
    public static final class DefenseLeaf extends Pair<String, Optional<Pair<String, Integer>>> {
        public DefenseLeaf(String left, Optional<Pair<String, Integer>> right) {
            super(left, right);
        }
    }

    /**
     * Constructs a defense.
     *
     * <p>DNF clauses may be added with the addDefenseClause() method.
     *
     * <p>Note that the probability is the probability that the defense successfully defends the
     * attack. When loading a defense with a DAL (the probability of a successful attack given the
     * defense), one should first NOT that DAL probability.
     *
     * @param attack the attack defended by the defense
     * @param defenseImpliedProperty the implied property of the attack
     * @param prob the probability that the defense successfully defends the attack
     */
    public Defense(Attack attack) {
        this.attack = attack;
        defenseDnf = new ArrayList<>();
    }

    /**
     * Add a conjunction clause to the defense DNF. Each element is a (name, description) pair.
     *
     * @param clause the clause to add
     */
    public void addDefenseClause(List<DefenseLeaf> clause) {
        defenseDnf.add(clause);
    }

    /**
     * @return the attack defended by this defense
     */
    public Attack getAttack() {
        return attack;
    }

    /**
     * A single Defense object comprises multiple "defenses" as output by STEM. The defenses are in
     * disjunctive-normal form (DNF), i.e. a disjunction of conjunctions of defenses.
     *
     * @return the list of name/description pairs of individual defenses
     */
    public List<List<DefenseLeaf>> getDefenseDnf() {
        return defenseDnf;
    }

    @Override
    public Defense crush() {
        // Fundamental, so no crushing to do
        return this;
    }

    @Override
    public Prob compute() {
        // We flip conjunction and disjunction because attack trees are the complement
        // of defense trees
        Prob total = Prob.certain();
        for (List<DefenseLeaf> term : defenseDnf) {
            Prob termTotal = Prob.impossible();
            for (DefenseLeaf leaf : term) {
                Prob prob =
                        leaf.right.isPresent()
                                ? Prob.fromDal(leaf.right.get().right)
                                : Prob.certain();
                termTotal = Prob.or(termTotal, prob);
            }
            total = Prob.and(total, termTotal);
        }
        // negate because this is complementary
        return Prob.not(total);
    }

    @Override
    public void prettyPrint(IndentedStringBuilder builder) {
        // systemName:(defenseImpliedPropertyFormula)
        builder.append(String.format(Locale.US, "%s:(", attack.getAttackable().getParentName()));

        // Print the DNF
        for (int i = 0; i < defenseDnf.size(); i++) {
            builder.append("(");

            List<DefenseLeaf> term = defenseDnf.get(i);
            for (int j = 0; j < term.size(); j++) {
                DefenseLeaf leaf = term.get(j);
                builder.append(leaf.left);
                builder.append("=");
                if (leaf.right.isPresent()) {
                    builder.append(leaf.right.get().right.toString());
                } else {
                    builder.append("n/a");
                }

                if (j < term.size() - 1) {
                    builder.append(" and ");
                }
            }

            builder.append(")");

            if (i < defenseDnf.size() - 1) {
                builder.append(" or ");
            }
        }

        builder.append(")");
    }

    @Override
    public Variable toLogicNg(FormulaFactory factory, CutSetGenerator.Cache cache) {
        if (cache.defenseToVar.containsKey(this)) {
            return cache.defenseToVar.get(this);
        } else {
            String name = "defense_" + toString();
            Variable var = factory.variable(name);
            cache.defenseToVar.put(this, var);
            cache.varToDefense.put(name, this);
            return var;
        }
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof Defense) {
            Defense otherDefense = (Defense) other;
            return otherDefense.attack.equals(attack) && otherDefense.defenseDnf.equals(defenseDnf);
        }

        return false;
    }

    @Override
    public int hashCode() {
        return Objects.hash(attack, defenseDnf);
    }
}
