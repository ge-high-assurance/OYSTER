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

import com.ge.verdict.attackdefensecollector.adtree.ADAnd;
import com.ge.verdict.attackdefensecollector.adtree.ADNot;
import com.ge.verdict.attackdefensecollector.adtree.ADOr;
import com.ge.verdict.attackdefensecollector.adtree.ADTree;
import com.ge.verdict.attackdefensecollector.adtree.Attack;
import com.ge.verdict.attackdefensecollector.adtree.Defense;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.logicng.formulas.And;
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;
import org.logicng.formulas.Literal;
import org.logicng.formulas.Not;
import org.logicng.formulas.Or;
import org.logicng.formulas.Variable;
import org.logicng.transformations.dnf.DNFFactorization;

/** Generate cut sets. Not currently used. */
public class CutSetGenerator {
    /**
     * Cache used internally by the cut set generator. Prevents creation of duplicate LogicNG
     * variables and allows for reconstructing the attack-defense tree at the end.
     */
    public static class Cache {
        public Map<Attack, Variable> attackToVar = new LinkedHashMap<>();
        public Map<String, Attack> varToAttack = new LinkedHashMap<>();
        public Map<Defense, Variable> defenseToVar = new LinkedHashMap<>();
        public Map<String, Defense> varToDefense = new LinkedHashMap<>();
    }

    /**
     * Perform cut set generation for the given attack-defense tree.
     *
     * @param adtree
     * @return
     */
    public static ADTree generate(ADTree adtree) {
        FormulaFactory factory = new FormulaFactory();
        Cache cache = new Cache();

        Formula formula = adtree.toLogicNg(factory, cache);

        long startTime = System.currentTimeMillis();

        // this is terribly inefficient for any non-trivial system
        // and it has not yet been observed to terminate
        // Formula minimal = QuineMcCluskeyAlgorithm.compute(formula);

        // this should be inefficient too, but it finishes trivially for trees already
        // in DNF form
        // not yet tested on non-DNF trees because we don't have a model that produces
        // one
        Formula minimal = (new DNFFactorization()).apply(formula, false);

        // for comparing approaches
        System.out.println(
                "converted to DNF in " + (System.currentTimeMillis() - startTime) + " ms");

        return extract(minimal, cache);
    }

    /**
     * Converts a LogicNG formula back into an attack-defense tree.
     *
     * @param formula
     * @param cache
     * @return
     */
    private static ADTree extract(Formula formula, Cache cache) {
        if (formula instanceof And) {
            List<ADTree> children = new ArrayList<>();
            for (Formula child : formula) {
                children.add(extract(child, cache));
            }
            return new ADAnd(children);
        } else if (formula instanceof Or) {
            List<ADTree> children = new ArrayList<>();
            for (Formula child : formula) {
                children.add(extract(child, cache));
            }
            return new ADOr(children);
        } else if (formula instanceof Not) {
            return new ADNot(extract(((Not) formula).operand(), cache));
        } else if (formula instanceof Literal) {
            String name = ((Literal) formula).name();
            if (cache.varToAttack.containsKey(name)) {
                return cache.varToAttack.get(name);
            } else if (cache.varToDefense.containsKey(name)) {
                return cache.varToDefense.get(name);
            } else {
                throw new RuntimeException("got an unknown literal: " + name);
            }
        } else {
            throw new RuntimeException(
                    "got unexpected dnf node: " + formula.getClass().getCanonicalName());
        }
    }
}
