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
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;

/**
 * An attack-defense tree. May be comprised of attacks, defenses, AND, OR and NOT. The fundamental
 * units of an attack-defense tree are attacks and defenses (on particular systems). Defenses must
 * always refer to an existing attack.
 */
public abstract class ADTree {
    /**
     * Compute the probability of an attack through this attack-defense tree.
     *
     * @return the computed probability
     */
    public abstract Prob compute();

    /**
     * Return an equivalent, "crushed" version of this attack-defense tree that preserves the same
     * structure but removes redundant nodes.
     *
     * <p>For current attack-defense trees (with no arbitrarily-complex cyber relations), crushed
     * trees are equivalent to the sum-of-products form.
     *
     * @return the crushed attack-defense tree
     */
    public abstract ADTree crush();

    @Override
    public String toString() {
        // Pretty-print with indentation
        IndentedStringBuilder builder = new IndentedStringBuilder();
        prettyPrint(builder);
        return builder.toString();
    }

    /**
     * Pretty-print this attack-defense tree to the provided IndentedStringBuilder. Child trees
     * should be pretty-printed by invoking prettyPrint() on the children, not by using toString()
     * (because toString() messes up the indentation).
     *
     * @param builder the indented string builder
     */
    public abstract void prettyPrint(IndentedStringBuilder builder);

    /**
     * Convert to a LogicNG formula, storing information in the cache accordingly. Used when
     * generating cut sets.
     *
     * @param factory
     * @param cache
     * @return
     */
    public abstract Formula toLogicNg(FormulaFactory factory, CutSetGenerator.Cache cache);

    @Override
    public abstract boolean equals(Object other);

    @Override
    public abstract int hashCode();
}
