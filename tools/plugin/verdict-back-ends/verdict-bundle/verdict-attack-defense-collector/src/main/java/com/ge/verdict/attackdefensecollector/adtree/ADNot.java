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
import java.util.Objects;
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;

/** A negation of an attack-defense tree. */
public class ADNot extends ADTree {
    /** The child attack-defense tree. */
    private ADTree adtree;

    /**
     * Constructs a NOT attack-defense tree.
     *
     * @param adtree the child attack-defense tree
     */
    public ADNot(ADTree adtree) {
        this.adtree = adtree;
    }

    public ADTree child() {
        return adtree;
    }

    @Override
    public ADTree crush() {
        // In either case, make sure to recursively crush the child

        // Double-not elimination
        if (adtree instanceof ADNot) {
            return ((ADNot) adtree).adtree.crush();
        }

        return new ADNot(adtree.crush());
    }

    @Override
    public Prob compute() {
        // Simply NOT the child's probability
        return Prob.not(adtree.compute());
    }

    @Override
    public void prettyPrint(IndentedStringBuilder builder) {
        // NOT child
        builder.append("NOT ");
        adtree.prettyPrint(builder);
    }

    @Override
    public Formula toLogicNg(FormulaFactory factory, CutSetGenerator.Cache cache) {
        return factory.not(adtree.toLogicNg(factory, cache));
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof ADNot && ((ADNot) other).adtree.equals(adtree);
    }

    @Override
    public int hashCode() {
        return Objects.hash(adtree);
    }
}
