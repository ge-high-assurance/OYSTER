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

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import java.util.Optional;
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;

/**
 * Represents a NOT in a defense tree. NOT nodes are not valid in the prepared defense tree, but
 * they may appear in the intermediary defense tree. Preparation cancels out two consecutive nots,
 * resulting in both being removed from the tree.
 */
public final class DNot implements DTree {
    public final DTree child;

    public DNot(DTree child) {
        this.child = child;
    }

    @Override
    public String prettyPrint() {
        return "(not " + child.prettyPrint() + ")";
    }

    @Override
    public BoolExpr toZ3(Context context) {
        // We could encode NOT, but this would invalidate the analysis
        throw new RuntimeException("cannot encode NOT nodes");
    }

    @Override
    public BoolExpr toZ3Multi(Context context) {
        // We could encode NOT, but this would invalidate the analysis
        throw new RuntimeException("cannot encode NOT nodes");
    }

    @Override
    public Formula toLogicNG(FormulaFactory factory) {
        throw new RuntimeException("cannot encode NOT nodes");
    }

    @Override
    public Optional<DTree> prepare() {
        if (child instanceof DNot) {
            // we can flatten by applying the rule (not (not x)) -> x
            return Optional.of(((DNot) child).child);
        } else {
            throw new RuntimeException("unable to flatten NOT node: " + prettyPrint());
        }
    }
}
