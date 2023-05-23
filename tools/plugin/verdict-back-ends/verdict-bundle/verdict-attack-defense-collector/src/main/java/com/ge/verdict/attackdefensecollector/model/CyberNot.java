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
package com.ge.verdict.attackdefensecollector.model;

import com.ge.verdict.attackdefensecollector.adtree.ADNot;
import com.ge.verdict.attackdefensecollector.adtree.ADTree;
import java.util.Optional;
import java.util.function.Function;

/** A cyber expression representing the negation of another cyber expression. */
public class CyberNot extends CyberExpr {
    /** The child cyber expression. */
    private CyberExpr cyberExpr;

    /**
     * Constructs a NOT expression.
     *
     * @param cyberExpr the child cyber expression
     */
    public CyberNot(CyberExpr cyberExpr) {
        this.cyberExpr = cyberExpr;
    }

    /**
     * Returns the mutable child cyber expression.
     *
     * @return the child
     */
    public CyberExpr getCyberExpr() {
        return cyberExpr;
    }

    @Override
    public Optional<ADTree> toADTree(Function<PortConcern, Optional<ADTree>> tracer) {
        // Simply convert child and wrap in NOT
        return cyberExpr.toADTree(tracer).map(ADNot::new);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof CyberNot && cyberExpr.equals(((CyberNot) other).cyberExpr);
    }

    @Override
    public int hashCode() {
        return cyberExpr.hashCode();
    }
}
