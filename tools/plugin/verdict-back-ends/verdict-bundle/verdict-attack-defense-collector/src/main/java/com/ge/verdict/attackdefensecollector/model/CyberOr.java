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

import com.ge.verdict.attackdefensecollector.adtree.ADOr;
import com.ge.verdict.attackdefensecollector.adtree.ADTree;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * A cyber-expression representing the disjunction of other cyber expressions. A CyberOr always
 * contains at least one child expression.
 */
public class CyberOr extends CyberExpr {
    /** The child cyber expressions. */
    private List<CyberExpr> cyberExprs;

    /**
     * Constructs an OR expression.
     *
     * <p>Requires that cyberExprs is not empty.
     *
     * @param cyberExprs
     */
    public CyberOr(List<CyberExpr> cyberExprs) {
        if (cyberExprs.isEmpty()) {
            throw new RuntimeException("Created empty CyberOr");
        }
        this.cyberExprs = cyberExprs;
    }

    /**
     * Returns a mutable list of children. It is the callee's responsibility to not remove the last
     * element from this list, which is a violation of the non-empty property.
     *
     * @return the list of children
     */
    public List<CyberExpr> getCyberExprs() {
        return cyberExprs;
    }

    @Override
    public Optional<ADTree> toADTree(Function<PortConcern, Optional<ADTree>> tracer) {
        // Convert all children into attack-defense trees and OR them together
        List<ADTree> adtrees =
                cyberExprs.stream()
                        .map(expr -> expr.toADTree(tracer))
                        .flatMap(opt -> opt.isPresent() ? Stream.of(opt.get()) : Stream.empty())
                        .collect(Collectors.toList());
        // Only return an attack-defense tree if it has children
        if (adtrees.isEmpty()) {
            return Optional.empty();
        } else {
            return Optional.of(new ADOr(adtrees));
        }
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof CyberOr && cyberExprs.equals(((CyberOr) other).cyberExprs);
    }

    @Override
    public int hashCode() {
        return cyberExprs.hashCode();
    }
}
