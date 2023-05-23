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

import com.ge.verdict.attackdefensecollector.adtree.ADTree;
import java.util.Optional;
import java.util.function.Function;

/**
 * An arbitary logical cyber expression. May be comprised of port concerns, AND, OR, and NOT. The
 * fundamental unit of a cyber expression is the port concern.
 *
 * <p>The primary difference between a cyber expression and an attack-defense tree is that a cyber
 * expression has not fully resolved its port concerns into attack-defense trees. The attack-defense
 * tree construction constructs cyber expressions from attack-defense trees by resolving the port
 * concerns into attack-defense trees (with the toADTree() method). The fundamental units of an
 * attack-defense tree are the attack and the defense.
 */
public abstract class CyberExpr {
    /**
     * Build an attack-defense tree from this cyber expression.
     *
     * @param tracer function for converting port concerns into attack-defense trees
     * @return the optional constructed attack-defense tree
     */
    public abstract Optional<ADTree> toADTree(Function<PortConcern, Optional<ADTree>> tracer);

    @Override
    public abstract boolean equals(Object other);

    @Override
    public abstract int hashCode();
}
