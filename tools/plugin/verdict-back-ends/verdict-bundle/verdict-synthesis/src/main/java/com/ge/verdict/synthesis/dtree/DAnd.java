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
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;

/**
 * A conjunction of defense tree nodes, indicating that all one of its children must be satisfied.
 */
public final class DAnd implements DTree {
    public final List<DTree> children;

    public DAnd(List<DTree> children) {
        this.children = Collections.unmodifiableList(children);
    }

    public DAnd(DTree... children) {
        this.children = Arrays.asList(children);
    }

    @Override
    public String prettyPrint() {
        return "("
                + children.stream().map(DTree::prettyPrint).collect(Collectors.joining(" ^ "))
                + ")";
    }

    @Override
    public BoolExpr toZ3(Context context) {
        return context.mkAnd(
                children.stream()
                        .map((child) -> child.toZ3(context))
                        .collect(Collectors.toList())
                        .toArray(new BoolExpr[0]));
    }

    @Override
    public BoolExpr toZ3Multi(Context context) {
        return context.mkAnd(
                children.stream()
                        .map((child) -> child.toZ3Multi(context))
                        .collect(Collectors.toList())
                        .toArray(new BoolExpr[0]));
    }

    @Override
    public Formula toLogicNG(FormulaFactory factory) {
        return factory.and(
                children.stream()
                        .map(child -> child.toLogicNG(factory))
                        .collect(Collectors.toList()));
    }

    @Override
    public Optional<DTree> prepare() {
        return Optional.of(
                new DAnd(
                        children.stream()
                                .map(DTree::prepare)
                                .flatMap(
                                        opt ->
                                                opt.isPresent()
                                                        ? Stream.of(opt.get())
                                                        : Stream.empty())
                                .collect(Collectors.toList())));
    }
}
