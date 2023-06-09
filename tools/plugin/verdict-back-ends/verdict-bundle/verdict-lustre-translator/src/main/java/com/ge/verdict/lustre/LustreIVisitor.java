/*
 * BSD 3-Clause License
 * 
 * Copyright (c) 2023, General Electric Company and Board of Trustees of
 * the University of Iowa.
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
package com.ge.verdict.lustre;

import verdict.vdm.vdm_data.DataType;
import verdict.vdm.vdm_lustre.Contract;
import verdict.vdm.vdm_lustre.LustreProgram;
import verdict.vdm.vdm_lustre.Node;
import verdict.vdm.vdm_lustre.NodeParameter;

public interface LustreIVisitor {

    public void visit(LustreProgram program);

    public void visit(Contract contract);

    public void visit(Node node);

    public void visit(NodeParameter nodeparameter);

    public void visit(DataType dataType);
    // public void visit(IteExpr expr);
    // public void visit(IntExpr expr);
    // public void visit(RealExpr expr);
    // public void visit(UnaryExpr expr);
    // public void visit(BinaryExpr expr);
    // public void visit(BooleanExpr expr);
    // public void visit(NodeCallExpr expr);
    //
    // public void visit(LustreEq equation);
    // public void visit(LustreVar var);
    // public void visit(VarIdExpr varId);
    // public void visit(MergeExpr mergeExpr);
    // public void visit(LustreEnumType enumType);
    //
    // public void visit(TupleExpr aThis);
    //
    // public void visit(PrimitiveType aThis);
    //
    // public void visit(ArrayType aThis);
    //
    // public void visit(ArrayExpr aThis);
    //
    // public void visit(LustreAutomaton aThis);
    //
    // public void visit(AutomatonState aThis);
    //
    // public void visit(AutomatonIteExpr aThis);
    //
    // public void visit(ArrayConst aThis);
    //
    // public void visit(EnumConst enumConst);

}
