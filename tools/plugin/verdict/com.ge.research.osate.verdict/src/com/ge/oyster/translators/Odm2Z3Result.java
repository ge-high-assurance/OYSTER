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
package com.ge.oyster.translators;

import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import java.util.List;
import java.util.Map;
import org.apache.commons.math3.util.Pair;

// object of this class will be used to pass the result of ODM2Z3 translator to the next translator
public class Odm2Z3Result {
    com.microsoft.z3.Model model;
    com.microsoft.z3.Context ctx;
    Map<String, Pair<String, String>> flowNamesToSrcDestInstance;
    List<String> instanceBoundTohostCompName;

    public Odm2Z3Result(
            Model model,
            Context ctx,
            Map<String, Pair<String, String>> flowNamesToSrcDestInstance,
            List<String> instanceBoundTohostCompName) {
        this.model = model;
        this.ctx = ctx;
        this.flowNamesToSrcDestInstance = flowNamesToSrcDestInstance;
        this.instanceBoundTohostCompName = instanceBoundTohostCompName;
    }

    public List<String> getInstanceBoundTohostCompName() {
        return instanceBoundTohostCompName;
    }

    public com.microsoft.z3.Model getModel() {
        return model;
    }

    public com.microsoft.z3.Context getCtx() {
        return ctx;
    }

    public Map<String, Pair<String, String>> getFlowNamesToSrcDestInstance() {
        return flowNamesToSrcDestInstance;
    }
}
