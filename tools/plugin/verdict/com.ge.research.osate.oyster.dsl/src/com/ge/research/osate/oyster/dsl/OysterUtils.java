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
package com.ge.research.osate.oyster.dsl;

import com.ge.research.osate.oyster.dsl.oyster.Oyster;
import com.ge.research.osate.oyster.dsl.oyster.OysterContractSubclause;
import org.osate.aadl2.DefaultAnnexSubclause;

public class OysterUtils {
    /**
     * Get the root AST "Oyster" node from an annex.
     *
     * @param obj some object that might be a Verdict
     * @return the Oyster
     */
    public static Oyster getOyster(Object obj) {
        if (obj == null) {
            return null;
        } else if (obj instanceof Oyster) {
            return (Oyster) obj;
        } else if (obj instanceof OysterContractSubclause) {
            return (Oyster) ((OysterContractSubclause) obj).getContract();
        } else if (obj instanceof DefaultAnnexSubclause) {
            return getOyster(((DefaultAnnexSubclause) obj).getParsedAnnexSubclause());
        } else {
            throw new IllegalArgumentException("Bad Oyster Annex: " + obj.getClass().getName());
        }
    }
}
