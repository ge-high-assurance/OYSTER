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
package com.ge.research.osate.verdict.dsl.ui.labeling;

import com.ge.research.osate.verdict.dsl.verdict.LAnd;
import com.ge.research.osate.verdict.dsl.verdict.LNot;
import com.ge.research.osate.verdict.dsl.verdict.LOr;
import com.ge.research.osate.verdict.dsl.verdict.LPort;
import com.ge.research.osate.verdict.dsl.verdict.Verdict;
import com.ge.research.osate.verdict.dsl.verdict.VerdictContractSubclause;
import com.google.inject.Inject;
import org.eclipse.emf.edit.ui.provider.AdapterFactoryLabelProvider;
import org.eclipse.xtext.ui.label.DefaultEObjectLabelProvider;

/**
 * Provides labels for EObjects.
 *
 * <p>See https://www.eclipse.org/Xtext/documentation/304_ide_concepts.html#label-provider
 *
 * <p>These labels show up primarily in the outline view.
 *
 * <p>TODO For some reason, the labels for LAnd, LOr, etc. do not seem to be working.
 */
public class VerdictLabelProvider extends DefaultEObjectLabelProvider {
    @Inject
    public VerdictLabelProvider(AdapterFactoryLabelProvider delegate) {
        super(delegate);
    }

    String text(VerdictContractSubclause verdict) {
        return "Annex Verdict";
    }

    String text(Verdict verdict) {
        return "Verdict";
    }

    String text(LAnd and) {
        return "and";
    }

    String text(LOr or) {
        return "or";
    }

    String text(LNot not) {
        return "not";
    }

    String text(LPort port) {
        return port.getPort() + ":" + port.getCia().toString();
    }
}
