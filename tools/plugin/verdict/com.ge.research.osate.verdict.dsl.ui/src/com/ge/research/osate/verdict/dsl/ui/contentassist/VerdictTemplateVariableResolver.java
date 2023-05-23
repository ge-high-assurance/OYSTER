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
package com.ge.research.osate.verdict.dsl.ui.contentassist;

import com.ge.research.osate.verdict.dsl.VerdictUtil;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.jface.text.templates.TemplateVariable;
import org.eclipse.xtext.ui.editor.templates.AbstractTemplateVariableResolver;
import org.eclipse.xtext.ui.editor.templates.XtextTemplateContext;
import org.osate.aadl2.DirectionType;

/**
 * Custom variable resolution for templates. Required because Osate does not support annex
 * templates.
 *
 * <p>Resolves template variables named 'VerdictTemplateVar' and uses the first parameter to
 * determine direction.
 *
 * <p>See also VerdictTemplateProposalProvider and VerdictTemplateContext.
 */
public class VerdictTemplateVariableResolver extends AbstractTemplateVariableResolver {
    private static final String TYPE = "VerdictTemplateVar";

    public VerdictTemplateVariableResolver() {
        super(TYPE, "Verdict");
    }

    @Override
    public List<String> resolveValues(
            TemplateVariable variable, XtextTemplateContext xtextTemplateContext) {
        // Only resolve our own variables
        if (variable.getType().equals(TYPE) && !variable.getVariableType().getParams().isEmpty()) {
            EObject model = xtextTemplateContext.getContentAssistContext().getCurrentModel();

            switch (variable.getVariableType().getParams().get(0)) {
                case "CyberRel.in":
                    return resolvePorts(model, DirectionType.IN);
                case "CyberRel.out":
                    return resolvePorts(model, DirectionType.OUT);
                case "CyberReq.cond":
                    return resolvePorts(model, DirectionType.OUT);
                case "Mission.req":
                    return resolveReqs(model);
            }
        }

        return new ArrayList<>();
    }

    private List<String> resolvePorts(EObject model, DirectionType dir) {
        VerdictUtil.AvailablePortsInfo info = VerdictUtil.getAvailablePorts(model, true, dir);
        return info.availablePorts;
    }

    private List<String> resolveReqs(EObject model) {
        return VerdictUtil.getAllReqs(model).stream()
                .map(req -> "\"" + req + "\"")
                .collect(Collectors.toList());
    }
}
