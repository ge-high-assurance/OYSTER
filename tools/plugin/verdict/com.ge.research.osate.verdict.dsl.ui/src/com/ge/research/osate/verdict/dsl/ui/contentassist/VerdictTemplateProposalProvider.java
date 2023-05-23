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

import com.google.inject.Inject;
import org.eclipse.jface.text.templates.ContextTypeRegistry;
import org.eclipse.jface.text.templates.Template;
import org.eclipse.jface.text.templates.TemplateContext;
import org.eclipse.jface.text.templates.TemplateProposal;
import org.eclipse.jface.text.templates.persistence.TemplateStore;
import org.eclipse.swt.graphics.Image;
import org.eclipse.xtext.ui.editor.contentassist.ContentAssistContext;
import org.eclipse.xtext.ui.editor.templates.ContextTypeIdHelper;
import org.eclipse.xtext.ui.editor.templates.DefaultTemplateProposalProvider;
import org.eclipse.xtext.ui.editor.templates.XtextTemplateProposal;

/**
 * Shim for supporting templates. Osate does not support annex templates, so we have to do this
 * ourselves.
 */
@SuppressWarnings("deprecation")
public class VerdictTemplateProposalProvider extends DefaultTemplateProposalProvider {
    private static final String CONTEXT_ID_CYBER_REL =
            "com.ge.research.osate.verdict.dsl.Verdict.CyberRel";
    private static final String CONTEXT_ID_CYBER_REQ =
            "com.ge.research.osate.verdict.dsl.Verdict.CyberReq";
    private static final String CONTEXT_ID_MISSION =
            "com.ge.research.osate.verdict.dsl.Verdict.CyberMission";
    private static final String CONTEXT_ID_MODEL =
            "com.ge.research.osate.verdict.dsl.Verdict.Model";

    @Inject
    public VerdictTemplateProposalProvider(
            TemplateStore templateStore, ContextTypeRegistry registry, ContextTypeIdHelper helper) {
        super(templateStore, registry, helper);

        // Allow Verdict to provide variable resolution

        VerdictTemplateVariableResolver resolver = new VerdictTemplateVariableResolver();
        registry.getContextType(CONTEXT_ID_CYBER_REL).addResolver(resolver);
        registry.getContextType(CONTEXT_ID_CYBER_REQ).addResolver(resolver);
        registry.getContextType(CONTEXT_ID_MISSION).addResolver(resolver);
        // We only need this one because the grammar is kind of hacky
        registry.getContextType(CONTEXT_ID_MODEL).addResolver(resolver);
    }

    @Override
    protected TemplateProposal doCreateProposal(
            Template template,
            TemplateContext templateContext,
            ContentAssistContext context,
            Image image,
            int relevance) {

        // Replace the context with our own context
        return new XtextTemplateProposal(
                template,
                new VerdictTemplateContext(templateContext),
                context.getReplaceRegion(),
                image,
                relevance);
    }
}
