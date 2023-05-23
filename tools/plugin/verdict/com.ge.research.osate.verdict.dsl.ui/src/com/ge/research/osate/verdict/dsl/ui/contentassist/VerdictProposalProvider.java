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

import com.ge.research.osate.verdict.dsl.ThreatModelUtil;
import com.ge.research.osate.verdict.dsl.VerdictUtil;
import com.ge.research.osate.verdict.dsl.type.VerdictField;
import com.ge.research.osate.verdict.dsl.type.VerdictType;
import com.ge.research.osate.verdict.dsl.type.VerdictVariable;
import com.ge.research.osate.verdict.dsl.verdict.ThreatEqualContains;
import com.ge.research.osate.verdict.dsl.verdict.Var;
import com.google.inject.Inject;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.Assignment;
import org.eclipse.xtext.RuleCall;
import org.eclipse.xtext.resource.impl.ResourceDescriptionsProvider;
import org.eclipse.xtext.ui.editor.contentassist.ContentAssistContext;
import org.eclipse.xtext.ui.editor.contentassist.ICompletionProposalAcceptor;

/**
 * See https://www.eclipse.org/Xtext/documentation/304_ide_concepts.html#content-assist on how to
 * customize the content assistant.
 */
public class VerdictProposalProvider extends AbstractVerdictProposalProvider {
    @Inject private ResourceDescriptionsProvider indexProvider;

    /**
     * Forces a set of proposal strings to appear in the provided order rather than alphabetical
     * order.
     *
     * @param proposals
     * @param context
     * @param acceptor
     */
    private void acceptOrderedProposals(
            String[] proposals,
            ContentAssistContext context,
            ICompletionProposalAcceptor acceptor) {

        // Note that this will have to be changed to cause proposals to
        // appear above the default ones (normal priority is like 500 or something)
        int base = 0;

        for (int i = 0; i < proposals.length; i++) {
            // Assign an arbitrary priority that forces ordering
            acceptor.accept(
                    createCompletionProposal(
                            proposals[i],
                            null,
                            null,
                            base + proposals.length - i,
                            context.getPrefix(),
                            context));
        }
    }

    @Override
    public void complete_LPort(
            EObject model,
            RuleCall ruleCall,
            ContentAssistContext context,
            ICompletionProposalAcceptor acceptor) {

        // Available ports for this system (in or out, depending on context)

        if (model != null) {
            VerdictUtil.AvailablePortsInfo info = VerdictUtil.getAvailablePorts(model, true);
            for (String port : info.availablePorts) {
                acceptor.accept(createCompletionProposal(port, context));
            }
        }
    }

    @Override
    public void complete_CIA(
            EObject model,
            RuleCall ruleCall,
            ContentAssistContext context,
            ICompletionProposalAcceptor acceptor) {

        String[] props = {"C", "I", "A", "Confidentiality", "Integrity", "Availability"};

        // C, I, A

        // Force correct ordering
        acceptOrderedProposals(props, context, acceptor);
    }

    @Override
    public void completeCyberMissionBlock_CyberReqs(
            EObject model,
            Assignment assignment,
            ContentAssistContext context,
            ICompletionProposalAcceptor acceptor) {

        // Available cyber requirements

        if (model != null) {
            Set<String> cyberReqs = VerdictUtil.getAllReqs(model);
            for (String req : cyberReqs) {
                acceptor.accept(createCompletionProposal("\"" + req + "\"", context));
            }
        }
    }

    // -------------------------------
    // -------- THREAT MODELS --------
    // -------------------------------

    @Override
    public void completeIntro_Type(
            EObject model,
            Assignment assignment,
            ContentAssistContext context,
            ICompletionProposalAcceptor acceptor) {

        // system, connection, port (can be extended by registering additional types)

        if (model != null
                && model.eResource() != null
                && model.eResource().getResourceSet() != null) {
            LinkedHashMap<String, VerdictType> types =
                    ThreatModelUtil.getTypes(model, indexProvider);
            for (String type : types.keySet()) {
                acceptor.accept(createCompletionProposal(type, context));
            }
        }
    }

    @Override
    public void complete_Var(
            EObject model,
            RuleCall ruleCall,
            ContentAssistContext context,
            ICompletionProposalAcceptor acceptor) {

        // Completes with variables that are in scope (introduced by intro clauses, i.e.
        // forall and exists)

        EObject scopeParent =
                ThreatModelUtil.getContainerForClasses(
                        model, ThreatModelUtil.VAR_FIELD_SCOPE_PARENT_CLASSES);

        if (scopeParent != null
                && scopeParent.eResource() != null
                && scopeParent.eResource().getResourceSet() != null) {
            // Get all variables in scope
            List<VerdictVariable> scope = ThreatModelUtil.getScope(scopeParent, indexProvider);
            for (VerdictVariable var : scope) {
                acceptor.accept(createCompletionProposal(var.getId(), context));
            }
        }

        // Completes enum constant values (e.g. "in" and "out" for port's direction
        // field)

        if (model != null) {
            // Get equal/contains parent
            EObject container = model;
            while (container != null && !(container instanceof ThreatEqualContains)) {
                container = container.eContainer();
            }
            if (container instanceof ThreatEqualContains) {
                ThreatEqualContains equalContains = (ThreatEqualContains) container;
                List<String> suggestions = null;

                if (equalContains.isEqual()
                        && equalContains.getLeft() != null
                        && equalContains.getLeft().eResource() != null
                        && equalContains.getLeft().eResource().getResourceSet() != null) {

                    // We know the left side, so predict based on that
                    ThreatModelUtil.FieldTypeResult res =
                            ThreatModelUtil.getVarType(equalContains.getLeft(), indexProvider);
                    if (res.type.isPresent()) {
                        suggestions = res.type.get().getValueSuggestions();
                    }
                }
                if (equalContains.isEqual()
                        && equalContains.getRight() != null
                        && equalContains.getRight().eResource() != null
                        && equalContains.getRight().eResource().getResourceSet() != null) {

                    // We know the right side, so predict based on that
                    ThreatModelUtil.FieldTypeResult res =
                            ThreatModelUtil.getVarType(equalContains.getRight(), indexProvider);
                    if (res.type.isPresent()) {
                        suggestions = res.type.get().getValueSuggestions();
                    }
                }

                if (suggestions != null) {
                    for (String suggestion : suggestions) {
                        // Higher priority (1100) to make them display above the vars
                        acceptor.accept(
                                createCompletionProposal(
                                        suggestion,
                                        null,
                                        null,
                                        1100,
                                        context.getPrefix(),
                                        context));
                    }
                }
            }
        }
    }

    @Override
    public void complete_ThreatEqualContains(
            EObject model,
            RuleCall ruleCall,
            ContentAssistContext context,
            ICompletionProposalAcceptor acceptor) {

        // The first thing in an equal/contains expression might be a var
        complete_Var(model, ruleCall, context, acceptor);
    }

    @Override
    public void completeVar_Ids(
            EObject model,
            Assignment assignment,
            ContentAssistContext context,
            ICompletionProposalAcceptor acceptor) {

        // Completes fields of vars (and fields of fields of vars, etc.)

        if (model != null
                && model.eResource() != null
                && model.eResource().getResourceSet() != null
                && model instanceof Var) {
            ThreatModelUtil.FieldTypeResult res =
                    ThreatModelUtil.getVarType((Var) model, indexProvider);
            if (res.type.isPresent()) {
                for (VerdictField field : res.type.get().getFields()) {
                    acceptor.accept(createCompletionProposal(field.getName(), context));
                }
            }
        }
    }

    @Override
    public void completeThreatDefenseBlock_Threats(
            EObject model,
            Assignment assignment,
            ContentAssistContext context,
            ICompletionProposalAcceptor acceptor) {

        // Complete threat model IDs

        if (model != null) {
            Set<String> threats = ThreatModelUtil.getDefinedThreatModels(model);
            for (String threat : threats) {
                acceptor.accept(createCompletionProposal("\"" + threat + "\"", context));
            }
        }
    }
}
