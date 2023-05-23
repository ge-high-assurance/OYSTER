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
package com.ge.research.osate.oyster.dsl.parsing;

import java.util.HashMap;
import java.util.Map;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.EnumLiteralDeclaration;
import org.eclipse.xtext.Keyword;
import org.eclipse.xtext.nodemodel.ICompositeNode;
import org.eclipse.xtext.nodemodel.INode;
import org.eclipse.xtext.parser.IParseResult;
import org.osate.aadl2.AnnexLibrary;
import org.osate.aadl2.AnnexSubclause;
import org.osate.annexsupport.AnnexHighlighter;
import org.osate.annexsupport.AnnexHighlighterPositionAcceptor;
import org.osate.annexsupport.AnnexUtil;
import org.osate.annexsupport.ParseResultHolder;

/**
 * Perform syntax highlighting/coloring; Osate extension point.
 *
 * <p>This file must be updated whenever the keywords change in the grammar.
 *
 * <p>Osate does not expose the normal Xtext ways of doing this, so our approach is a little bit
 * hackier.
 *
 * <p>We are able to highlight all lexed tokens in this manner.
 *
 * <p>We cannot choose the colors; we are currently just using the default set of colors.
 */
public class OysterAnnexHighlighter implements AnnexHighlighter {
    // Styles maps
    private Map<String, String> stylesAll, stylesSubclause, stylesLibrary;

    public static final String STRING_ID = AnnexHighlighterPositionAcceptor.STRING_ID;
    public static final String KEYWORD_ID = AnnexHighlighterPositionAcceptor.KEYWORD_ID;
    public static final String COMMENT_ID = AnnexHighlighterPositionAcceptor.COMMENT_ID;

    public OysterAnnexHighlighter() {
        /*
         * We construct map keys as follows: - Keywords prefixed with "kw_" - Enums
         * prefixed with "enum_" - Strings as "string" - Comments as "comment"
         */

        stylesAll = new HashMap<>();
        stylesSubclause = new HashMap<>();
        stylesLibrary = new HashMap<>();

        stylesAll.put("string", STRING_ID);
        stylesAll.put("comment", COMMENT_ID);

        stylesSubclause.put("kw_Define", KEYWORD_ID);
        /*
         * stylesSubclause.put("kw_Cabinet", KEYWORD_ID);
         * stylesSubclause.put("kw_Cabinets", KEYWORD_ID); stylesSubclause.put("kw_GPM",
         * KEYWORD_ID); stylesSubclause.put("kw_GPMs", KEYWORD_ID);
         * stylesSubclause.put("kw_RDC", KEYWORD_ID); stylesSubclause.put("kw_RDCs",
         * KEYWORD_ID); stylesSubclause.put("kw_ACS", KEYWORD_ID);
         * stylesSubclause.put("kw_ACSs", KEYWORD_ID);
         * stylesSubclause.put("kw_Application", KEYWORD_ID);
         * stylesSubclause.put("kw_Applications", KEYWORD_ID);
         * stylesSubclause.put("kw_GMS", KEYWORD_ID);
         * stylesSubclause.put("kw_Read-Only-GMS", KEYWORD_ID);
         * stylesSubclause.put("kw_Internal", KEYWORD_ID);
         * stylesSubclause.put("kw_External", KEYWORD_ID);
         * stylesSubclause.put("kw_Connection", KEYWORD_ID);
         * stylesSubclause.put("kw_VirtualLink", KEYWORD_ID);
         * stylesSubclause.put("kw_Sensor", KEYWORD_ID);
         * stylesSubclause.put("kw_Sensors", KEYWORD_ID);
         */

        stylesSubclause.put("kw_Application", KEYWORD_ID);
        stylesSubclause.put("kw_id", KEYWORD_ID);
        stylesSubclause.put("kw_distinct", KEYWORD_ID);
        stylesSubclause.put("kw_and", KEYWORD_ID);
        stylesSubclause.put("kw_cpu", KEYWORD_ID);
        stylesSubclause.put("kw_CPU", KEYWORD_ID);
        stylesSubclause.put("kw_RAM", KEYWORD_ID);
        stylesSubclause.put("kw_ROM", KEYWORD_ID);
        stylesSubclause.put("kw_mem", KEYWORD_ID);
        stylesSubclause.put("kw_ram", KEYWORD_ID);
        stylesSubclause.put("kw_rom", KEYWORD_ID);
        stylesSubclause.put("kw_memory", KEYWORD_ID);
        stylesSubclause.put("kw_MEM", KEYWORD_ID);
        stylesSubclause.put("kw_buffers", KEYWORD_ID);
        stylesSubclause.put("kw_send-bandwidth", KEYWORD_ID);
        stylesSubclause.put("kw_receive-bandwidth", KEYWORD_ID);
        stylesSubclause.put("kw_out-bandwidth", KEYWORD_ID);
        stylesSubclause.put("kw_in-bandwidth", KEYWORD_ID);
        stylesSubclause.put("kw_bandwidth", KEYWORD_ID);
        stylesSubclause.put("kw_amount", KEYWORD_ID);

        stylesSubclause.put("kw_Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_Constraints", KEYWORD_ID);
        stylesSubclause.put("kw_Fixed-Cabinet-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_Fixed-GPM-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_FGC", KEYWORD_ID);
        stylesSubclause.put("kw_FCC", KEYWORD_ID);
        stylesSubclause.put("kw_Separation-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_SC", KEYWORD_ID);
        stylesSubclause.put("kw_Co-Location-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_CLC", KEYWORD_ID);
        stylesSubclause.put("kw_Read-only-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_Read-Only-GMS", KEYWORD_ID);
        stylesSubclause.put("kw_ROC", KEYWORD_ID);
        stylesSubclause.put("kw_applications", KEYWORD_ID);
        stylesSubclause.put("kw_application", KEYWORD_ID);
        stylesSubclause.put("kw_cabinet", KEYWORD_ID);
        stylesSubclause.put("kw_gms", KEYWORD_ID);
        stylesSubclause.put("kw_GMS", KEYWORD_ID);
        stylesSubclause.put("kw_gpm", KEYWORD_ID);
        stylesSubclause.put("kw_Fixed-Location-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_FLC", KEYWORD_ID);
        stylesSubclause.put("kw_Fixed-Location-Constraints", KEYWORD_ID);
        stylesSubclause.put("kw_FLCs", KEYWORD_ID);
        stylesSubclause.put("kw_Utilization-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_UC", KEYWORD_ID);
        stylesSubclause.put("kw_LC", KEYWORD_ID);
        stylesSubclause.put("kw_Location-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_Port-Connection-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_Virtual-Link-Constraint", KEYWORD_ID);
        stylesSubclause.put("kw_PCC", KEYWORD_ID);
        stylesSubclause.put("kw_VLC", KEYWORD_ID);
        stylesSubclause.put("kw_from", KEYWORD_ID);
        stylesSubclause.put("kw_to", KEYWORD_ID);
        stylesSubclause.put("kw_<->", KEYWORD_ID);
        stylesSubclause.put("kw_->", KEYWORD_ID);
        stylesSubclause.put("kw_~>", KEYWORD_ID);

        stylesLibrary.put("kw_Define", KEYWORD_ID);
        /*
         * stylesLibrary.put("kw_Cabinet", KEYWORD_ID); stylesLibrary.put("kw_Cabinets",
         * KEYWORD_ID); stylesLibrary.put("kw_GPM", KEYWORD_ID);
         * stylesLibrary.put("kw_GPMs", KEYWORD_ID); stylesLibrary.put("kw_ACS",
         * KEYWORD_ID); stylesLibrary.put("kw_ACSs", KEYWORD_ID);
         * stylesLibrary.put("kw_RDC", KEYWORD_ID); stylesLibrary.put("kw_RDCs",
         * KEYWORD_ID); stylesLibrary.put("kw_Application", KEYWORD_ID);
         * stylesLibrary.put("kw_Applications", KEYWORD_ID); stylesLibrary.put("kw_GMS",
         * KEYWORD_ID); stylesLibrary.put("kw_Read-Only-GMS", KEYWORD_ID);
         * stylesLibrary.put("kw_Connection", KEYWORD_ID);
         * stylesLibrary.put("kw_Internal", KEYWORD_ID);
         * stylesLibrary.put("kw_External", KEYWORD_ID);
         * stylesLibrary.put("kw_VirtualLink", KEYWORD_ID);
         * stylesLibrary.put("kw_Sensor", KEYWORD_ID); stylesLibrary.put("kw_Sensors",
         * KEYWORD_ID);
         */

        stylesLibrary.put("kw_Application", KEYWORD_ID);
        stylesLibrary.put("kw_id", KEYWORD_ID);
        stylesLibrary.put("kw_distinct", KEYWORD_ID);
        stylesLibrary.put("kw_and", KEYWORD_ID);
        stylesLibrary.put("kw_cpu", KEYWORD_ID);
        stylesLibrary.put("kw_CPU", KEYWORD_ID);
        stylesLibrary.put("kw_RAM", KEYWORD_ID);
        stylesLibrary.put("kw_ROM", KEYWORD_ID);
        stylesLibrary.put("kw_mem", KEYWORD_ID);
        stylesLibrary.put("kw_ram", KEYWORD_ID);
        stylesLibrary.put("kw_rom", KEYWORD_ID);
        stylesLibrary.put("kw_memory", KEYWORD_ID);
        stylesLibrary.put("kw_MEM", KEYWORD_ID);
        stylesLibrary.put("kw_buffers", KEYWORD_ID);
        stylesLibrary.put("kw_send-bandwidth", KEYWORD_ID);
        stylesLibrary.put("kw_receive-bandwidth", KEYWORD_ID);
        stylesLibrary.put("kw_out-bandwidth", KEYWORD_ID);
        stylesLibrary.put("kw_in-bandwidth", KEYWORD_ID);
        stylesLibrary.put("kw_bandwidth", KEYWORD_ID);
        stylesLibrary.put("kw_amount", KEYWORD_ID);

        stylesLibrary.put("kw_Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_Constraints", KEYWORD_ID);
        stylesLibrary.put("kw_Fixed-Cabinet-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_Fixed-GPM-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_FGC", KEYWORD_ID);
        stylesLibrary.put("kw_FCC", KEYWORD_ID);
        stylesLibrary.put("kw_Separation-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_SC", KEYWORD_ID);
        stylesLibrary.put("kw_Co-Location-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_CLC", KEYWORD_ID);
        stylesLibrary.put("kw_Read-only-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_Read-Only-GMS", KEYWORD_ID);
        stylesLibrary.put("kw_ROC", KEYWORD_ID);
        stylesLibrary.put("kw_applications", KEYWORD_ID);
        stylesLibrary.put("kw_application", KEYWORD_ID);
        stylesLibrary.put("kw_cabinet", KEYWORD_ID);
        stylesLibrary.put("kw_gms", KEYWORD_ID);
        stylesLibrary.put("kw_GMS", KEYWORD_ID);
        stylesLibrary.put("kw_gpm", KEYWORD_ID);
        stylesLibrary.put("kw_Fixed-Location-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_FLC", KEYWORD_ID);
        stylesLibrary.put("kw_Fixed-Location-Constraints", KEYWORD_ID);
        stylesLibrary.put("kw_FLCs", KEYWORD_ID);
        stylesLibrary.put("kw_Utilization-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_UC", KEYWORD_ID);
        stylesLibrary.put("kw_LC", KEYWORD_ID);
        stylesLibrary.put("kw_Location-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_Port-Connection-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_Virtual-Link-Constraint", KEYWORD_ID);
        stylesLibrary.put("kw_PCC", KEYWORD_ID);
        stylesLibrary.put("kw_VLC", KEYWORD_ID);
        stylesLibrary.put("kw_from", KEYWORD_ID);
        stylesLibrary.put("kw_to", KEYWORD_ID);
        stylesLibrary.put("kw_<->", KEYWORD_ID);
        stylesLibrary.put("kw_->", KEYWORD_ID);
        stylesLibrary.put("kw_~>", KEYWORD_ID);

        // stylesAll is included in both library and subclause
        stylesSubclause.putAll(stylesAll);
        stylesLibrary.putAll(stylesAll);
    }

    @Override
    public void highlightAnnexLibrary(
            AnnexLibrary library, AnnexHighlighterPositionAcceptor acceptor) {
        highlightAnnex(library, acceptor, stylesLibrary);
    }

    @Override
    public void highlightAnnexSubclause(
            AnnexSubclause subclause, AnnexHighlighterPositionAcceptor acceptor) {
        highlightAnnex(subclause, acceptor, stylesSubclause);
    }

    private void highlightAnnex(
            EObject annex, AnnexHighlighterPositionAcceptor acceptor, Map<String, String> styles) {
        EObject saved = AnnexUtil.getParsedAnnex(annex);
        if (annex != null && saved != null) {
            int offset = AnnexUtil.getAnnexOffset(annex);
            IParseResult parseResult =
                    ParseResultHolder.Factory.INSTANCE.adapt(saved).getParseResult();
            if (parseResult != null) {
                highlight(parseResult.getRootNode(), acceptor, offset, styles);
            }
        }
    }

    private boolean isStringLiteral(String str) {
        return str.startsWith("\"") || str.startsWith("'");
    }

    private boolean isComment(String str) {
        return str.startsWith("--");
    }

    private void highlight(
            ICompositeNode rootNode,
            AnnexHighlighterPositionAcceptor acceptor,
            int offset,
            Map<String, String> styles) {
        String lookup;
        // Process all nodes in the parse tree
        for (INode node : rootNode.getAsTreeIterable()) {
            lookup = null;
            // Build keys for things that we want to highlight
            // There probably won't be anything else for the forseeable future
            if (node.getGrammarElement() instanceof Keyword) {
                lookup = "kw_" + ((Keyword) node.getGrammarElement()).getValue();
            } else if (node.getGrammarElement() instanceof EnumLiteralDeclaration) {
                lookup =
                        "enum_"
                                + ((EnumLiteralDeclaration) node.getGrammarElement())
                                        .getLiteral()
                                        .getValue();
            } else if (isStringLiteral(node.getText())) {
                lookup = "string";
            } else if (isComment(node.getText())) {
                lookup = "comment";
            }

            if (lookup != null && styles.containsKey(lookup)) {
                // Highlight token
                acceptor.addPosition(
                        node.getTotalOffset() - offset, node.getTotalLength(), styles.get(lookup));
            }
        }
    }
}
