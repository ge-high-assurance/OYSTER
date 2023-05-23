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
package com.ge.research.osate.oyster.dsl.ui.quickfix;

/**
 * Custom quickfixes.
 *
 * <p>See https://www.eclipse.org/Xtext/documentation/310_eclipse_support.html#quick-fixes
 */
public class OysterQuickfixProvider
        extends org.osate.xtext.aadl2.properties.ui.quickfix.PropertiesQuickfixProvider {

    //	@Fix(MyJavaValidator.INVALID_NAME)
    //	public void capitalizeName(final Issue issue, IssueResolutionAcceptor acceptor) {
    //		acceptor.accept(issue, "Capitalize name", "Capitalize the name.", "upcase.png", new
    // IModification() {
    //			public void apply(IModificationContext context) throws BadLocationException {
    //				IXtextDocument xtextDocument = context.getXtextDocument();
    //				String firstLetter = xtextDocument.get(issue.getOffset(), 1);
    //				xtextDocument.replace(issue.getOffset(), 1, firstLetter.toUpperCase());
    //			}
    //		});
    //	}

}
