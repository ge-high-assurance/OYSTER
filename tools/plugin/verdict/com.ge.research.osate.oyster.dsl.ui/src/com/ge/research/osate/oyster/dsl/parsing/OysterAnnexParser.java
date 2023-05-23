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

import com.ge.research.osate.oyster.dsl.parser.antlr.OysterParser;
import com.ge.research.osate.oyster.dsl.services.OysterGrammarAccess;
import com.ge.research.osate.oyster.dsl.ui.internal.DslActivator;
import com.google.inject.Injector;
import org.osate.aadl2.AnnexLibrary;
import org.osate.aadl2.AnnexSubclause;
import org.osate.aadl2.modelsupport.errorreporting.ParseErrorReporter;
import org.osate.annexsupport.AnnexParseUtil;
import org.osate.annexsupport.AnnexParser;

/**
 * Parse the verdict annex; Osate extension point.
 *
 * <p>An annex library is outside of a system and contains threat models.
 *
 * <p>An annex subclause is inside of a system and contains cyber properties.
 */
public class OysterAnnexParser implements AnnexParser {

    private OysterParser parser;

    protected OysterParser getParser() {
        if (parser == null) {
            Injector injector =
                    DslActivator.getInstance()
                            .getInjector(DslActivator.COM_GE_RESEARCH_OSATE_OYSTER_DSL_OYSTER);
            parser = injector.getInstance(OysterParser.class);
        }
        return parser;
    }

    protected OysterGrammarAccess getGrammarAccess() {
        return getParser().getGrammarAccess();
    }

    @Override
    public AnnexLibrary parseAnnexLibrary(
            String annexName,
            String source,
            String filename,
            int line,
            int column,
            ParseErrorReporter errReporter) {
        // return null;
        return (AnnexLibrary)
                AnnexParseUtil.parse(
                        getParser(),
                        source,
                        getGrammarAccess().getOysterLibraryRule(),
                        filename,
                        line,
                        column,
                        errReporter);
    }

    @Override
    public AnnexSubclause parseAnnexSubclause(
            String annexName,
            String source,
            String filename,
            int line,
            int column,
            ParseErrorReporter errReporter) {
        // return (OysterContractSubclause) AnnexParseUtil.parse(parser, source,
        // getGrammarAccess().getAnnexSubclauseRule(), filename, line, column,
        // errReporter);
        return (AnnexSubclause)
                AnnexParseUtil.parse(
                        getParser(),
                        source,
                        getGrammarAccess().getOysterSubclauseRule(),
                        filename,
                        line,
                        column,
                        errReporter);
    }

    @Override
    public String getFileExtension() {
        return "oyster";
    }
}
