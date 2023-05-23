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

import com.ge.verdict.vdm.VdmTranslator;
import edu.uiowa.clc.verdict.lustre.VDMLustre2Kind2;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import verdict.vdm.vdm_model.Model;

/** Translate a Verdict data model to or from a Lustre file. */
public class VerdictLustreTranslator extends VdmTranslator {

    /**
     * Marshal a Verdict data model to a Lustre file.
     *
     * @param model Verdict data model to marshal
     * @param outputFile Lustre file to write to
     */
    public static void marshalToLustre(Model model, File outputFile) {
        // Skip and warn if output file can't be created
        if (canWrite(outputFile)) {
            // Open output stream to be written to
            try (OutputStream output = new BufferedOutputStream(new FileOutputStream(outputFile))) {
                String text = VDMLustre2Kind2.translate(model).toString();
                // Last, write text to output stream
                output.write(text.getBytes(StandardCharsets.UTF_8));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }

    /**
     * Unmarshal a Verdict data model from a Lustre file.
     *
     * @param inputFile Lustre file to unmarshal from
     * @return Verdict data model from Lustre file
     */
    public static Model unmarshalFromLustre(File inputFile) {
        // Parse the Lustre file into a parse tree
        LustreParser.ProgramContext programContext =
                VerdictLustreTranslator.parseFromLustre(inputFile);

        // Extract any data from the parse tree with our listener
        VerdictLustreListener extractor = new VerdictLustreListener(inputFile);
        ParseTreeWalker.DEFAULT.walk(extractor, programContext);

        // Return the model extracted from the parse tree
        Model model = extractor.getModel();
        return model;
    }

    /**
     * Parse a Lustre file into a parse tree. Not for public use; intended only for within-package
     * use by VerdictLustreTranslator and VerdictLustreListener.
     *
     * @param inputFile Lustre file to parse
     * @return Parse tree from Lustre file
     */
    static LustreParser.ProgramContext parseFromLustre(File inputFile) {
        try {
            CharStream input = CharStreams.fromFileName(inputFile.getPath());
            LustreLexer lexer = new LustreLexer(input);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            LustreParser parser = new LustreParser(tokens);
            lexer.removeErrorListeners();
            lexer.addErrorListener(LustreErrorListener.INSTANCE);
            parser.removeErrorListeners();
            parser.addErrorListener(LustreErrorListener.INSTANCE);
            return parser.program();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
