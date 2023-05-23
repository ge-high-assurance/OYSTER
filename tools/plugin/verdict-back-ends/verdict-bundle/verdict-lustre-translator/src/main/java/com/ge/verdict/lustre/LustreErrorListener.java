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

import java.io.IOException;
import java.nio.file.Paths;
import java.util.Scanner;
import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;

/** Include the source filename and source line in parser error messages. */
public class LustreErrorListener extends BaseErrorListener {
    /** Provides a default instance of {@link LustreErrorListener}. */
    public static final LustreErrorListener INSTANCE = new LustreErrorListener();

    @Override
    public void syntaxError(
            Recognizer<?, ?> recognizer,
            Object offendingSymbol,
            int line,
            int charPositionInLine,
            String msg,
            RecognitionException e) {
        String source = recognizer.getInputStream().getSourceName();
        StringBuilder sb = new StringBuilder();

        addMessage(sb, line, charPositionInLine, msg, source);
        addSourceLine(sb, source, line);
        addPointer(sb, charPositionInLine);
        System.err.println(sb.toString());
    }

    private void addMessage(
            StringBuilder sb, int line, int charPositionInLine, String msg, String source) {
        sb.append(source)
                .append(":")
                .append(line)
                .append(":")
                .append(charPositionInLine)
                .append(" ")
                .append(msg)
                .append("\n");
    }

    private void addSourceLine(StringBuilder sb, String source, int errorLineNumber) {
        String currentLine = "";
        try (Scanner fileScanner = new Scanner(Paths.get(source))) {
            int currentLineNumber = 1;
            while (fileScanner.hasNextLine()) {
                currentLine = fileScanner.nextLine();
                if (currentLineNumber == errorLineNumber) {
                    sb.append(currentLine);
                    break;
                }
                currentLineNumber++;
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        } finally {
            sb.append("\n");
        }
    }

    private void addPointer(StringBuilder sb, int charPositionInLine) {
        for (int i = 0; i < charPositionInLine; i++) {
            sb.append(" ");
        }
        sb.append("^");
    }
}
