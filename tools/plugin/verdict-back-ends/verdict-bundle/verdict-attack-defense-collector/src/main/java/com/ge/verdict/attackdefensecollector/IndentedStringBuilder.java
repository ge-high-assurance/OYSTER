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
package com.ge.verdict.attackdefensecollector;

/**
 * Wrapper around StringBuilder to support indentation of output.
 *
 * <p>To extract the string at the end, call toString().
 *
 * <p>Will throw exceptions if indentation levels are not matched correctly.
 *
 * <p>This class does not extend StringBuilder because StringBuilder is declared final. As such not
 * all of StringBuilder's methods are implemented.
 */
public class IndentedStringBuilder {
    private StringBuilder builder;
    private int indent;
    private int spacesPerIndent;

    public IndentedStringBuilder(int spacesPerIndent) {
        if (spacesPerIndent < 0) {
            throw new RuntimeException(
                    "Cannot have negative spaces per indent: " + spacesPerIndent);
        }

        builder = new StringBuilder();
        this.spacesPerIndent = spacesPerIndent;
    }

    public IndentedStringBuilder() {
        this(2);
    }

    public int getSpacesPerIndent() {
        return spacesPerIndent;
    }

    public void append(String str) {
        builder.append(str);
    }

    public void append(char chr) {
        builder.append(chr);
    }

    public void append(int i) {
        builder.append(i);
    }

    public void append(float f) {
        builder.append(f);
    }

    public void append(boolean bool) {
        builder.append(bool);
    }

    /**
     * Insert the newline character followed by a number of spaces corresponding to the current
     * indentation level.
     */
    public void newLine() {
        builder.append("\n");
        for (int i = 0; i < indent; i++) {
            builder.append(' ');
        }
    }

    /** Increase the indentation level. Must be followed with a corresponding unindent(). */
    public void indent() {
        indent += spacesPerIndent;
    }

    /** Decrease the indentation level. Must be preceded with a corresponding indent(). */
    public void unindent() {
        indent -= spacesPerIndent;

        if (indent < 0) {
            throw new RuntimeException("Unindented past zero");
        }
    }

    @Override
    public String toString() {
        if (indent != 0) {
            throw new RuntimeException(
                    "IndentedStringBuilder: Leftover indentation in toString: " + indent);
        }

        return builder.toString();
    }
}
