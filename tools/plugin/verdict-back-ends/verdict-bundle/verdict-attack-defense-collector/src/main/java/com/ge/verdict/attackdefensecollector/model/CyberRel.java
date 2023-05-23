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
package com.ge.verdict.attackdefensecollector.model;

import java.util.Optional;

/**
 * A cyber relation. Comprised of a name, an input expression, and an output port concern. The input
 * is optional; if it is not present, it signifies a cyber relation whose output is always an active
 * concern.
 *
 * <p>This class has different constructors for VDM and CSV input. The VDM constructors are more
 * powerful and are intended for use when the VDM input method is implemented. CSV input does not
 * support arbitrary logical expressions, for example.
 */
public class CyberRel {
    /** The name of the cyber relation. */
    private String name;
    /** The optional input expression. */
    private Optional<CyberExpr> input;
    /** The output port concern. */
    private PortConcern output;

    /**
     * Construct a cyber relation with an input expression. (Use for VDM input.)
     *
     * @param name the name of the cyber relation
     * @param input the input expression
     * @param output the output port concern
     */
    public CyberRel(String name, CyberExpr input, PortConcern output) {
        this.name = name;
        this.input = Optional.of(input);
        this.output = output;
    }

    /**
     * Construct a cyber relation with no input. (Use for VDM input.)
     *
     * @param name the name of the cyber relation
     * @param output the output port concern
     */
    public CyberRel(String name, PortConcern output) {
        this.name = name;
        input = Optional.empty();
        this.output = output;
    }

    /**
     * Construct a cyber relation with an input port concern. (Use for CSV input.)
     *
     * @param inputPort the input port name
     * @param inputCia the input port CIA concern
     * @param outputPort the output port name
     * @param outputCia the output port CIA concern
     */
    public CyberRel(String inputPort, CIA inputCia, String outputPort, CIA outputCia) {
        name = "";
        input = Optional.of(new PortConcern(inputPort, inputCia));
        output = new PortConcern(outputPort, outputCia);
    }

    /**
     * Construct a cyber relation with no input. (Use for CSV input.)
     *
     * @param outputPort the output port name
     * @param outputCia the output port CIA concern
     */
    public CyberRel(String outputPort, CIA outputCia) {
        name = "";
        input = Optional.empty();
        output = new PortConcern(outputPort, outputCia);
    }

    /**
     * Get the name of this cyber relation.
     *
     * <p>Note that for cyber relations constructed with the CSV input constructors, the name is the
     * empty string (the CSV format does not provide names).
     *
     * @return the name of the cyber relation
     */
    public String getName() {
        return name;
    }

    /**
     * @return the optional input expression
     */
    public Optional<CyberExpr> getInput() {
        return input;
    }

    /**
     * @return the output port concern
     */
    public PortConcern getOutput() {
        return output;
    }
}
