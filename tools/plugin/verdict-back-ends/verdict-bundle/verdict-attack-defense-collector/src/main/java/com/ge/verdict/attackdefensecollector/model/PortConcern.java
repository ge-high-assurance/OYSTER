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

import com.ge.verdict.attackdefensecollector.adtree.ADTree;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Function;

/**
 * A cyber expression for a single port concern, the fundamental unit for all cyber expressions.
 * Consists of a port name and a CIA.
 */
public class PortConcern extends CyberExpr {
    /** The name of the port. */
    private String portName;
    /** The CIA concern for the port. */
    private CIA cia;

    /**
     * Construct a port concern.
     *
     * @param portName the name of the port
     * @param cia the CIA concern for the port
     */
    public PortConcern(String portName, CIA cia) {
        this.portName = portName;
        this.cia = cia;
    }

    /**
     * @return the name of the port
     */
    public String getPortName() {
        return portName;
    }

    /**
     * @return the CIA concern for the port
     */
    public CIA getCia() {
        return cia;
    }

    @Override
    public Optional<ADTree> toADTree(Function<PortConcern, Optional<ADTree>> tracer) {
        // Directly apply provided tracer
        // This is the fundamental cyber expression unit, so no more work to do
        // The toADTree() method exists to support AND, OR, and NOT
        return tracer.apply(this);
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof PortConcern) {
            PortConcern otherPortConcern = (PortConcern) other;
            return this.portName.equals(otherPortConcern.portName)
                    && this.cia.equals(otherPortConcern.cia);
        }

        return false;
    }

    @Override
    public int hashCode() {
        return Objects.hash(portName, cia);
    }

    @Override
    public String toString() {
        return portName + ":" + cia.toString();
    }
}
