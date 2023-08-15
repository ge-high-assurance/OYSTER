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
package com.ge.oyster.translators;

/**
 * @author Joyanta Debnath
 */

// this is a helper class to contain all the port-to-port connection information in one object
public class PortConnection {
    final String name;
    final String connectionKind;
    final String direction;
    final String sourceEntityName;
    final String sourceEntityPort;
    final String sourceEntityPortMode;
    final String sourceEntityPortDataType;
    final String destEntityName;
    final String destEntityPort;
    final String destEntityPortMode;
    final String destEntityPortDataType;
    final int bandwidth;

    public PortConnection(
            String name,
            String connectionKind,
            String direction,
            String sourceEntityName,
            String sourceEntityPort,
            String sourceEntityPortMode,
            String sourceEntityPortDataType,
            String destEntityName,
            String destEntityPort,
            String destEntityPortMode,
            String destEntityPortDataType,
            int bandwidth) {
        super();
        this.name = name;
        this.connectionKind = connectionKind;
        this.direction = direction;
        this.sourceEntityName = sourceEntityName;
        this.sourceEntityPort = sourceEntityPort;
        this.sourceEntityPortMode = sourceEntityPortMode;
        this.sourceEntityPortDataType = sourceEntityPortDataType;
        this.destEntityName = destEntityName;
        this.destEntityPort = destEntityPort;
        this.destEntityPortMode = destEntityPortMode;
        this.destEntityPortDataType = destEntityPortDataType;
        this.bandwidth = bandwidth;
    }

    public String generateConnectionKindInfo() {
        return (connectionKind);
    }

    public String generateSourceInfo() {
        return (sourceEntityName);
    }

    public String getConnectionName() {
        return name;
    }

    public String getSource() {
        return sourceEntityName.split("\\.")[0];
    }

    public String generateDestInfo() {
        return (destEntityName);
    }

    public String getSourcePortMode() {
        return sourceEntityPortMode;
    }

    public String getSourcePort() {
        return sourceEntityPort;
    }

    public String getDestinatonPort() {
        return destEntityPort;
    }

    public String generateSourcePortInfo() {
        return (sourceEntityPort + "_" + sourceEntityPortMode + "_" + sourceEntityPortDataType);
    }

    public String generateDestPortInfo() {
        return (destEntityPort + "_" + destEntityPortMode + "_" + destEntityPortDataType);
    }

    public int getBandwidth() {
        return bandwidth;
    }

    public String getSourceEntityType() {
        return sourceEntityPortDataType;
    }

    public String generateConnectionInfo() {
        if (bandwidth > 0) {
            return generateSourceInfo() + "@" + generateDestInfo() + "@" + bandwidth;
        } else {
            return generateSourceInfo() + "@" + generateDestInfo();
        }
    }
}
