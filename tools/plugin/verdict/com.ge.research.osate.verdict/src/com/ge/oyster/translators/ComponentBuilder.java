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

public class ComponentBuilder {
    private String id = "";
    private String type = "";
    private Long cpuUsed = (long) 0;
    private Long cpuProvided = (long) 0;
    private Long ramUsed = (long) 0;
    private Long ramProvided = (long) 0;
    private Long romUsed = (long) 0;
    private Long romProvided = (long) 0;
    private Long memUsed = (long) 0;
    private Long memProvided = (long) 0;
    private Long buffers = (long) 0;
    private Long sendBandwidth = (long) 0;
    private Long receiveBandwidth = (long) 0;
    private Long inBandwidth = (long) 0;
    private Long outBandwidth = (long) 0;
    private Long bandwidth = (long) 0;
    private Long totalNumber = (long) 0;

    ComponentBuilder setID(String s) {
        this.id = s;
        return this;
    }

    ComponentBuilder setType(String s) {
        this.type = s;
        return this;
    }

    ComponentBuilder setCpuUsed(Long l) {
        this.cpuUsed = l;
        return this;
    }

    ComponentBuilder setCpuProvided(Long l) {
        this.cpuProvided = l;
        return this;
    }

    ComponentBuilder setRamUsed(Long l) {
        this.ramUsed = l;
        return this;
    }

    ComponentBuilder setRamProvided(Long l) {
        this.ramProvided = l;
        return this;
    }

    ComponentBuilder setRomUsed(Long l) {
        this.romUsed = l;
        return this;
    }

    ComponentBuilder setRomProvided(Long l) {
        this.romProvided = l;
        return this;
    }

    ComponentBuilder setMemUsed(Long l) {
        this.memUsed = l;
        return this;
    }

    ComponentBuilder setMemProvided(Long l) {
        this.memProvided = l;
        return this;
    }

    ComponentBuilder setBuffers(Long l) {
        this.buffers = l;
        return this;
    }

    ComponentBuilder setSendBandwidth(Long l) {
        this.sendBandwidth = l;
        return this;
    }

    ComponentBuilder setReceiveBandwidth(Long l) {
        this.receiveBandwidth = l;
        return this;
    }

    ComponentBuilder setInBandwidth(Long l) {
        this.inBandwidth = l;
        return this;
    }

    ComponentBuilder setOutBandwidth(Long l) {
        this.outBandwidth = l;
        return this;
    }

    ComponentBuilder setBandwidth(Long l) {
        this.bandwidth = l;
        return this;
    }

    ComponentBuilder setTotalNumber(Long l) {
        this.totalNumber = l;
        return this;
    }

    Component build() {
        return new Component(
                id,
                type,
                cpuUsed,
                cpuProvided,
                ramUsed,
                ramProvided,
                romUsed,
                romProvided,
                memUsed,
                memProvided,
                buffers,
                sendBandwidth,
                receiveBandwidth,
                inBandwidth,
                outBandwidth,
                bandwidth,
                totalNumber);
    }
}
