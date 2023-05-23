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

public class Component {
    final String id;
    final String type;
    final Long cpuUsed;
    final Long cpuProvided;
    final Long ramUsed;
    final Long ramProvided;
    final Long romUsed;
    final Long romProvided;
    final Long memUsed;
    final Long memProvided;
    final Long buffers;
    final Long sendBandwidth;
    final Long receiveBandwidth;
    final Long inBandwidth;
    final Long outBandwidth;
    final Long bandwidth;
    final Long totalNumber;

    Component(
            String id,
            String type,
            Long cpuUsed,
            Long cpuProvided,
            Long ramUsed,
            Long ramProvided,
            Long romUsed,
            Long romProvided,
            Long memUsed,
            Long memProvided,
            Long buffers,
            Long sendBandwidth,
            Long receiveBandwidth,
            Long inBandwidth,
            Long outBandwidth,
            Long bandwidth,
            Long totalNumber) {
        this.id = id;
        this.type = type;
        this.cpuUsed = cpuUsed;
        this.cpuProvided = cpuProvided;
        this.ramUsed = ramUsed;
        this.ramProvided = ramProvided;
        this.romUsed = romUsed;
        this.romProvided = romProvided;
        this.memUsed = memUsed;
        this.memProvided = memProvided;
        this.buffers = buffers;
        this.sendBandwidth = sendBandwidth;
        this.receiveBandwidth = receiveBandwidth;
        this.inBandwidth = inBandwidth;
        this.outBandwidth = outBandwidth;
        this.bandwidth = bandwidth;
        this.totalNumber = totalNumber;
    }
}
