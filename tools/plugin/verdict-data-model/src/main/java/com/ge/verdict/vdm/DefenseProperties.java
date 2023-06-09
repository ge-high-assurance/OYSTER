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
package com.ge.verdict.vdm;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public final class DefenseProperties {
    // TODO perhaps further break down by connection vs component

    /*
     * encryptedTransmission: aadlinteger 0 .. 9 => 0 applies to (connection);
     *
     * --- MBAA: --- deviceAuthentication --- IA-3 Device Identification and
     * Authentication --- IA-3 (1) Cryptographic Bidirectional Authentication ---
     * IA-3 specifies general verification of the identity of other connected
     * systems, while enhancement IA-3 (1) establishes --- requirements for mutual
     * verification of identity through cryptographic algorithms. --- CRV: --- The
     * deviceAuthentication cyber-defense property is applied to channels instead of
     * components, which indicates whether or not --- the component originates this
     * connection is authenticated, and if so (values greater than 0) how strong is
     * that. Channels with zero --- deviceAuthentication are susceptible to Network
     * Injection, Remote Code Injection, or Software Virus/Worm/Malware.
     *
     * deviceAuthentication: aadlinteger 0 .. 9 => 0 applies to (connection);
     *
     * --- MBAA: --- sessionAuthenticity --- SC-23 Session Authenticity --- SC-23
     * specifies technical means to maintain the authenticity of communications
     * after establishing initial --- identity. Mitigations focus on unique randomly
     * generated session identifiers. --- CRV: --- The sessionAuthenticity
     * cyber-defense property is applied to channels instead of components, which
     * indicates whether or not --- the connection session is authenticated, and if
     * so (values greater than 0) how strong is that. Channels with zero
     * sessionAuthenticity are --- susceptible to Network Injection, Remote Code
     * Injection, or Software Virus/Worm/Malware.
     *
     * sessionAuthenticity: aadlinteger 0 .. 9 => 0 applies to (connection);
     */
    private static final String[] compProps = {
        "antiJamming",
        "auditMessageResponses",
        "dosProtection",
        "encryptedStorage",
        "failSafe",
        "heterogeneity",
        "inputValidation",
        "logging",
        "memoryProtection",
        "physicalAccessControl",
        "remoteAttestation",
        "removeIdentifyingInformation",
        "resourceAvailability",
        "resourceIsolation",
        "secureBoot",
        "staticCodeAnalysis",
        "strongCryptoAlgorithms",
        "supplyChainSecurity",
        "systemAccessControl",
        "tamperProtection",
        "userAuthentication",
        "zeroize",
    };

    private static final String[] connProps = {
        "encryptedTransmission", "deviceAuthentication", "sessionAuthenticity"
    };

    /**
     * This is a hard-coded list of defense properties. It is kind of disgusting, but it is the best
     * solution for now. In the future, STEM etc. should make the list accessible to Java through
     * some kind of API.
     *
     * <p>This list does need to be updated if CASE_Consolidated_Properties.aadl changes!
     */
    public static final List<String> MBAA_COMP_DEFENSE_PROPERTIES_LIST =
            Collections.unmodifiableList(Arrays.asList(compProps));

    public static final List<String> MBAA_CONN_DEFENSE_PROPERTIES_LIST =
            Collections.unmodifiableList(Arrays.asList(connProps));

    public static final Set<String> MBAA_COMP_DEFENSE_PROPERTIES_SET =
            Collections.unmodifiableSet(new HashSet<>(MBAA_COMP_DEFENSE_PROPERTIES_LIST));

    public static final Set<String> MBAA_CONN_DEFENSE_PROPERTIES_SET =
            Collections.unmodifiableSet(new HashSet<>(MBAA_CONN_DEFENSE_PROPERTIES_LIST));
}
