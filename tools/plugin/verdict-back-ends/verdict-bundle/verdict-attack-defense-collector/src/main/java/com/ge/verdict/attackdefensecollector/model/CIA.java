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

/** Confidentiality, Integrity, or Availability (the CIA triad). */
public enum CIA {
    C("Confidentiality"),
    I("Integrity"),
    A("Availability");

    private String fullName;

    private CIA(String fullName) {
        this.fullName = fullName;
    }

    /**
     * @return the full name (e.g. "Integrity" instead of just "I").
     */
    public String getFullName() {
        return fullName;
    }

    /**
     * Constructs a CIA from a string. Ignores case and accepts short form (e.g. "I") and long form
     * (e.g. "Integrity").
     *
     * @param str the string to parse
     * @return the parsed CIA, or empty
     */
    public static Optional<CIA> fromStringOpt(String str) {
        switch (str.toLowerCase()) {
            case "c":
            case "confidentiality":
                return Optional.of(C);
            case "i":
            case "integrity":
                return Optional.of(I);
            case "a":
            case "availability":
                return Optional.of(A);
            default:
                return Optional.empty();
        }
    }

    /**
     * Constructs a CIA from a string. Same as fromStringOpt(), except throws an exception instead
     * of returning an empty option.
     *
     * @param str the string to parse
     * @return the parsed CIA
     */
    public static CIA fromString(String str) {
        Optional<CIA> opt = fromStringOpt(str);
        if (opt.isPresent()) {
            return opt.get();
        } else {
            throw new RuntimeException("Invalid CIA string: " + str);
        }
    }

    /**
     * Constructs a CIA from the first valid CIA string in a sequence of strings. Throws an
     * exception if none of the strings is a valid CIA string.
     *
     * @param strs the possible strings to parse
     * @return the parsed CIA
     */
    public static CIA fromStrings(String... strs) {
        // Check all
        for (String str : strs) {
            Optional<CIA> opt = fromStringOpt(str);
            if (opt.isPresent()) {
                // Return first one found
                return opt.get();
            }
        }

        // None found
        StringBuilder msg = new StringBuilder();
        msg.append("No valid CIA found in strings: ");
        for (String str : strs) {
            msg.append(str);
            msg.append(",");
        }
        throw new RuntimeException(msg.toString());
    }
}
