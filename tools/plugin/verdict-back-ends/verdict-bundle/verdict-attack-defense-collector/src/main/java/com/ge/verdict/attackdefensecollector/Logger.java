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

import java.util.HashSet;
import java.util.Set;

/** Logging. Used to prevent the same warning message being shown multiple times. */
public class Logger {
    /** Log of messages already sent. */
    private static Set<String> messages = new HashSet<>();

    /**
     * Print a message. No prevention of duplicate messages.
     *
     * @param message
     */
    public static void println(String message) {
        System.out.println(message);
    }

    /** Print a blank line. */
    public static void println() {
        println("");
    }

    /**
     * Print an object using obj.toString().
     *
     * @param obj
     */
    public static void println(Object obj) {
        println(obj.toString());
    }

    /**
     * Print a message if it hasn't been printed before.
     *
     * @param message
     */
    private static void showMessage(String message) {
        if (!messages.contains(message)) {
            messages.add(message);
            println(message);
        }
    }

    /**
     * Print a warning message if it hasn't been printed before.
     *
     * @param message
     */
    public static void showWarning(String message) {
        showMessage("Warning: " + message);
    }
}
