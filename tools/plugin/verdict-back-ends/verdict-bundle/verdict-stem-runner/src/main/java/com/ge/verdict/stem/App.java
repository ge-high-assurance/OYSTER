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
package com.ge.verdict.stem;

import java.io.File;
import java.net.URISyntaxException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/** Runs SADL on a Verdict STEM project. */
public class App {

    private static final Logger LOGGER = LoggerFactory.getLogger(App.class);

    /**
     * Runs SADL on the given Verdict STEM project.
     *
     * @param args Command line arguments with path to project
     */
    public static void main(String[] args) throws URISyntaxException {
        // Check that we have one argument
        if (args.length == 1) {

            // Get the Verdict STEM project directory (check it exists and is writable)
            File projectDir = new File(args[0]);
            checkDir(projectDir);

            // By convention, the output and graphs directories will be subdirectories of
            // projectDir
            File outputDir = new File(projectDir, "Output");
            File graphsDir = new File(projectDir, "Graphs");

            // Run SADL on the Verdict STEM project
            VerdictStem stem = new VerdictStem();
            stem.runStem(projectDir, outputDir, graphsDir);
        } else {
            File jarFile =
                    new File(App.class.getProtectionDomain().getCodeSource().getLocation().toURI());
            LOGGER.error("Usage: java -jar {} <project dir>", jarFile.getName());
        }
    }

    /**
     * Checks the given directory exists and is writable.
     *
     * @param directory The path to the directory
     * @throws RuntimeException If the directory doesn't exist or is not writable
     */
    private static void checkDir(File directory) {
        if (!directory.exists()) {
            throw new RuntimeException("Directory does not exist: " + directory);
        }

        if (!directory.canRead()) {
            throw new RuntimeException("Directory is not readable: " + directory);
        }

        if (!directory.canWrite()) {
            throw new RuntimeException("Directory is not writable: " + directory);
        }
    }
}
