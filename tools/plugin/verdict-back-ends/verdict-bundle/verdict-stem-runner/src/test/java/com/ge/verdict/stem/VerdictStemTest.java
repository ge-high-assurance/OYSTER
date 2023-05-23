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

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.stream.Collectors;
import org.assertj.core.api.Assertions;
import org.junit.Ignore;
import org.junit.Test;

/** Runs unit tests on a VerdictStem object. */
public class VerdictStemTest {

    @Test
    @Ignore
    public void testSTEM() throws IOException {
        Path controlOutputDir = Paths.get("../../STEM/Output");
        Path testStemDir = Paths.get("target/test-classes/STEM");
        Path testOutputDir = testStemDir.resolve("Output");
        Path testGraphsDir = testStemDir.resolve("Graphs");

        // Remove the output and graphs directories first
        if (Files.exists(testOutputDir)) {
            for (Path path :
                    Files.walk(testOutputDir)
                            .sorted(Comparator.reverseOrder())
                            .collect(Collectors.toList())) {
                Files.delete(path);
            }
        }
        if (Files.exists(testGraphsDir)) {
            for (Path path :
                    Files.walk(testGraphsDir)
                            .sorted(Comparator.reverseOrder())
                            .collect(Collectors.toList())) {
                Files.delete(path);
            }
        }

        // Run SADL on the STEM test project
        VerdictStem stem = new VerdictStem();
        stem.runStem(testStemDir.toFile(), testOutputDir.toFile(), testGraphsDir.toFile());

        // Verify that SADL created some new files with expected contents
        Path controlFile = controlOutputDir.resolve("CAPEC.csv");
        Path testFile = testOutputDir.resolve("CAPEC.csv");
        Assertions.assertThat(testFile).exists();
        String controlData = new String(Files.readAllBytes(controlFile));
        String testData = new String(Files.readAllBytes(testFile));
        Assertions.assertThat(testData).isEqualToNormalizingNewlines(controlData);

        controlFile = controlOutputDir.resolve("Defenses.csv");
        testFile = testOutputDir.resolve("Defenses.csv");
        Assertions.assertThat(testFile).exists();
        controlData = new String(Files.readAllBytes(controlFile));
        testData = new String(Files.readAllBytes(testFile));
        Assertions.assertThat(testData).isEqualToNormalizingNewlines(controlData);

        controlFile = controlOutputDir.resolve("Defenses2NIST.csv");
        testFile = testOutputDir.resolve("Defenses2NIST.csv");
        Assertions.assertThat(testFile).exists();
        controlData = new String(Files.readAllBytes(controlFile));
        testData = new String(Files.readAllBytes(testFile));
        Assertions.assertThat(testData).isEqualToNormalizingNewlines(controlData);

        testFile = testGraphsDir.resolve("Run_sadl_graph.svg");
        Assertions.assertThat(testFile).exists();
    }
}
