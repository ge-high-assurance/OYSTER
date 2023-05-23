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

import com.ge.verdict.attackdefensecollector.AttackDefenseCollector.Result;
import com.ge.verdict.attackdefensecollector.adtree.ADTree;
import java.io.File;
import java.io.IOException;
import java.util.List;

public class Main {
    private static final String USAGE =
            "java -jar {attack-defense-collector.jar} --vdm {STEM output dir} {vdm file} [--inference] [--cut-set]";

    @SuppressWarnings("deprecation")
    public static void main(String[] args) throws IOException, CSVFile.MalformedInputException {
        if (arrayContains(args, "--help")) {
            System.out.println("Usage: " + USAGE);
            return;
        }

        long start = System.currentTimeMillis();
        // this argument parsing is pretty bad. but we shouldn't be using this anyway.
        boolean inference = arrayContains(args, "--inference");
        boolean cutSet = arrayContains(args, "--cut-set");
        AttackDefenseCollector attackDefenseCollector;

        // If "--vdm" is present, we will use the vdm file;
        // otherwise, we will load csv files
        if (arrayContains(args, "--vdm")) {
            attackDefenseCollector =
                    new AttackDefenseCollector(new File(args[1]), new File(args[0]), inference);
        } else {
            attackDefenseCollector = new AttackDefenseCollector(args[0], inference);
        }
        List<Result> results = attackDefenseCollector.perform();
        for (Result result : results) {
            // Convert adtree to cutset only if --cut-set is on.
            ADTree adtree = cutSet ? CutSetGenerator.generate(result.adtree) : result.adtree;

            Logger.println();
            // The default printer includes indentation for clean-ness
            Logger.println(adtree);
            Logger.println();
            Logger.println("CyberReq: " + result.cyberReq.getName());
            Logger.println("Mission: " + result.cyberReq.getMission());
            Logger.println("Severity: " + result.cyberReq.getSeverity());
            Logger.println("Computed: " + result.prob);
            Logger.println(
                    "Successful: "
                            + (Prob.lte(result.prob, result.cyberReq.getSeverity())
                                    ? "Yes"
                                    : "No"));
        }
        Logger.println("Total time: " + (System.currentTimeMillis() - start) + " milliseconds");
    }

    private static boolean arrayContains(String[] arr, String val) {
        for (String elem : arr) {
            if (elem.equals(val)) {
                return true;
            }
        }
        return false;
    }
}
