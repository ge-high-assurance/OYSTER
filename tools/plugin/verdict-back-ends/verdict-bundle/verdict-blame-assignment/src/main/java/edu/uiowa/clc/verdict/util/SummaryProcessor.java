/*
 * BSD 3-Clause License
 * 
 * Copyright (c) 2019-2020, General Electric Company and Board of Trustees of
 * the University of Iowa.
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
package edu.uiowa.clc.verdict.util;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.Vector;

// Reads Kind2 XML output & Generate VerdictProperties.
// PropertyID
// Status
// Source
// Time
// CounterExample ...
// BlameAssignment ...
public class SummaryProcessor {

    public static Vector<VerdictProperty> readResults(File resultFile)
            throws FileNotFoundException {

        FileInputStream resultStream = new FileInputStream(resultFile);
        return readResults(resultStream);
    }

    public static void printLog(File resultFile) throws FileNotFoundException {

        XMLProcessor.parseLog(resultFile);
    }

    public static Vector<VerdictProperty> readResults(InputStream inputStream)
            throws FileNotFoundException {

        // File resultFile = new File("eg1_results.xml");

        Vector<VerdictProperty> properties = XMLProcessor.praseXML(inputStream);

        LOGGY.info("================== Properties Summary==================");
        for (VerdictProperty p : properties) {

            LOGGY.info("Property: " + p.getId() + "  " + p.isSAT());

            if (!p.isSAT() && p.getSource().equals("mcs") && p.getAllWeakAssumptions().size() > 0) {

                LOGGY.info("Weak Assumptions: ");
                LOGGY.info("-----------------");
                printwaReport(p.getAllWeakAssumptions());
                LOGGY.info("--------------------------");
            }
        }
        LOGGY.info("=============== Properties Summary=====================");
        return properties;
    }

    private static void printwaReport(Vector<WeakAssumption> wk_assumptions) {

        for (WeakAssumption wk : wk_assumptions) {
            LOGGY.info(wk.getwId() + " " + wk.getStatus());
        }
    }
}
