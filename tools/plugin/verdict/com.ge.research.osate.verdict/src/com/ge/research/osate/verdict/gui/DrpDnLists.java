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
package com.ge.research.osate.verdict.gui;

import java.util.ArrayList;
import java.util.List;
import org.osate.aadl2.DataPort;
import org.osate.aadl2.impl.SystemTypeImpl;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// this class stores the contents of all the drop down lists used in Wizard
public class DrpDnLists {

    public final String[] CIA = {"Confidentiality (C)", "Integrity (I)", "Availability (A)"};
    public final String[] CIA_ABBREV = {"C", "I", "A"};
    public final String[] CIA_WITH_NULL = {
        "", "Confidentiality (C)", "Integrity (I)", "Availability (A)"
    };
    public final String[] CIA_ABBEV_WITH_NULL = {"", "C", "I", "A"};
    public final String[] OPERATORS_BUTTON = {" ( ", " ) ", "and", "or ", " ! "};
    public final String[] OPERATORS_EXPR = {"(", ")", " and ", " or ", "!"};
    public final String[] SEVERITY = {
        "Catastrophic", "Hazardous", "Major", "Minor", "No safety effect"
    };
    public String[] inPorts;
    public String[] outPorts;
    public String[] inPortsWithNull;
    public String[] outPortsWithNull;
    public String inStr; // this stores the "Available INPorts" to display in top of StatementEditor
    // window
    public String
            outStr; // this stores the "Available OUTPorts" to display in top of StatementEditor
    // window
    public String autoGenConfidentiality = "";
    public String autoGenIntegrity = "";
    public String autoGenAvailability = "";

    public DrpDnLists(SystemTypeImpl sys) {
        List<DataPort> ports = sys.getOwnedDataPorts();
        List<String> inPortsLabels = new ArrayList<String>();
        List<String> outPortsLabels = new ArrayList<String>();

        for (int i = 0; i < ports.size(); i++) {
            if (ports.get(i).isIn()) {
                inPortsLabels.add(ports.get(i).getFullName());
            } else {
                outPortsLabels.add(ports.get(i).getFullName());
            }
        }

        inPorts = new String[inPortsLabels.size()];
        inPortsWithNull = new String[inPortsLabels.size() + 1];
        outPorts = new String[outPortsLabels.size()];
        outPortsWithNull = new String[outPortsLabels.size() + 1];

        outPortsWithNull[0] = "";
        inPortsWithNull[0] = "";

        inStr = "Available IN Ports: " + "\n";
        outStr = "Available OUT Ports: " + "\n";

        int lineStartID = 0;
        int threshold = 120;
        for (int i = 0; i < inPortsLabels.size(); i++) {
            inPorts[i] = inPortsLabels.get(i);
            inPortsWithNull[i + 1] = inPortsLabels.get(i);
            if (inStr.length() - lineStartID > threshold) {
                lineStartID = inStr.length();
                inStr = inStr + "\n";
            }
            if (i == inPortsLabels.size() - 1) {
                inStr = inStr + (i + 1) + ". " + inPortsLabels.get(i);
            } else {
                inStr = inStr + (i + 1) + ". " + inPortsLabels.get(i) + ", ";
            }
        }

        lineStartID = 0;
        for (int i = 0; i < outPortsLabels.size(); i++) {
            outPorts[i] = outPortsLabels.get(i);
            outPortsWithNull[i + 1] = outPortsLabels.get(i);
            if (outStr.length() - lineStartID > threshold) {
                lineStartID = outStr.length();
                outStr = outStr + "\n";
            }
            if (i == outPortsLabels.size() - 1) {
                outStr = outStr + (i + 1) + ". " + outPortsLabels.get(i);
            } else {
                outStr = outStr + (i + 1) + ". " + outPortsLabels.get(i) + ", ";
            }
        }

        for (int i = 0; i < inPorts.length; i++) {
            if (i != inPorts.length - 1) {
                autoGenConfidentiality = autoGenConfidentiality + inPorts[i] + ":C or ";
                autoGenIntegrity = autoGenIntegrity + inPorts[i] + ":I or ";
                autoGenAvailability = autoGenAvailability + inPorts[i] + ":A or ";
            } else {
                autoGenConfidentiality = autoGenConfidentiality + inPorts[i] + ":C";
                autoGenIntegrity = autoGenIntegrity + inPorts[i] + ":I";
                autoGenAvailability = autoGenAvailability + inPorts[i] + ":A";
            }
        }
        if (inPorts.length == 0) {
            autoGenConfidentiality = "TRUE";
            autoGenIntegrity = "TRUE";
            autoGenAvailability = "TRUE";
        }
    }

    // finds a string from an array of strings
    public int findIndex(String[] strs, String str) {
        int i = -1;
        for (int j = 0; j < strs.length; j++) {
            if (strs[j].equals(str)) {
                i = j;
                break;
            }
        }
        return i;
    }
}
