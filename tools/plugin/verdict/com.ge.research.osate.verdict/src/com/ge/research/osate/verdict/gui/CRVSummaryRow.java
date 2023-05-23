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

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// This class stores the contents of a row in the CRV Results tables
public class CRVSummaryRow {
    private String propertyName = "";
    private List<String> rowContents = new ArrayList<String>();
    private List<CounterExampleAttributes> counterExample = null;
    private List<CounterExampleAttributes> testCase = null;
    private String validTill = "";

    public void addRow(String str) {
        rowContents.add(str);
    }

    public List<String> getRowContents() {
        return rowContents;
    }

    public void setCounterExample(List<CounterExampleAttributes> ce) {
        counterExample = ce;
    }

    public List<CounterExampleAttributes> getCounterExample() {
        return counterExample;
    }

    public void setValidTill(String str) {
        validTill = str;
    }

    public String getValidTill() {
        return validTill;
    }

    public void setTestCase(List<CounterExampleAttributes> ce) {
        testCase = ce;
    }

    public List<CounterExampleAttributes> getTestCase() {
        return testCase;
    }

    public void setPropertyName(String name) {
        this.propertyName = name;
    }

    public String getPropertyName() {
        return propertyName;
    }

    public boolean hasCounterExample() {
        return counterExample != null && !counterExample.isEmpty();
    }

    public boolean hasAttackType() {
        return rowContents.size() > 2 && rowContents.get(2).length() > 0;
    }

    public boolean hasCompromisedComponents() {
        return rowContents.size() > 3 && rowContents.get(3).length() > 0;
    }

    public boolean hasCompromisedLinks() {
        return rowContents.size() > 4 && rowContents.get(4).length() > 0;
    }

    public boolean hasUncompromisedComponents() {
        return rowContents.size() > 5 && rowContents.get(5).length() > 0;
    }

    public boolean hasUncompromisedLinks() {
        return rowContents.size() > 6 && rowContents.get(6).length() > 0;
    }
}
