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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// this class stores content of a mission
public class MissionInfo {
    private String missionID;
    private Set<Integer> rowInTable = new HashSet<Integer>();
    private String verdictStatement;
    private List<String> cyberReqs = new ArrayList<String>();
    private String comment = null;
    private String description = null;

    public void setMissionID(String str) {
        missionID = str;
    }

    public String getMissionID() {
        return missionID;
    }

    public void addToRow(int i) {
        rowInTable.add(i);
    }

    public void removeRow(int i) {
        rowInTable.remove(i);
    }

    public Set<Integer> getRow() {
        return rowInTable;
    }

    public void setRow(Set<Integer> set) {
        rowInTable = set;
    }

    public String getVerdictStatement() {
        return verdictStatement;
    }

    public void setVerdictStatement(String str) {
        this.verdictStatement = str;
    }

    public void addToCyberReqs(String str) {
        cyberReqs.add(str);
    }

    public List<String> getCyberReqs() {
        return cyberReqs;
    }

    public String getComment() {
        return comment;
    }

    public void setComment(String str) {
        this.comment = str;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String str) {
        this.description = str;
    }
}
