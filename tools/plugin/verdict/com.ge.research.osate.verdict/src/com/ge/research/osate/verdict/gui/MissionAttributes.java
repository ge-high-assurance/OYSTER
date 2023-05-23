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

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// this class stores the attributes of a "Mission" in MBAS .xml
public class MissionAttributes implements Serializable, Cloneable {

    private static final long serialVersionUID = 1L;
    private String mission;
    private boolean missionSuccess;
    private List<RequirementAttributes> requirements = new ArrayList<RequirementAttributes>();
    private List<MBASSummaryRow> tableContents = new ArrayList<MBASSummaryRow>();

    public void setMission(String str) {
        mission = str;
    }

    public String getMission() {
        return mission;
    }

    public String getMissionStatus() {
        return missionSuccess ? "Succeeded" : "Failed";
    }

    // determines whether mission has succeeded of failed
    public void setRequirements(List<RequirementAttributes> rq) {
        missionSuccess = true;
        requirements = rq;
        for (int i = 0; i < requirements.size(); i++) {
            if (!requirements.get(i).hasSucceeded()) {
                missionSuccess = false;
                break;
            }
        }
    }

    public void updateSuccessWithSafety(List<MBASSafetyResult> safetyResults) {
        if (missionSuccess) {
            for (MBASSafetyResult safetyResult : safetyResults) {
                if (!safetyResult.isSuccessful()) {
                    missionSuccess = false;
                    break;
                }
            }
        }
    }

    public List<RequirementAttributes> getRequirements() {
        return requirements;
    }

    public void setTableContents(List<MBASSummaryRow> list) {
        tableContents = list;
    }

    public List<MBASSummaryRow> getTableContents() {
        return tableContents;
    }
}
