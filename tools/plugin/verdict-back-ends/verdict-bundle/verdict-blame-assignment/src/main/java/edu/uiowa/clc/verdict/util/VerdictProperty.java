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

import java.util.Vector;

public class VerdictProperty {

    private String pId;
    private String source;
    private boolean sat_status;
    private String time;

    private Vector<WeakAssumption> wk_assumptions;

    public VerdictProperty() {
        wk_assumptions = new Vector<WeakAssumption>();
        // false_assumptions = new Vector<WeakAssumption>();
    }

    public String getId() {
        return pId;
    }

    public void setId(String pId) {
        this.pId = pId;
    }

    public String getSource() {
        return source;
    }

    public void setSource(String source) {
        this.source = source;
    }

    public boolean isSAT() {
        return sat_status;
    }

    public void setStatus(boolean sat_status) {
        this.sat_status = sat_status;
    }

    public String getTime() {
        return time;
    }

    public void setTime(String time) {
        this.time = time;
    }

    public Vector<WeakAssumption> getAllWeakAssumptions() {
        return this.wk_assumptions;
    }

    public Vector<String> getTrueWeakAssumptions() {

        Vector<String> wks = new Vector<String>();

        for (WeakAssumption wk : this.wk_assumptions) {
            if (wk.isTrue()) {
                String w_value = wk.getwId();
                wks.add(w_value);
            }
        }

        return wks;
    }

    public Vector<String> getFalseWeakAssumptions() {

        Vector<String> wks = new Vector<String>();

        for (WeakAssumption wk : this.wk_assumptions) {
            if (!wk.isTrue()) {
                String w_value = wk.getwId();
                wks.add(w_value);
            }
        }

        return wks;
    }

    public boolean isSatisfied(String wk_Id) {

        boolean sat_status = false;

        boolean containsId = false;
        for (WeakAssumption wk : this.wk_assumptions) {
            String w_value = wk.getwId();
            if (w_value.equals(wk_Id)) {
                containsId = true;
                break;
            }
        }

        // this.wk_assumptions.contains(wk_Id) is not likely to work (String and
        // WeakAssumption are
        // different types)
        if (containsId) {
            for (WeakAssumption wk : this.wk_assumptions) {
                if (wk.isTrue()) {
                    return true;
                }
            }
        }
        return sat_status;
    }

    public void addAssumption(String wId, boolean status) {

        WeakAssumption wk = new WeakAssumption(wId, status);
        this.wk_assumptions.add(wk);
    }
}
