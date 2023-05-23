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

import java.util.Collections;
import java.util.List;

public class MBASSafetyResult {
    private String reqName, defenseType, computedLikelihood, acceptableLikelihood;
    private List<CutsetResult> cutsets;
    private boolean successful;

    public static class CutsetResult {
        public static class Event {
            private String component, eventName;

            public Event(String component, String eventName) {
                this.component = component;
                this.eventName = eventName;
            }

            public String getComponent() {
                return component;
            }

            public String getEventName() {
                return eventName;
            }
        }

        private String likelihood;
        private List<Event> events;

        public CutsetResult(String likelihood, List<Event> events) {
            this.likelihood = likelihood;
            this.events = Collections.unmodifiableList(events);
        }

        public String getLikelihood() {
            return likelihood;
        }

        public List<Event> getEvents() {
            return events;
        }
    }

    public MBASSafetyResult(
            String reqName,
            String defenseType,
            String computedLikelihood,
            String acceptableLikelihood,
            List<CutsetResult> cutsets) {
        this.reqName = reqName;
        this.defenseType = defenseType;
        this.computedLikelihood = computedLikelihood;
        this.acceptableLikelihood = acceptableLikelihood;
        this.cutsets = Collections.unmodifiableList(cutsets);

        try {
            double acceptable = Double.parseDouble(getAcceptableLikelihood());
            double computed = Double.parseDouble(getComputedLikelihood());
            successful = computed <= acceptable;
        } catch (NumberFormatException e) {
            System.out.println(
                    "Error parsing probablities: "
                            + getAcceptableLikelihood()
                            + ", "
                            + getComputedLikelihood());
            successful = false;
        }
    }

    public String getReqName() {
        return reqName;
    }

    public String getDefenseType() {
        return defenseType;
    }

    public String getComputedLikelihood() {
        return computedLikelihood;
    }

    public String getAcceptableLikelihood() {
        return acceptableLikelihood;
    }

    public List<CutsetResult> getCutsets() {
        return cutsets;
    }

    public boolean isSuccessful() {
        return successful;
    }
}
