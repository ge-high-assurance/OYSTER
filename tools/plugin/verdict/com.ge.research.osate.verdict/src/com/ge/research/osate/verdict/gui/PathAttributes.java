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
import java.util.stream.Collectors;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// this class stores the contents of a "Path" element in the MBAS .xml
public class PathAttributes implements Serializable, Cloneable {

    public static class ComponentData {
        private String component;
        private String data;

        public ComponentData(String component, String data) {
            this.component = component;
            this.data = data;
        }

        public String getComponent() {
            return component;
        }

        public String getData() {
            return data;
        }

        public String getJoined() {
            return component + ":" + data;
        }
    }

    private static final long serialVersionUID = 1L;
    private String likelihood;
    private List<ComponentData> componentAttacks = new ArrayList<>();
    private List<ComponentData> componentSuggestedDefenses = new ArrayList<>();
    private List<ComponentData> componentSuggestedDefensesProfile = new ArrayList<>();
    private List<ComponentData> componentImplDefenses = new ArrayList<>();

    public void setLikelihood(String str) {
        likelihood = str;
    }

    public String getLikelihood() {
        return likelihood;
    }

    public void setComponentAttacks(List<ComponentData> componentAttacks) {
        this.componentAttacks = componentAttacks;
    }

    public List<ComponentData> getComponentAttacks() {
        return componentAttacks;
    }

    public void setComponentSuggestedDefenses(List<ComponentData> componentDefenses) {
        this.componentSuggestedDefenses = componentDefenses;
    }

    public List<ComponentData> getComponentSuggestedDefenses() {
        return componentSuggestedDefenses;
    }

    public void setComponentSuggestedDefensesProfile(List<ComponentData> componentDefensesProfile) {
        this.componentSuggestedDefensesProfile = componentDefensesProfile;
    }

    public List<ComponentData> getComponentSuggestedDefensesProfile() {
        return componentSuggestedDefensesProfile;
    }

    public void setComponentImplDefense(List<ComponentData> componentImplDefenses) {
        this.componentImplDefenses = componentImplDefenses;
    }

    public List<ComponentData> getComponentImplDefenses() {
        return componentImplDefenses;
    }

    private static String joinComponentDataList(List<ComponentData> data) {
        List<String> joined =
                data.stream().map(ComponentData::getJoined).collect(Collectors.toList());
        return String.join("\n ^ ", joined);
    }

    public String attacks() {
        return joinComponentDataList(componentAttacks);
    }

    public String suggestedDefenses() {
        return joinComponentDataList(componentSuggestedDefenses);
    }

    public String suggestedDefensesProfile() {
        return joinComponentDataList(componentSuggestedDefensesProfile);
    }

    public String implDefenses() {
        return joinComponentDataList(componentImplDefenses);
    }

    public boolean compareCutset(PathAttributes other) {
        // We use this so that we can search for matching cutsets
        // between ApplicableDefenseProperties and ImplProperties.

        if (other.componentAttacks.size() != componentAttacks.size()) {
            return false;
        }
        for (int i = 0; i < componentAttacks.size(); i++) {
            if (!other.componentAttacks
                            .get(i)
                            .getComponent()
                            .equals(componentAttacks.get(i).getComponent())
                    || !other.componentAttacks
                            .get(i)
                            .getData()
                            .equals(componentAttacks.get(i).getData())) {
                return false;
            }
        }
        return true;
    }
}
