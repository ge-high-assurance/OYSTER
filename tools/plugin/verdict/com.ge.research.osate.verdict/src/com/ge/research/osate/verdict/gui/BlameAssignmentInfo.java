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

// this class stores contents related to Blame-assignment (used by CRV Results viewer-tab)
public class BlameAssignmentInfo {
    //	private String threatDescription = "";
    private List<String> components = new ArrayList<>();
    private List<String> links = new ArrayList<>();
    private List<String> threats = new ArrayList<String>();
    private List<String> componentsUncompromised = new ArrayList<>();
    private List<String> linksUncompromised = new ArrayList<>();

    private String buildStringList(List<String> list) {
        StringBuilder builder = new StringBuilder();
        for (int i = 0; i < list.size() - 1; i++) {
            builder.append(list.get(i));
            builder.append(", ");
        }
        if (list.size() > 0) {
            builder.append(list.get(list.size() - 1));
        }
        return builder.toString();
    }

    public void addComponent(String str) {
        components.add(str);
    }

    public String getComponents() {
        return buildStringList(components);
    }

    public void addLink(String str) {
        links.add(str);
    }

    public String getLinks() {
        return buildStringList(links);
    }

    public void addComponentUncompromised(String str) {
        componentsUncompromised.add(str);
    }

    public String getComponentsUncompromised() {
        return buildStringList(componentsUncompromised);
    }

    public void addLinkUncompromised(String str) {
        linksUncompromised.add(str);
    }

    public String getLinksUncompromised() {
        return buildStringList(linksUncompromised);
    }

    public void addThreat(String str) {
        this.threats.add(str);
    }

    public String getThreats() {
        return buildStringList(this.threats);
    }
}
