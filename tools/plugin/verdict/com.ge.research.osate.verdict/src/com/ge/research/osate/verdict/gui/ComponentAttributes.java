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

// this class stores the attributes of a component extracted from MBAS .xml
public class ComponentAttributes implements Serializable, Cloneable {

    private static final long serialVersionUID = 1L;
    private String component;
    private List<String> capecs = new ArrayList<String>();
    private List<String> defenses = new ArrayList<String>();
    private List<String> description = new ArrayList<String>();

    public void setComponent(String str) {
        component = str;
    }

    public String getComponent() {
        return component;
    }

    public void addCapec(String str) {
        capecs.add(str);
    }

    public void addDefense(String str) {
        defenses.add(str);
    }

    public void addDescription(String str) {
        description.add(str);
    }

    public List<String> getCapecs() {
        return capecs;
    }

    public List<String> getDefenses() {
        return defenses;
    }

    public List<String> getDescriptions() {
        return description;
    }

    public void setDescriptions(List<String> list) {
        description = list;
    }
}
