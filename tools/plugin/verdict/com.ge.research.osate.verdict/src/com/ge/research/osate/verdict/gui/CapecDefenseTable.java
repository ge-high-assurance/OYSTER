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

import com.ge.research.osate.verdict.gui.PathAttributes.ComponentData;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// This class creates the row contents of Vulnerability/Defense tables, extracting from
// the contents read from the MBAS .xml output

public class CapecDefenseTable {

    private List<PathAttributes> pathList;
    private List<CapecDefenseRow> tableContents = new ArrayList<CapecDefenseRow>();

    public CapecDefenseTable(
            Display display,
            Shell lastShell,
            List<PathAttributes> list,
            Map<String, String> attackDesc,
            Map<String, String> defenseDesc) {
        pathList = list;
        tableContents = loadTableContents(pathList, attackDesc, defenseDesc);
    }

    private List<CapecDefenseRow> loadTableContents(
            List<PathAttributes> list,
            Map<String, String> attackDesc,
            Map<String, String> defenseDesc) {
        List<CapecDefenseRow> contents = new ArrayList<CapecDefenseRow>();
        for (int i = 0; i < list.size(); i++) {
            PathAttributes path = list.get(i);
            CapecDefenseRow newRow = new CapecDefenseRow();
            newRow.addToRow("Path # " + (i + 1));
            newRow.addToRow(path.getLikelihood());
            newRow.addToRow(path.attacks());
            newRow.addToRow(path.suggestedDefenses());
            newRow.addToRow(path.suggestedDefensesProfile());
            newRow.addToRow(path.implDefenses());

            // Find descriptions for all CAPECs and NISTS
            // We don't have the unformatted attacks/defenses, so we need to do a regex
            // split
            // We ignore "(", ")", and whitespace, plus the words "and" and "or"
            for (ComponentData data : path.getComponentAttacks()) {
                String[] keys = data.getData().split("[\\s()]");
                for (String key : keys) {
                    if (key.length() == 0 || "and".equals(key) || "or".equals(key)) {
                        continue;
                    } else if (attackDesc.containsKey(key)) {
                        newRow.addAttackHoverText(key + ": " + attackDesc.get(key));
                    } else {
                        System.err.println("could not find attack key: " + key);
                    }
                }
            }
            for (ComponentData data : path.getComponentSuggestedDefensesProfile()) {
                String[] keys = data.getData().split("[\\s()]");
                for (String key : keys) {
                    if (key.length() == 0 || "and".equals(key) || "or".equals(key)) {
                        continue;
                    } else if (defenseDesc.containsKey(key)) {
                        newRow.addDefenseHoverText(key + ": " + defenseDesc.get(key));
                    } else {
                        System.err.println("could not find defense key: " + key);
                    }
                }
            }

            contents.add(newRow);
        }
        return contents;
    }

    public List<CapecDefenseRow> getTableContents() {
        return tableContents;
    }
}
