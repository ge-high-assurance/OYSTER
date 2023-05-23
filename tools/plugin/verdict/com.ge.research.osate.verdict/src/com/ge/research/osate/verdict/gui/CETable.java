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
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// this class creates contents of the counter-example table,
// extracting from the content read from CRV .xml
public class CETable {

    private List<CounterExampleAttributes> ceList;
    private List<CERow> tableContents = new ArrayList<CERow>();

    public CETable(Display display, Shell lastShell, List<CounterExampleAttributes> list) {
        ceList = list;
        tableContents = loadTableContents(ceList);
    }

    private List<CERow> loadTableContents(List<CounterExampleAttributes> list) {
        List<CERow> contents = new ArrayList<CERow>();
        for (int i = 0; i < list.size(); i++) {
            CounterExampleAttributes ce = list.get(i);
            String sysName = ce.getNodeName();
            List<CENode> nodeAttr = ce.getNodeAttr();
            for (int j = 0; j < nodeAttr.size(); j++) {
                CERow newRow = new CERow();
                newRow.addRow(sysName);
                CENode node = nodeAttr.get(j);
                newRow.addRow(node.getVarName());
                newRow.addRow(node.getVarClass());
                newRow.addRow(node.getVarType());
                for (int k = 0; k < node.getVarValue().size(); k++) {
                    newRow.addRow(node.getVarValue().get(k));
                }
                contents.add(newRow);
                sysName = "-do-";
            }
        }

        return contents;
    }

    public List<CERow> getTableContents() {
        return tableContents;
    }
}
