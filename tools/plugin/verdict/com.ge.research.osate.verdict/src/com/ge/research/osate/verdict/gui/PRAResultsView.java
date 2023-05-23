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

import com.ge.oyster.proof_repair_assistant.PRAResultsInstance;
import com.ge.research.osate.verdict.handlers.PRAHandler;
import com.ge.research.osate.verdict.handlers.VerdictHandlersUtils;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.ui.part.ViewPart;

public class PRAResultsView extends ViewPart {
    public static final String ID = "com.ge.research.osate.verdict.gui.praResultsView";
    private Composite composite;
    public static PRAResultsInstance results;
    public static Runnable applyToProject;
    private Table table;
    public static HashMap<String, ArrayList<String>> kind2Results = new HashMap<>();

    @Override
    public void setFocus() {
        if (composite != null) {
            composite.setFocus();
        }
    }

    @Override
    public void createPartControl(Composite parent) {
        Composite composite = new Composite(parent, SWT.NONE);
        if (kind2Results.keySet().isEmpty() && !VerdictHandlersUtils.isRunning()) {
            // preempt rendering when there are no iterations completed
            return;
        }
        Display display = Display.getCurrent();
        // composite.setSize(parent.getSize());
        composite.setLayout(new FillLayout());
        composite.setSize(1130 / 2, 600);
        // Table table2 = new Table(composite, SWT.NONE);
        table = new Table(composite, SWT.H_SCROLL | SWT.V_SCROLL);

        table.setSize(1130, 600);
        table.setHeaderVisible(true);
        table.setLinesVisible(true);
        table.setFocus();

        table.setHeaderBackground(display.getSystemColor(SWT.COLOR_TITLE_BACKGROUND_GRADIENT));
        table.setHeaderForeground(display.getSystemColor(SWT.COLOR_TITLE_FOREGROUND));

        TableColumn propertyColHeader = new TableColumn(table, SWT.CENTER);
        propertyColHeader.setText("Property");
        propertyColHeader.setWidth(500);
        propertyColHeader.pack();
        for (int i = 0; i <= PRAHandler.getCurrentIteration(); i++) {
            TableColumn iterationHeader = new TableColumn(table, SWT.CENTER);
            if (i == 0) {
                iterationHeader.setText("Verification Result (initial)");
            } else {
                iterationHeader.setText("Verification Result (" + i + ")");
            }
            iterationHeader.pack();
        }
        // populate the data
        Set<String> properties = kind2Results.keySet();
        for (String property : properties) {
            TableItem item = new TableItem(table, SWT.CENTER);
            ArrayList<String> results = kind2Results.get(property);
            item.setText(0, property);
            for (int j = 0; j < results.size(); j++) {

                if (results.get(j).equals("valid")) {
                    item.setImage(j + 1, ViewUtils.getIcon("valid.png"));
                } else {
                    item.setImage(j + 1, ViewUtils.getIcon("false.png"));
                }
            }
        }

        table.pack();
        composite.pack();
    }
}
