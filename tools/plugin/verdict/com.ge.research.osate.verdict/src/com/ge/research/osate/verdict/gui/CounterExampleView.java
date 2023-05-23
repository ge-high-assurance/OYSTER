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
import org.eclipse.jface.resource.FontDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
// import org.eclipse.jface.action.MenuManager;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.ui.part.ViewPart;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// this class generates the counter-example view-tab for CRV
public class CounterExampleView extends ViewPart {
    private Composite composite;
    public static final String ID_COUNTER_EXAMPLE =
            "com.ge.research.osate.verdict.gui.counterExampleView";
    public static final String ID_TEST_CASE = "com.ge.research.osate.verdict.gui.testCaseView";
    public static List<CERow> tableContents = new ArrayList<CERow>();
    public static boolean testCase = false;
    public static String propertyName = "";

    // Subclasses because Eclipse distinguishes between different tabs with classes
    // This allows us to use the same class for both

    public static class CounterExample extends CounterExampleView {}

    public static class TestCase extends CounterExampleView {}

    @Override
    public void setFocus() {
        if (composite != null) {
            composite.setFocus();
        }
    }

    @Override
    public void createPartControl(Composite parent) {
        // Check to make sure we're in the correct view
        // In practice we're only in the wrong one if the user manually
        // launches the view from Window > Show View
        if (this instanceof TestCase && !testCase) {
            return;
        }
        if (this instanceof CounterExample && testCase) {
            return;
        }

        Composite composite = new Composite(parent, SWT.NONE);
        Display display = Display.getCurrent();

        composite.setSize(1130, 600);
        composite.setLayout(new GridLayout(1, false));

        Label label = new Label(composite, SWT.NONE);
        FontDescriptor descriptor = FontDescriptor.createFrom(label.getFont());
        descriptor = descriptor.setStyle(SWT.BOLD);
        label.setFont(descriptor.createFont(Display.getCurrent()));
        label.setText((testCase ? "Test Case" : "Counter-example") + ": " + propertyName);

        Table table = new Table(composite, SWT.MULTI | SWT.FULL_SELECTION);
        table.setLayoutData(new GridData(GridData.FILL_BOTH));
        table.setHeaderVisible(true);
        table.setLinesVisible(true);
        table.setHeaderBackground(display.getSystemColor(SWT.COLOR_TITLE_BACKGROUND_GRADIENT));
        table.setHeaderForeground(display.getSystemColor(SWT.COLOR_TITLE_FOREGROUND));

        TableColumn col1 = new TableColumn(table, SWT.CENTER | SWT.WRAP);
        col1.setText("Component");
        TableColumn col2 = new TableColumn(table, SWT.CENTER | SWT.WRAP);
        col2.setText("Variable");
        TableColumn col3 = new TableColumn(table, SWT.CENTER | SWT.WRAP);
        col3.setText("Port Type");
        TableColumn col4 = new TableColumn(table, SWT.CENTER | SWT.WRAP);
        col4.setText("Data Type");

        int colCount = 0;
        if (tableContents.size() > 0) {
            colCount = tableContents.get(0).getRowContents().size();
        }
        for (int i = 0; i < colCount - 4; i++) {
            TableColumn col = new TableColumn(table, SWT.CENTER | SWT.WRAP);
            col.setText("Value (t = " + i + ")");
        }

        int itemCount = tableContents.size();
        for (int i = 0; i < itemCount; i++) {
            TableItem item = new TableItem(table, SWT.NONE);
            List<String> currRow = tableContents.get(i).getRowContents();
            String[] itemSeq = new String[colCount];
            for (int j = 0; j < colCount; j++) {
                itemSeq[j] = currRow.get(j);
            }
            item.setText(itemSeq);
            //			item.setFont(new Font(display, new FontData("Times New Roman", 10, SWT.NORMAL)));
        }

        for (int i = 0; i < table.getColumnCount(); i++) {
            table.getColumn(i).pack();
        }

        table.pack();
        composite.pack();
    }
}
