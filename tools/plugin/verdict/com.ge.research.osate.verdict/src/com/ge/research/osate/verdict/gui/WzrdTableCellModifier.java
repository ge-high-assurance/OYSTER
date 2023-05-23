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

import org.eclipse.jface.viewers.ICellModifier;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Item;

/** Author: Soumya Talukder Date: Jul 18, 2019 */
// this class is used by jFace table-viewer for updating table-cell contents
// after user edits
public class WzrdTableCellModifier implements ICellModifier {
    private Viewer viewer; // the current viewer
    private WzrdTableRow tableRow; // the data-structure to contain contents of the current row
    private String[] props =
            new String[3]; // contains the header elements of the StatementEditor tableViewer

    public WzrdTableCellModifier(Viewer viewer, String[] strings) {
        this.viewer = viewer;
        props = strings;
    }

    @Override
    public boolean canModify(Object element, String property) {
        return true;
    }

    @Override
    public Object getValue(Object element, String property) {
        tableRow = (WzrdTableRow) element;
        if (props[0].equals(property)) {
            return tableRow.getFormulaID();
        } else if (props[1].equals(property)) {
            return tableRow.getFirstElement();
        } else if (props[2].equals(property)) {
            return tableRow.getSecondElement();
        } else {
            return tableRow.getThirdElement();
        }
    }

    @Override
    public void modify(Object element, String property, Object value) {
        if (element instanceof Item) {
            element = ((Item) element).getData();
        }

        tableRow = (WzrdTableRow) element;
        if (props[0].equals(property)) {
            tableRow.setFormulaID((String) value);
        } else if (props[1].equals(property)) {
            tableRow.setFirstElement((int) value);
        } else if (props[2].equals(property)) {
            tableRow.setSecondElement((int) value);
        } else {
            tableRow.setThirdElement((String) value);
        }

        viewer.refresh();
    }
}
