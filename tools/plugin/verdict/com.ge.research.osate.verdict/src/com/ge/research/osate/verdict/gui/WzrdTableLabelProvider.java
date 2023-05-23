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

import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.swt.graphics.Image;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// this class is used by JFace table-viewer. It provides the drop-down contents
// to the table cells
public class WzrdTableLabelProvider implements ITableLabelProvider {

    private boolean systemLevel;
    private DrpDnLists drpdn;

    public WzrdTableLabelProvider(DrpDnLists list, boolean sysLevel) {
        systemLevel = sysLevel;
        drpdn = list;
    }

    @Override
    public Image getColumnImage(Object element, int columnIndex) {
        return null;
    }

    @Override
    public String getColumnText(Object element, int columnIndex) {
        WzrdTableRow tableRow = (WzrdTableRow) element;
        switch (columnIndex) {
            case 0:
                return tableRow.getFormulaID();
            case 1:
                if (systemLevel) {
                    return drpdn.CIA[tableRow.getFirstElement().intValue()];
                } else {
                    return drpdn.outPorts[tableRow.getFirstElement().intValue()];
                }
            case 2:
                if (systemLevel) {
                    return drpdn.SEVERITY[tableRow.getSecondElement().intValue()];
                } else {
                    return drpdn.CIA[tableRow.getSecondElement().intValue()];
                }
            case 3:
                return tableRow.getThirdElement();
        }
        return null;
    }

    @Override
    public void addListener(ILabelProviderListener listener) {
        // Ignore it
    }

    @Override
    public void dispose() {
        // Nothing to dispose
    }

    @Override
    public boolean isLabelProperty(Object element, String property) {
        return false;
    }

    @Override
    public void removeListener(ILabelProviderListener listener) {
        // Ignore
    }
}
