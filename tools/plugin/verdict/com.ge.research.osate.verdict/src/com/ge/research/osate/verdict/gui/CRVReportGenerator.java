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

import java.util.List;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// this class performs the overall task of generating report from CRV .xml file
// need to be invoked from CRV handler (just before the handler returns for static implementation
// dynamic update can be implemented by creating parallel threads: one for CRV tool, one for the
// report-generator)
public class CRVReportGenerator implements Runnable {
    private String fileName1;
    private String fileName2;
    public List<CRVSummaryRow> tableContents;
    public static IWorkbenchWindow window;

    public CRVReportGenerator(String fileName1, String fileName2, IWorkbenchWindow window) {
        this.fileName1 = fileName1;
        this.fileName2 = fileName2;
        CRVReportGenerator.window = window;
        ResultsPageUtil.closePages();
        CRVResultSummary result = new CRVResultSummary(fileName1, fileName2);
        tableContents = result.getTableContents();
        // MeritAssignmentView.treeContents = result.getIVC();
        MeritAssignmentView.mustSet = result.getMustSet();
        MeritAssignmentView.aInvTreeContents = result.getaIVCs();
        MeritAssignmentView.mInvTreeContents = result.getmIVCs();

        showView(window);
    }

    @Override
    public void run() {
        new CRVResultSummary(fileName1, fileName2);
    }

    // invokes the view tab for CRV result
    protected void showView(IWorkbenchWindow window) {
        /*
         * This command is executed while the xtext document is locked. Thus it must be
         * async otherwise we can get a deadlock condition if the UI tries to lock the
         * document, e.g., to pull up hover information.
         */
        window.getShell()
                .getDisplay()
                .asyncExec(
                        () -> {
                            try {
                                CRVResultsView.tableContents = tableContents;
                                window.getActivePage().showView(CRVResultsView.ID);
                            } catch (PartInitException e) {
                                e.printStackTrace();
                            }
                        });
    }
}
