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

import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;

public class ResultsPageUtil {
    public static void closePages() {
        IWorkbenchPage wp = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
        IViewPart myView1 = wp.findView(MBASResultsView.ID);
        if (myView1 != null) {
            wp.hideView(myView1);
        }
        IViewPart myView2 = wp.findView(CapecDefenseView.ID);
        if (myView2 != null) {
            wp.hideView(myView2);
        }
        IViewPart myView3 = wp.findView(SafetyCutsetsView.ID);
        if (myView3 != null) {
            wp.hideView(myView3);
        }
        IViewPart myView4 = wp.findView(MBASSynthesisResultsView.ID);
        if (myView4 != null) {
            wp.hideView(myView4);
        }
        IViewPart myView5 = wp.findView(CRVResultsView.ID);
        if (myView5 != null) {
            wp.hideView(myView5);
        }
        IViewPart myView6 = wp.findView(CounterExampleView.ID_COUNTER_EXAMPLE);
        if (myView6 != null) {
            wp.hideView(myView6);
        }
        IViewPart myView7 = wp.findView(CounterExampleView.ID_TEST_CASE);
        if (myView7 != null) {
            wp.hideView(myView7);
        }
        IViewPart myView8 = wp.findView(MeritAssignmentView.ID);
        if (myView8 != null) {
            wp.hideView(myView8);
        }
    }
}
