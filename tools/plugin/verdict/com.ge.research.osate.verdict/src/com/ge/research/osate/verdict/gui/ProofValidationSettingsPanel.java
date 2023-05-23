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

import org.eclipse.jface.window.ApplicationWindow;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Monitor;
import org.eclipse.swt.widgets.Shell;

public class ProofValidationSettingsPanel extends ApplicationWindow {

    private static final String SETTINGS_TITLE = "Proof Validation Settings";

    // static vars are preserved through the eclipse session
    private static boolean smtLibEnabled = true;
    private static boolean cvc5Enabled = true;
    private static boolean z3Enabled = true;
    private static boolean lfscEnabled = true;

    private static final Font REG_FONT = 
    		new Font(null, "Helvetica", 12, SWT.NORMAL);
    
    private static final Font BOLD_FONT = 
    		new Font(null, "Helvetica", 12, SWT.BOLD);

    public ProofValidationSettingsPanel() {
        super(null);
    }

    @Override
    protected void configureShell(Shell shell) {
        super.configureShell(shell);
        final Display display = shell.getDisplay();
        final Monitor primary = display.getPrimaryMonitor();
        final Rectangle bounds = primary.getBounds();
        final Rectangle rect = shell.getBounds();
        int x = bounds.x + (bounds.width - rect.width) / 2;
        int y = bounds.y + (bounds.height - rect.height) / 2;
        shell.setLocation(x, y);
        shell.setText(SETTINGS_TITLE);
        shell.setFont(REG_FONT);
    }

    public void run() {
        setBlockOnOpen(true);
        open();
    }

    public static void bringToFront(final Shell shell) {
        shell.setActive();
    }

    public static boolean isCvc5Enabled() {
        return cvc5Enabled;
    }

    public static boolean isZ3Enabled() {
        return z3Enabled;
    }

    public static boolean isLfscEnabled() {
        return lfscEnabled;
    }

    @Override
    protected Control createContents(Composite parent) {

        final Composite mainComposite = new Composite(parent, SWT.NONE);
        mainComposite.setLayout(new GridLayout(1, false));

        final Label optLabel2 = new Label(mainComposite, SWT.NONE);
        optLabel2.setText("Proof Validators");
        optLabel2.setFont(BOLD_FONT);

        final Group validatorGroup1 = new Group(mainComposite, SWT.NONE);
        validatorGroup1.setLayout(new GridLayout(1, false));
        final GridData gridData = new GridData(GridData.VERTICAL_ALIGN_END);
        gridData.horizontalIndent = 25;

        final Button smtToggle = new Button(validatorGroup1, SWT.CHECK);
        smtToggle.setText("SMT-Lib");
        smtToggle.setFont(REG_FONT);
        smtToggle.setSelection(smtLibEnabled);

        final Button z3Toggle = new Button(validatorGroup1, SWT.CHECK);
        z3Toggle.setText("Z3");
        z3Toggle.setFont(REG_FONT);
        z3Toggle.setSelection(z3Enabled);
        z3Toggle.setLayoutData(gridData);

        final Button cvc5Toggle = new Button(validatorGroup1, SWT.CHECK);
        cvc5Toggle.setText("CVC5");
        cvc5Toggle.setFont(REG_FONT);
        cvc5Toggle.setSelection(cvc5Enabled);
        cvc5Toggle.setLayoutData(gridData);

        final Group validatorGroup2 = new Group(mainComposite, SWT.NONE);
        validatorGroup2.setLayout(new GridLayout(1, false));
        final Button lfscToggle = new Button(validatorGroup2, SWT.CHECK);
        lfscToggle.setText("LFSC");
        lfscToggle.setFont(REG_FONT);
        lfscToggle.setSelection(lfscEnabled);

        smtToggle.addSelectionListener(
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent e) {
                        z3Toggle.setSelection(smtToggle.getSelection());
                        cvc5Toggle.setSelection(smtToggle.getSelection());
                    }
                });

        final SelectionAdapter smtSubListener =
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent e) {
                        smtToggle.setSelection(
                                z3Toggle.getSelection() && cvc5Toggle.getSelection());
                    }
                };

        z3Toggle.addSelectionListener(smtSubListener);
        cvc5Toggle.addSelectionListener(smtSubListener);

        // save and close buttons
        final Composite closeButtons = new Composite(mainComposite, SWT.NONE);
        closeButtons.setLayout(new RowLayout(SWT.HORIZONTAL));
        closeButtons.setLayoutData(new GridData(SWT.CENTER, SWT.BOTTOM, true, true, 1, 1));

        final Button cancel = new Button(closeButtons, SWT.PUSH);
        cancel.setText("Cancel");
        cancel.setFont(REG_FONT);

        final Button save = new Button(closeButtons, SWT.PUSH);
        save.setText("Save Settings");
        save.setFont(REG_FONT);

        final Point bestSize = getShell().computeSize(SWT.DEFAULT, SWT.DEFAULT);
        getShell().setSize(bestSize);

        cancel.addSelectionListener(
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent e) {
                        mainComposite.getShell().close();
                    }
                });

        save.addSelectionListener(
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent event) {
                        smtLibEnabled = smtToggle.getSelection();
                        cvc5Enabled = cvc5Toggle.getSelection();
                        z3Enabled = z3Toggle.getSelection();
                        lfscEnabled = lfscToggle.getSelection();
                        mainComposite.getShell().close();
                    }
                });

        return mainComposite;
    }
}
