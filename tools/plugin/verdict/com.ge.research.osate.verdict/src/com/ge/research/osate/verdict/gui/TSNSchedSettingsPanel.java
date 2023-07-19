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

import java.util.HashSet;
import java.util.Set;

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

public class TSNSchedSettingsPanel extends ApplicationWindow {

    private static final String SETTINGS_TITLE = "TSN Schedule Proof Validation Settings";

    // static vars are preserved through the eclipse session
    private static boolean dotEnabled = true;
    private static boolean lfscEnabled = true;
    private static boolean aletheEnabled = true;
    private static boolean lfscCheckEnabled = true;

    private static final Font REG_FONT = new Font(null, "Helvetica", 12, SWT.NORMAL);

    private static final Font BOLD_FONT = new Font(null, "Helvetica", 12, SWT.BOLD);

    public TSNSchedSettingsPanel() {
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

    public static boolean isDotEnabled() {
        return dotEnabled;
    }

    public static boolean isLFSCEnabled() {
        return lfscEnabled;
    }

    public static boolean isAletheEnabled() {
        return aletheEnabled;
    }
    
    public static boolean isLFSCCheckEnabled() {
    	return lfscCheckEnabled;
    }
    
    public static Set<String> getProofFormats(){
    	Set<String> proofFormats = new HashSet<>();
    	if(dotEnabled) {
    		proofFormats.add("dot");
    	}
    	if(aletheEnabled) {
    		proofFormats.add("alethe");
    		
    	}
    	if(lfscEnabled) {
    		proofFormats.add("lfsc");
    	}
    	return proofFormats;
    }

    @Override
    protected Control createContents(Composite parent) {

        final Composite mainComposite = new Composite(parent, SWT.NONE);
        mainComposite.setLayout(new GridLayout(1, false));

        final Label optLabel2 = new Label(mainComposite, SWT.NONE);
        optLabel2.setText("TSN Proof Formats");
        optLabel2.setFont(BOLD_FONT);

        final Group validatorGroup1 = new Group(mainComposite, SWT.NONE);
        validatorGroup1.setLayout(new GridLayout(1, false));
        final GridData gridData = new GridData(GridData.VERTICAL_ALIGN_END);
        //gridData.horizontalIndent = 25;

        final Button dotToggle = new Button(validatorGroup1, SWT.CHECK);
        dotToggle.setText("Dot");
        dotToggle.setFont(REG_FONT);
        dotToggle.setSelection(dotEnabled);

        final Button lfscToggle = new Button(validatorGroup1, SWT.CHECK);
        lfscToggle.setText("LFSC");
        lfscToggle.setFont(REG_FONT);
        lfscToggle.setSelection(lfscEnabled);
        lfscToggle.setLayoutData(gridData);

        final Button aletheToggle = new Button(validatorGroup1, SWT.CHECK);
        aletheToggle.setText("Alethe");
        aletheToggle.setFont(REG_FONT);
        aletheToggle.setSelection(aletheEnabled);
        aletheToggle.setLayoutData(gridData);

        
        
        final Label optLabel3 = new Label(mainComposite, SWT.NONE);
        optLabel3.setText("Proof Checkers");
        optLabel3.setFont(BOLD_FONT);
        
        final Group validatorGroup2 = new Group(mainComposite, SWT.NONE);
        validatorGroup2.setLayout(new GridLayout(1, false));
        final Button lfscCheckToggle = new Button(validatorGroup2, SWT.CHECK);
        lfscCheckToggle.setText("Use LFSC Checker");
        lfscCheckToggle.setFont(REG_FONT);
        lfscCheckToggle.setSelection(lfscCheckEnabled);

        
        lfscCheckToggle.addSelectionListener(
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent e) {
                    	    if(lfscCheckToggle.getSelection()) {
                    	    	lfscToggle.setSelection(true);
                    	    }
                    }
                });

        
        
         
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
                        dotEnabled = dotToggle.getSelection();
                        lfscEnabled = lfscToggle.getSelection();
                        aletheEnabled = aletheToggle.getSelection();
                        lfscCheckEnabled = lfscCheckToggle.getSelection();
                        mainComposite.getShell().close();
                    }
                });

        return mainComposite;
    }
}
