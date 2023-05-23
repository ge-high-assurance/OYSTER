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
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Monitor;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

/** Author: Joyanta Debnath Date: July 15, 2022 */
public class IMASynthesisSettingsPanel extends ApplicationWindow {
    public static Set<String> selectedThreats = new HashSet<String>();
    public static boolean optBandwidthYes = false;
    public static boolean fsbBandwidthYes = false;
    public static boolean opte2eFlowYes = false;
    public static boolean fsbe2eFlowYes = false;
    public static boolean fsbAppScheduleYes = false;
    public static boolean unsatCoreYes = false;

    public static String hostCompName = "";
    public static boolean hostCompNameTBvisible = false;

    private Font font, boldFont;

    public IMASynthesisSettingsPanel() {
        super(null);

        font = new Font(null, "Helvetica", 12, SWT.NORMAL);
        boldFont = new Font(null, "Helvetica", 12, SWT.BOLD);
    }

    @Override
    protected void configureShell(Shell shell) {
        super.configureShell(shell);
        Display display = shell.getDisplay();
        Monitor primary = display.getPrimaryMonitor();
        Rectangle bounds = primary.getBounds();
        Rectangle rect = shell.getBounds();

        int x = bounds.x + (bounds.width - rect.width) / 2;
        int y = bounds.y + (bounds.height - rect.height) / 2;

        shell.setLocation(x, y);
        shell.setText("IMA Synthesis Settings");
        shell.setFont(font);
    }

    public void run() {
        setBlockOnOpen(true);
        open();
    }

    public void bringToFront(Shell shell) {
        shell.setActive();
    }

    @Override
    protected Control createContents(Composite parent) {
        Composite mainComposite = new Composite(parent, SWT.NONE);
        mainComposite.setLayout(new GridLayout(1, false));

        // Options
        Label optLabel0 = new Label(mainComposite, SWT.NONE);
        optLabel0.setText("Default: Architecture Synthesis Only");
        optLabel0.setFont(font);

        Label optLabel2 = new Label(mainComposite, SWT.NONE);
        optLabel2.setText("Virtual-Link Flows");
        optLabel2.setFont(boldFont);

        Group optGroup2 = new Group(mainComposite, SWT.NONE);
        optGroup2.setLayout(new GridLayout(1, false));

        Button e2eFlowFsb = new Button(optGroup2, SWT.CHECK);
        e2eFlowFsb.setText("Generate Feasible Solution");
        e2eFlowFsb.setFont(font);
        e2eFlowFsb.setSelection(fsbe2eFlowYes);

        Button e2eFlowOpt = new Button(optGroup2, SWT.CHECK);
        e2eFlowOpt.setText("Generate Optimal Solution");
        e2eFlowOpt.setFont(font);
        e2eFlowOpt.setSelection(opte2eFlowYes);

        Label optLabel1 = new Label(mainComposite, SWT.NONE);
        optLabel1.setText("Network Bandwidth");
        optLabel1.setFont(boldFont);

        Group optGroup1 = new Group(mainComposite, SWT.NONE);
        optGroup1.setLayout(new GridLayout(1, false));

        Button netBandFsb = new Button(optGroup1, SWT.CHECK);
        netBandFsb.setText("Generate Feasible Solution");
        netBandFsb.setFont(font);
        netBandFsb.setSelection(fsbBandwidthYes);

        //		Button netBandOpt = new Button(optGroup1, SWT.CHECK);
        //		netBandOpt.setText("Generate Optimal Solution");
        //		netBandOpt.setFont(font);
        //		netBandOpt.setSelection(optBandwidthYes);

        Label optLabel3 = new Label(mainComposite, SWT.NONE);
        optLabel3.setText("GPM Application Scheduling");
        optLabel3.setFont(boldFont);

        Group optGroup3 = new Group(mainComposite, SWT.NONE);
        optGroup3.setLayout(new GridLayout(1, false));

        Button appScheduleFsb = new Button(optGroup3, SWT.CHECK);
        appScheduleFsb.setText("Generate Feasible Solution");
        appScheduleFsb.setFont(font);
        appScheduleFsb.setSelection(fsbAppScheduleYes);

        Label optLabel4 = new Label(optGroup3, SWT.NONE);
        optLabel4.setText("Enter the name of host component instance");
        optLabel4.setFont(font);
        optLabel4.setVisible(hostCompNameTBvisible);

        Text appScheduleTb = new Text(optGroup3, SWT.BORDER);
        appScheduleTb.setText(hostCompName);
        appScheduleTb.setFont(font);
        appScheduleTb.setVisible(hostCompNameTBvisible);
        
        
       
        
        netBandFsb.addSelectionListener(
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent e) {
                        if (!(netBandFsb.getSelection())) {
                            //					netBandOpt.setSelection(false);
                        }
                    }
                });

        //		netBandOpt.addSelectionListener(new SelectionAdapter() {
        //			@Override
        //			public void widgetSelected(SelectionEvent e) {
        //				if (netBandOpt.getSelection()) {
        //					netBandFsb.setSelection(true);
        //					netBandFsb.setEnabled(false);
        //				} else {
        //					netBandFsb.setEnabled(true);
        //				}
        //			}
        //		});

        e2eFlowFsb.addSelectionListener(
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent e) {
                        if (!(e2eFlowFsb.getSelection())) {
                            e2eFlowOpt.setSelection(false);
                        }
                    }
                });

        e2eFlowOpt.addSelectionListener(
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent e) {
                        if (e2eFlowOpt.getSelection()) {
                            e2eFlowFsb.setSelection(true);
                            e2eFlowFsb.setEnabled(false);
                        } else {
                            e2eFlowFsb.setEnabled(true);
                        }
                    }
                });

        appScheduleFsb.addSelectionListener(
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent event) {
                        if (appScheduleFsb.getSelection()) {
                            appScheduleTb.setVisible(true);
                            optLabel4.setVisible(true);
                        } else {
                            appScheduleTb.setVisible(false);
                            optLabel4.setVisible(false);
                            hostCompName = "";
                            appScheduleTb.setText(hostCompName);
                        }
                    }
                });
        

        Label optLabel5 = new Label(mainComposite, SWT.NONE);
        optLabel5.setText("UNSAT Cores");
        optLabel5.setFont(boldFont);
        
        Group optGroup4 = new Group(mainComposite, SWT.NONE);
        optGroup4.setLayout(new GridLayout(1, false));
        
        Button unsatCoreBtn = new Button(optGroup4, SWT.CHECK);
        unsatCoreBtn.setText("Report unsat core");
        unsatCoreBtn.setFont(font);
        unsatCoreBtn.setSelection(unsatCoreYes);
        
        unsatCoreBtn.addSelectionListener(
                new SelectionAdapter() {
                    @Override
                    public void widgetSelected(SelectionEvent event) {
                        if (unsatCoreBtn.getSelection()) {
                       /* 	
                        	MessageBox messageBox = new MessageBox(Display.getDefault().getActiveShell(), SWT.ICON_WARNING);
                             messageBox.setText("Warning");
                            messageBox.setMessage("IMA Synthesis will take a long time when there is no unsat core (that is the constraints are sat)");
                            messageBox.open();
                        */     
                        } 
                    }
                });
        
        
        
        // save and close buttons
        Composite closeButtons = new Composite(mainComposite, SWT.NONE);
        closeButtons.setLayout(new RowLayout(SWT.HORIZONTAL));
        closeButtons.setLayoutData(new GridData(SWT.CENTER, SWT.BOTTOM, true, true, 1, 1));

        Button cancel = new Button(closeButtons, SWT.PUSH);
        cancel.setText("Cancel");
        cancel.setFont(font);

        Button save = new Button(closeButtons, SWT.PUSH);
        save.setText("Save Settings");
        save.setFont(font);

        // Set font for button text
        save.setFont(font);

        // Set the preferred size
        Point bestSize = getShell().computeSize(SWT.DEFAULT, SWT.DEFAULT);
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
                        // assign values for network bandwidth optimization
                        //				optBandwidthYes = netBandOpt.getSelection();
                        fsbBandwidthYes = netBandFsb.getSelection();
                        opte2eFlowYes = e2eFlowOpt.getSelection();
                        fsbe2eFlowYes = e2eFlowFsb.getSelection();
                        fsbAppScheduleYes = appScheduleFsb.getSelection();
                        hostCompName = appScheduleTb.getText();
                        hostCompNameTBvisible = appScheduleFsb.getSelection();
                        unsatCoreYes = unsatCoreBtn.getSelection();
                        mainComposite.getShell().close();
                    }
                });

        return mainComposite;
    }
}
