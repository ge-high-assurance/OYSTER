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

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.ui.part.ViewPart;

import oyster.odm.odm_model.ConstraintType;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class UnsatCoreView extends ViewPart {
    public static final String ID = "com.ge.research.osate.verdict.gui.unsatCoreView";
    private Composite composite;
    private Table table;
    public static List<String> unsatCore = new ArrayList<>();
    public static Map<String, ConstraintType> constraintType = new HashMap<>();

    @Override
    public void setFocus() {
        if (composite != null) {
            composite.setFocus();
        }
    }

    @Override
    public void createPartControl(Composite parent) {
        Composite composite = new Composite(parent, SWT.NONE);
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

        TableColumn constraintColHeader = new TableColumn(table, SWT.CENTER);
        constraintColHeader.setText("Constraint");
        constraintColHeader.setWidth(500);
        constraintColHeader.pack();

        TableColumn constraintTypeHeader = new TableColumn(table, SWT.CENTER);
        constraintTypeHeader.setText("Constraint Type");
        constraintTypeHeader.pack();

        TableColumn commentsHeader = new TableColumn(table, SWT.CENTER);
        commentsHeader.setText("Comments");
        commentsHeader.pack();


        // populate the data

        for (String constraint : unsatCore) {
            TableItem item = new TableItem(table, SWT.CENTER);
            item.setText(0, constraint);
            item.setText(1, formatConstraintType(constraint, constraintType));
            item.setText(2, "");
           
        	}

        table.pack();
        composite.pack();
    }
    
    public static String formatConstraintType(String constraint, Map<String, ConstraintType> constraintType) {
    	 ConstraintType type = constraintType.get(constraint);
    	 if(type == null && constraint.contains("sched")) {
    		 return "Scheduling Constraint";
    	 }
    	 
    	 if(type != null) {
    		 switch(type) {
    		 case FIXED_LOCATION_CONSTRAINT :
    			        return "Fixed Location Constraint";
    		 case SEPARATION_CONSTRAINT:
    			        return "Separation Constraint";
    		 case CO_LOCATION_CONSTRAINT:
    			        return "Co-location Constraint";
    		 case UTILIZATION_CONSTRAINT:
    			        return "Utilization Constraint";
    		 case VIRTUAL_LINK_CONSTRAINT:
    			        return "Virtual Link Constraint";
    		 case PORT_CONNECTION_CONSTRAINT:
    			        return "Port Connection Constraint";
    		 case LOCATION_CONSTRAINT:
    			        return "Location Constraint";
    		 case READ_ONLY_CONSTRAINT:
    			        return "Read-only Constraint";
    			 
    		 }
    	 }
    	 
    	 
    	 return "";
    }
}
