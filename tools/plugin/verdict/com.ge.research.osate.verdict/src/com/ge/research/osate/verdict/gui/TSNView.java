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

import java.util.HashMap;
import java.util.Map;

public class TSNView extends ViewPart {
	public static final String ID = "com.ge.research.osate.verdict.gui.tsnView";
	private Composite composite;
	private Table table;
	public static HashMap<String, Boolean> tsnResults = new HashMap<>();
	public static HashMap<String, Boolean> tsnLFSCResults = new HashMap<>();
	public static HashMap<String, Boolean> tsnAletheResults = new HashMap<>();

	public static Map<String, Map<String, Integer>> tsnProps = new HashMap<>();

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

		TableColumn propertyColHeader = new TableColumn(table, SWT.CENTER);
		propertyColHeader.setText("TSN Stream");
		propertyColHeader.setWidth(500);
		propertyColHeader.pack();

		TableColumn arrivalTimeHeader = new TableColumn(table, SWT.CENTER);
		arrivalTimeHeader.setText("Arrival time (microseconds)");
		arrivalTimeHeader.pack();

		TableColumn arrivalLimitHeader = new TableColumn(table, SWT.CENTER);
		arrivalLimitHeader.setText("Max Arrival Limit (microseconds)");
		arrivalLimitHeader.pack();

		TableColumn validationHeader = new TableColumn(table, SWT.CENTER);
		validationHeader.setText("Latency Analysis");
		validationHeader.pack();

		if (TSNSchedSettingsPanel.isLFSCCheckEnabled()) {
			TableColumn lfscHeader = new TableColumn(table, SWT.CENTER);
			lfscHeader.setText("LFSC Proof Checking");
			lfscHeader.pack();
		}

		if (TSNSchedSettingsPanel.isAletheCheckEnabled()) {
			TableColumn aletheHeader = new TableColumn(table, SWT.CENTER);
			aletheHeader.setText("Alethe Proof Checking");
			aletheHeader.pack();
		}

		// populate the data

		for (String tsnStream : tsnResults.keySet()) {
			TableItem item = new TableItem(table, SWT.CENTER);
			item.setText(0, tsnStream);
			int arrivalTime = tsnProps.get(tsnStream).get("tsn_sched_arrival_time");
			int maxArrivalTime = tsnProps.get(tsnStream).get("tsn_sched_arrival_limit")
					+ tsnProps.get(tsnStream).get("tsn_sched_threshold");
			item.setText(1, Integer.toString(arrivalTime));
			item.setText(2, Integer.toString(maxArrivalTime));

			if (tsnResults.get(tsnStream).booleanValue() == true) {
				item.setImage(3, ViewUtils.getIcon("valid.png"));

			} else {
				item.setImage(3, ViewUtils.getIcon("false.png"));
			}

			if (TSNSchedSettingsPanel.isLFSCCheckEnabled()) {
				if (tsnLFSCResults.get(tsnStream) != null && tsnLFSCResults.get(tsnStream).booleanValue() == true) {
					item.setImage(4, ViewUtils.getIcon("valid.png"));
				} else {
					item.setImage(4, ViewUtils.getIcon("false.png"));
				}
			}

			if (TSNSchedSettingsPanel.isAletheCheckEnabled()) {
				int index = (TSNSchedSettingsPanel.isLFSCCheckEnabled()) ? 5 : 4;
				
				if (tsnAletheResults.get(tsnStream) != null && tsnAletheResults.get(tsnStream).booleanValue() == true) {
					item.setImage(index, ViewUtils.getIcon("valid.png"));
				} else {
					item.setImage(index, ViewUtils.getIcon("false.png"));
				}
			}
		}

		table.pack();
		composite.pack();
	}
}
