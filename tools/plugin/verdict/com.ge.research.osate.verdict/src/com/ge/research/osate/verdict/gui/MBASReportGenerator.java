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

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

/** Author: Soumya Talukder Date: Jul 18, 2019 */
// this class performs the overall activities of generating report from CRV .xml
// to be called from MBAS handler (just before the handler returns for static implementation
// dynamic update can be implemented by creating two threads: one for MBAS tool and the other for
// this class)
public class MBASReportGenerator implements Runnable {
    private String applicableDefense;
    private String implProperty;
    public static IWorkbenchWindow window;
    private List<MissionAttributes> missions = new ArrayList<MissionAttributes>();
    private Map<String, List<MBASSafetyResult>> safetyResults;
    private Map<String, String> attackDesc, defenseDesc;

    public MBASReportGenerator(
            String applicableDefense,
            String implProperty,
            String safetyApplicableDefense,
            String safetyImplProperty,
            IWorkbenchWindow window,
            String capecFile,
            String nistFile) {
        this.applicableDefense = applicableDefense;
        this.implProperty = implProperty;
        MBASReportGenerator.window = window;
        ResultsPageUtil.closePages();
        MBASResultSummary result = new MBASResultSummary(applicableDefense, implProperty);
        missions = result.getMissions();
        safetyResults = loadSafetyResults(safetyApplicableDefense, safetyImplProperty);
        result.updateMissionsWithSafety(safetyResults);

        // Load maps from CAPECs and NISTS to descriptions (for tooltips)
        attackDesc =
                CsvMapReader.readCsvMap(new File(capecFile), "\"CAPEC\"", "\"CAPECDescription\"");
        defenseDesc =
                CsvMapReader.readCsvMap(
                        new File(nistFile), "\"NISTProfile\"", "\"DefenseDescription\"");

        showView(window);
    }

    @Override
    public void run() {
        new MBASResultSummary(applicableDefense, implProperty);
    }

    // invokes the MBAS Result viewer-tab in OSATE
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
                                MBASResultsView.missions = missions;
                                MBASResultsView.safetyResults = safetyResults;
                                MBASResultsView.attackDesc = attackDesc;
                                MBASResultsView.defenseDesc = defenseDesc;
                                window.getActivePage().showView(MBASResultsView.ID);
                            } catch (PartInitException e) {
                                e.printStackTrace();
                            }
                        });
    }

    private Map<String, List<MBASSafetyResult>> loadSafetyResults(
            String safetyApplicableDefense, String safetyImplProperty) {
        Map<String, List<MBASSafetyResult>> results = new LinkedHashMap<>();

        // We don't use both files right now because AFAIK they are 99.9% identical

        try {
            DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
            DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
            Document doc = dBuilder.parse(new File(safetyApplicableDefense));
            doc.getDocumentElement().normalize();

            NodeList missionNodes = doc.getElementsByTagName("Mission");

            for (int i = 0; i < missionNodes.getLength(); i++) {
                Node missionNode = missionNodes.item(i);
                if (missionNode.getNodeType() == Node.ELEMENT_NODE) {
                    Element missionElem = (Element) missionNode;
                    String missionName = missionElem.getAttribute("label");
                    List<MBASSafetyResult> requirements = new ArrayList<>();

                    NodeList reqNodes = missionElem.getElementsByTagName("Requirement");
                    for (int j = 0; j < reqNodes.getLength(); j++) {
                        Node reqNode = reqNodes.item(j);
                        if (reqNode.getNodeType() == Node.ELEMENT_NODE) {
                            Element reqElem = (Element) reqNode;
                            String reqName = reqElem.getAttribute("label");
                            String defenseType = reqElem.getAttribute("defenseType");
                            String computedLikelihood = reqElem.getAttribute("computed_p");
                            String acceptableLikelihood = reqElem.getAttribute("acceptable_p");
                            List<MBASSafetyResult.CutsetResult> cutsets = new ArrayList<>();

                            NodeList cutsetNodes = reqElem.getElementsByTagName("Cutset");
                            for (int k = 0; k < cutsetNodes.getLength(); k++) {
                                Node cutsetNode = cutsetNodes.item(k);
                                if (cutsetNode.getNodeType() == Node.ELEMENT_NODE) {
                                    Element cutsetElem = (Element) cutsetNode;
                                    String likelihood = cutsetElem.getAttribute("probability");
                                    List<MBASSafetyResult.CutsetResult.Event> events =
                                            new ArrayList<>();

                                    NodeList componentNodes =
                                            cutsetElem.getElementsByTagName("Component");
                                    for (int m = 0; m < componentNodes.getLength(); m++) {
                                        Node componentNode = componentNodes.item(m);
                                        if (componentNode.getNodeType() == Node.ELEMENT_NODE) {
                                            Element componentElem = (Element) componentNode;
                                            String componentName =
                                                    componentElem.getAttribute("name");

                                            NodeList eventNodes =
                                                    componentElem.getElementsByTagName("Event");
                                            if (eventNodes.getLength() > 0
                                                    && eventNodes.item(0).getNodeType()
                                                            == Node.ELEMENT_NODE) {
                                                Element eventElem = (Element) eventNodes.item(0);
                                                String eventName = eventElem.getAttribute("name");

                                                events.add(
                                                        new MBASSafetyResult.CutsetResult.Event(
                                                                componentName, eventName));
                                            }
                                        }
                                    }

                                    cutsets.add(
                                            new MBASSafetyResult.CutsetResult(likelihood, events));
                                }
                            }

                            requirements.add(
                                    new MBASSafetyResult(
                                            reqName,
                                            defenseType,
                                            computedLikelihood,
                                            acceptableLikelihood,
                                            cutsets));
                        }
                    }
                    results.put(missionName, requirements);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }

        return results;
    }
}
