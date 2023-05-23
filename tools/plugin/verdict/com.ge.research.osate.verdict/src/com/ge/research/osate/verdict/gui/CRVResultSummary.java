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

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Author: Soumya Talukder Date: Jul 18, 2019 */

// this class creates the CRV Results table contents from the contents extracted from .xml
public class CRVResultSummary {

    private List<CRVSummaryRow> tableContents;
    // private List<IVCNode> ivc;
    private ModelSet mustSet;
    private List<Set<ModelNode>> mIvcsList;
    private List<Set<ModelNode>> aIvcsList;

    public CRVResultSummary(String fileName1, String fileName2) {
        CRVReadXMLFile xmlReader = new CRVReadXMLFile(fileName1, fileName2);
        tableContents = loadTableContents(xmlReader.getResults());
        // ivc = xmlReader.getIVC();
        mustSet = xmlReader.mustSet;
        mIvcsList = xmlReader.mIvcsList;
        aIvcsList = xmlReader.aIvcsList;
    }

    private List<CRVSummaryRow> loadTableContents(List<CRVResultAttributes> attributes) {
        try {
            return loadTableContentsAtg(attributes);
        } catch (InvalidAtgException e) {
            return loadTableContentsNormal(attributes);
        }
    }

    public List<CRVSummaryRow> loadTableContentsNormal(List<CRVResultAttributes> attributes) {
        List<CRVSummaryRow> list = new ArrayList<CRVSummaryRow>();
        for (int i = 0; i < attributes.size(); i++) {
            if ("wamax".equals(attributes.get(i).getSource())) {
                continue;
            }
            CRVSummaryRow newRow = new CRVSummaryRow();
            newRow.setPropertyName(attributes.get(i).getProperty());
            newRow.addRow(attributes.get(i).getProperty());
            newRow.addRow(attributes.get(i).getAnswer());
            if (attributes.get(i).getBlameAssignment() != null) {
                newRow.addRow(attributes.get(i).getBlameAssignment().getThreats());
                newRow.addRow(attributes.get(i).getBlameAssignment().getComponents());
                newRow.addRow(attributes.get(i).getBlameAssignment().getLinks());
                newRow.addRow(attributes.get(i).getBlameAssignment().getComponentsUncompromised());
                newRow.addRow(attributes.get(i).getBlameAssignment().getLinksUncompromised());
            } else {
                newRow.addRow("");
                newRow.addRow("");
                newRow.addRow("");
                newRow.addRow("");
                newRow.addRow("");
            }
            newRow.setCounterExample(attributes.get(i).getCntExample());
            newRow.setTestCase(Collections.emptyList());
            newRow.setValidTill(attributes.get(i).getValidTill());
            list.add(newRow);
        }
        return list;
    }

    private static class PosNegPair {
        CRVResultAttributes pos, neg;
    }

    private static class InvalidAtgException extends Exception {
        private static final long serialVersionUID = 1L;

        public InvalidAtgException(String message) {
            super(message);
        }
    }

    public List<CRVSummaryRow> loadTableContentsAtg(List<CRVResultAttributes> attributes)
            throws InvalidAtgException {
        // Match pairs of pos, neg guarantees together
        Map<String, PosNegPair> pairs = new LinkedHashMap<>();
        for (CRVResultAttributes lustreRow : attributes) {
            if ("wamax".equals(lustreRow.getSource())) {
                continue;
            }
            boolean pos;
            if (lustreRow.getProperty().startsWith("pos_")) {
                pos = true;
            } else if (lustreRow.getProperty().startsWith("neg_")) {
                pos = false;
            } else {
                throw new InvalidAtgException(
                        "got a row without valid 'pos_' or 'neg_' prefix: "
                                + lustreRow.getProperty());
            }

            // Chop prefix, remove '[#]' suffix
            int lastOpenBracket = lustreRow.getProperty().lastIndexOf('[');
            String realName = lustreRow.getProperty().substring(4, lastOpenBracket);
            lustreRow.setProperty(realName);

            PosNegPair pair;

            if (pairs.containsKey(realName)) {
                pair = pairs.get(realName);
            } else {
                pair = new PosNegPair();
                pairs.put(realName, pair);
            }

            if (pos) {
                pair.pos = lustreRow;
            } else {
                pair.neg = lustreRow;
            }
        }

        List<CRVSummaryRow> list = new ArrayList<CRVSummaryRow>();

        for (String prop : pairs.keySet()) {
            PosNegPair pair = pairs.get(prop);
            if (pair.pos == null || pair.neg == null) {
                throw new InvalidAtgException(
                        "Mission either pos or neg guarantee for property: " + prop);
            }

            CRVSummaryRow newRow = new CRVSummaryRow();
            newRow.setPropertyName(prop);
            newRow.addRow(prop);
            newRow.addRow(pair.pos.getAnswer());
            if (pair.pos.getBlameAssignment() != null) {
                newRow.addRow(pair.pos.getBlameAssignment().getThreats());
                newRow.addRow(pair.pos.getBlameAssignment().getComponents());
                newRow.addRow(pair.pos.getBlameAssignment().getLinks());
                newRow.addRow(pair.pos.getBlameAssignment().getComponentsUncompromised());
                newRow.addRow(pair.pos.getBlameAssignment().getLinksUncompromised());
            } else {
                newRow.addRow("");
                newRow.addRow("");
                newRow.addRow("");
                newRow.addRow("");
                newRow.addRow("");
            }

            newRow.setCounterExample(pair.pos.getCntExample());
            newRow.setValidTill(pair.pos.getValidTill());

            if (!"falsifiable".equals(pair.pos.getAnswer())) {
                // Valid
                newRow.setTestCase(pair.neg.getCntExample());
            } else {
                // Invalid
                newRow.setTestCase(pair.pos.getCntExample());
            }

            list.add(newRow);
        }

        return list;
    }

    public List<CRVSummaryRow> getTableContents() {
        return tableContents;
    }

    //	public List<IVCNode> getIVC() {
    //		return ivc;
    //	}

    public ModelSet getMustSet() {
        return mustSet;
    }

    public List<Set<ModelNode>> getaIVCs() {
        return aIvcsList;
    }

    public List<Set<ModelNode>> getmIVCs() {
        return mIvcsList;
    }
}
