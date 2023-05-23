/*
 * BSD 3-Clause License
 * 
 * Copyright (c) 2023, General Electric Company and Board of Trustees of
 * the University of Iowa.
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
package edu.uiowa.clc.verdict.merit;

import java.io.File;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import org.apache.commons.lang3.StringUtils;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class MeritAssignment {

    File kind2OutputFile = null;

    public MeritAssignment(File kind2OutputFile) {
        this.kind2OutputFile = kind2OutputFile;
    }

    public void readAndPrintInfo() {
        DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
        try {
            DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
            Document doc = dBuilder.parse(kind2OutputFile);
            doc.getDocumentElement().normalize();

            NodeList MESList = doc.getElementsByTagName("ModelElementSet");

            for (int i = 0; i < MESList.getLength(); ++i) {
                Node MESNode = MESList.item(i);

                if (MESNode.getNodeType() != Node.ELEMENT_NODE) continue;

                Element MESElement = (Element) MESNode;
                NodeList nList = MESElement.getElementsByTagName("Node");

                for (int j = 0; j < nList.getLength(); ++j) {
                    Node nNode = nList.item(j);

                    if (nNode.getNodeType() != Node.ELEMENT_NODE) continue;

                    Element nodeElement = (Element) nNode;

                    String element_name = nodeElement.getAttribute("name");

                    // element_name = element_name.replaceAll("_port_", ".");
                    element_name = element_name.replace("_dot_", ".");
                    element_name = element_name.replace("_double_colon_", "::");

                    System.out.println("Component " + element_name + ":");

                    NodeList eList = nodeElement.getElementsByTagName("Element");

                    for (int k = 0; k < eList.getLength(); ++k) {
                        Node eNode = eList.item(k);

                        if (eNode.getNodeType() != Node.ELEMENT_NODE) continue;

                        Element elementElement = (Element) eNode;

                        System.out.print("  ");

                        String category =
                                StringUtils.capitalize(elementElement.getAttribute("category"))
                                        .replace('_', ' ');

                        System.out.print(category);

                        System.out.println(" '" + elementElement.getAttribute("name") + "'");

                        // System.out.print(" '" + elementElement.getAttribute("name") + "'");

                        // String line = elementElement.getAttribute("line");
                        // String column =
                        // elementElement.getAttribute("column");
                        //
                        // System.out.println(" at position [l" + line + "c"
                        // + column + "]");
                    }

                    System.out.println();
                }
            }

        } catch (Exception e) {
            System.err.println("Error reading .xml file: " + e.getMessage());
            e.printStackTrace();
        }
    }
}
