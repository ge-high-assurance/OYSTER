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
package com.ge.verdict.gsn;

import com.ge.verdict.vdm.VdmTranslator;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import javax.xml.parsers.ParserConfigurationException;
import org.xml.sax.SAXException;
import verdict.vdm.vdm_model.Mission;
import verdict.vdm.vdm_model.Model;

/**
 * @author Saswata Paul
 */
public class GSNInterface {
    static final String SEP = File.separator;

    /**
     * The interface for creating GSN artefacts
     *
     * @param userInput -- the GUI user input with Ids
     * @param gsnOutputDir -- the directory where outputs will be stored
     * @param soteriaOutputDir -- the directory containing Soteria outputs
     * @param caseAadlPath -- the directory containing the AADL files
     * @param xmlFlag -- determines if xml should be created
     * @param soteriaOutputLinkPathPrefix -- a prefix for creating the clickable urls
     * @throws IOException
     * @throws ParserConfigurationException
     * @throws SAXException
     */
    public void runGsnArtifactsGenerator(
            String userInput,
            String gsnOutputDir,
            String soteriaOutputDir,
            String modelAadlPath,
            boolean xmlFlag,
            String soteriaOutputLinkPathPrefix,
            String hostSTEMDir)
            throws IOException, ParserConfigurationException, SAXException {

        File modelXml = new File(gsnOutputDir, "modelXML.xml");
        File cyberOutput = new File(soteriaOutputDir, "ImplProperties.xml");
        File safetyOutput = new File(soteriaOutputDir, "ImplProperties-safety.xml");

        // Fetch the DeliveryDrone model from the XML
        Model xmlModel = VdmTranslator.unmarshalFromXml(modelXml);

        // List of all mission ids
        List<String> missionIds = new ArrayList<>();
        for (Mission aMission : xmlModel.getMission()) {
            missionIds.add(aMission.getId());
        }

        // List of ids to create fragments for
        List<String> forIds = new ArrayList<>();

        if (userInput.equals("ALLMREQKEY")) {
            forIds.addAll(missionIds);
        } else {

            // get individual IDs from the user input
            String[] inputs = userInput.split(";");

            // adding each Id to the list
            for (String id : inputs) {
                forIds.add(id);
            }
        }

        // creating fragments
        for (String rootGoalId : forIds) {
            // create the GSN fragment
            CreateGSN objCreateGSN = new CreateGSN();
            GsnNode gsnFragment =
                    objCreateGSN.gsnCreator(
                            xmlModel,
                            cyberOutput,
                            safetyOutput,
                            modelAadlPath,
                            rootGoalId,
                            soteriaOutputLinkPathPrefix,
                            hostSTEMDir);
            System.out.println("Info: Created GSN fragment for " + rootGoalId);

            // Filenames
            String xmlFilename = rootGoalId + "_GsnFragment.xml";
            String dotFilename = rootGoalId + "_GsnFragment.dot";
            String svgFilename = rootGoalId + "_GsnFragment.svg";

            if (xmlFlag) {
                // Create a file and print the GSN XML
                File gsnXmlFile = new File(gsnOutputDir, xmlFilename);
                Gsn2Xml objGsn2Xml = new Gsn2Xml();
                objGsn2Xml.convertGsnToXML(gsnFragment, gsnXmlFile);
                System.out.println(
                        "Info: Written GSN to xml for "
                                + rootGoalId
                                + ": "
                                + gsnXmlFile.getAbsolutePath());
            }

            // Create a file and print the dot
            File gsnDotFile = new File(gsnOutputDir, dotFilename);
            Gsn2Dot objGsn2Dot = new Gsn2Dot();
            objGsn2Dot.createDot(gsnFragment, gsnDotFile);
            // System.out.println(
            // "Info: Written GSN to dot for "
            // + rootGoalId
            // + ": "
            // + gsnDotFile.getAbsolutePath());

            // generate the svg file using graphviz
            String graphDestination = gsnOutputDir + SEP + svgFilename;
            String dotFileSource = gsnDotFile.getAbsolutePath();

            Dot2GraphViz objDot2GraphViz = new Dot2GraphViz();
            objDot2GraphViz.generateGraph(dotFileSource, graphDestination);
            System.out.println(
                    "Info: Written GSN to svg for " + rootGoalId + ": " + graphDestination);
        }
    }
}
