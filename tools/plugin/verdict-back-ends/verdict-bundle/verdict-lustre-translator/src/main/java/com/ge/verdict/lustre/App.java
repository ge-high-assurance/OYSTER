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
package com.ge.verdict.lustre;

import edu.uiowa.clc.verdict.lustre.VDM2Lustre;
import java.io.File;
import java.net.URISyntaxException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import verdict.vdm.vdm_model.Model;

public class App {

    private static final Logger LOGGER = LoggerFactory.getLogger(App.class);

    public static void main(String[] args) throws URISyntaxException {

        // Check that we have two arguments
        if (args.length == 2 || args.length == 3) {

            File inputFile = null;
            File vdm_outputFile = null;
            File lustre_outputFile = null;

            if (args.length == 3) {
                // Get the input and output files
                inputFile = new File(args[0]);

                // VDM File
                vdm_outputFile = new File(args[1]);

                // Lustre File
                lustre_outputFile = new File(args[2]);
            } else if (args.length == 2) {
                // Get the input and output files
                inputFile = new File(args[0]);
                // Lustre File
                lustre_outputFile = new File(args[1]);
            }

            // Determine whether we should translate from Lustre to VDM or from VDM to
            // Lustre
            if (inputFile.getName().endsWith(".lus")) {
                Model verdictDataModel = VerdictLustreTranslator.unmarshalFromLustre(inputFile);
                VerdictLustreTranslator.marshalToXml(verdictDataModel, lustre_outputFile);
            } else {

                Model verdictDataModel = VerdictLustreTranslator.unmarshalFromXml(inputFile);

                VDM2Lustre vdm2Lustre = new VDM2Lustre(verdictDataModel);
                verdictDataModel = vdm2Lustre.translate();

                if (args.length == 3) {
                    VerdictLustreTranslator.marshalToXml(verdictDataModel, vdm_outputFile);
                }

                VerdictLustreTranslator.marshalToLustre(verdictDataModel, lustre_outputFile);

                // PrettyPrinter pp = new PrettyPrinter();
                // pp.printProgram(verdictDataModel.getDataflowCode(),
                // lustre_outputFile);
            }
        } else {
            File jarFile =
                    new File(App.class.getProtectionDomain().getCodeSource().getLocation().toURI());
            LOGGER.error(
                    "Usage: java -jar {} <input file> <output file(1).xml> <output file(2).lus>",
                    jarFile.getName());
        }
    }
}
