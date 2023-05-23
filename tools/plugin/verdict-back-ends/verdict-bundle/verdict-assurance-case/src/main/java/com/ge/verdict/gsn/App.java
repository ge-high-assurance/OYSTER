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

import java.io.IOException;
import javax.xml.parsers.ParserConfigurationException;
import org.xml.sax.SAXException;

/**
 * @author Saswata Paul
 */
public class App {

    /**
     * This main method can be used for independently using the security gsn interface
     *
     * @param args
     * @throws IOException
     * @throws SAXException
     * @throws ParserConfigurationException
     */
    public static void main(String[] args)
            throws IOException, ParserConfigurationException, SAXException {

        if (args.length != 6) {
            System.out.println("Argument Error: Invalid number of arguments provided.");
        } else {
            String userInput = args[0];
            String gsnOutputDir = args[1];
            String soteriaOutputDir = args[2];
            String modelAadlPath = args[3];
            String soteriaOutputLinkPathPrefix = args[4];
            String hostSTEMDir = args[5];

            boolean securityCaseFlag = true;
            boolean xmlFlag = false;

            // calling the security gsn creating interface
            SecurityGSNInterface interfaceObj = new SecurityGSNInterface();

            interfaceObj.runGsnArtifactsGenerator(
                    userInput,
                    gsnOutputDir,
                    soteriaOutputDir,
                    modelAadlPath,
                    securityCaseFlag,
                    xmlFlag,
                    soteriaOutputLinkPathPrefix,
                    hostSTEMDir);
        }
    }
}
