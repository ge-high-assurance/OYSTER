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
package com.ge.verdict.mbas;

import java.io.File;
import java.net.URISyntaxException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import verdict.vdm.vdm_model.Model;

public class App {

    private static final Logger LOGGER = LoggerFactory.getLogger(App.class);

    public static boolean isValidDir(String dirName) {
        if (dirName == null) {
            System.out.println("Input directory name is null!");
            return false;
        }

        File dir = new File(dirName);

        if (!dir.exists()) {
            System.out.println("Directory: " + dirName + " does not exist!");
            return false;
        }
        if (!dir.isDirectory()) {
            System.out.println(dirName + " is not a directory!");
            return false;
        }
        return true;
    }

    public static boolean isValidXMLFile(String fileName) {
        if (fileName == null) {
            System.out.println("Input directory name is null!");
            return false;
        }

        File file = new File(fileName);

        if (!file.exists()) {
            System.out.println("File: " + fileName + " does not exist!");
            return false;
        }
        if (!file.isFile()) {
            System.out.println(fileName + " is not a file!");
            return false;
        }
        return true;
    }

    public static void main(String[] args) throws URISyntaxException {
        // Check that we have three arguments
        // args[0]: input aadl file path, args[1]: output STEM inputs, args[2]: output
        // Soteria++
        // inputs
        if (args.length != 3) {
            File jarFile =
                    new File(App.class.getProtectionDomain().getCodeSource().getLocation().toURI());
            LOGGER.error(
                    "Usage: java -jar {} <input file> <STEM output folder> <Soteria++ output folder>",
                    jarFile.getName());
        } else {
            if (isValidXMLFile(args[0])) {
                if (isValidDir(args[1]) && isValidDir(args[2])) {
                    File inputFile = new File(args[0]);

                    // Translate VDM to Mbas inputs
                    Model model = VDM2CSV.unmarshalFromXml(inputFile);
                    VDM2CSV.marshalToMbasInputs(model, args[0], args[1], args[2]);
                }
            }
        }
    }
}
