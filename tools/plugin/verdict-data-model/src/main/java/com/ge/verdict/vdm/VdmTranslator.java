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
package com.ge.verdict.vdm;

import jakarta.xml.bind.JAXBContext;
import jakarta.xml.bind.JAXBElement;
import jakarta.xml.bind.JAXBException;
import jakarta.xml.bind.Marshaller;
import jakarta.xml.bind.Unmarshaller;
import java.io.File;
import java.io.IOException;
import javax.xml.transform.stream.StreamSource;
import verdict.vdm.vdm_model.Model;
import verdict.vdm.vdm_model.ObjectFactory;

/** Translate a Verdict data model to or from an XML file. */
public class VdmTranslator {

    /**
     * Marshal a Verdict data model to an XML file.
     *
     * @param model Verdict data model to marshal
     * @param outputFile XML file to write to
     */
    public static void marshalToXml(Model model, File outputFile) {
        // Skip and warn if output file can't be created
        if (canWrite(outputFile)) {
            try {
                // Set up model as element to marshal
                ObjectFactory factory = new ObjectFactory();
                JAXBElement<Model> element = factory.createModel(model);
                JAXBContext context = JAXBContext.newInstance(model.getClass());
                Marshaller marshaller = context.createMarshaller();

                // Marshal element to output file
                marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, true);
                marshaller.marshal(element, outputFile);
            } catch (JAXBException e) {
                throw new RuntimeException(e);
            }
        }
    }

    /**
     * Unmarshal a Verdict data model from an XML file.
     *
     * @param inputFile XML file to unmarshal from
     * @return Verdict data model from XML file
     */
    public static Model unmarshalFromXml(File inputFile) {
        try {
            // Set up input file as source to unmarshal from
            StreamSource source = new StreamSource(inputFile);
            JAXBContext context = JAXBContext.newInstance(Model.class);
            Unmarshaller unmarshaller = context.createUnmarshaller();

            // Umarshall model from stream source
            JAXBElement<Model> element = unmarshaller.unmarshal(source, Model.class);
            Model model = element.getValue();
            return model;
        } catch (JAXBException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Check that a output file is writable; log a warning message if not.
     *
     * @param outputFile File to write to
     * @return true If file is writable, false otherwise
     */
    protected static boolean canWrite(File outputFile) {
        File outputDir = outputFile.getParentFile();
        boolean canWrite = true;

        // Ensure output directory exists
        if (outputDir == null) {
            outputDir = new File(".");
        }
        if (canWrite && !outputDir.exists()) {
            if (!outputDir.mkdirs()) {
                System.out.println("Could not create directory " + outputDir.getAbsolutePath());
                canWrite = false;
            }
        }

        // Ensure output file exists
        if (canWrite && !outputFile.exists()) {
            try {
                outputFile.createNewFile();
            } catch (IOException e) {
                System.out.println(
                        "Error creating file " + outputFile.getAbsolutePath() + ": " + e);
                canWrite = false;
            }
        }

        // Check output file is writable
        if (canWrite && !outputFile.canWrite()) {
            System.out.println("Cannot write file " + outputFile.getAbsolutePath());
            canWrite = false;
        }

        return canWrite;
    }
}
