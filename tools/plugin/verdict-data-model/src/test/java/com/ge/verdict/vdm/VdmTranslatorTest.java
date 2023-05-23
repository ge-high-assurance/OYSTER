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

import java.io.File;
import java.io.IOException;
import org.assertj.core.api.Assertions;
import org.junit.Ignore;
import org.junit.Test;
import org.xmlunit.assertj.XmlAssert;
import verdict.vdm.vdm_model.Model;

public class VdmTranslatorTest {

    @Ignore
    @Test
    public void testMarshalToXml() throws IOException {
        Model controlModel = VdmTest.createControlModel();

        File testFile = File.createTempFile("vdm-model", ".xml");
        testFile.deleteOnExit();
        VdmTranslator.marshalToXml(controlModel, testFile);
        Assertions.assertThat(testFile).exists();

        File controlFile = new File("src/test/resources/vdm-model.xml");
        XmlAssert.assertThat(testFile).and(controlFile).normalizeWhitespace().areIdentical();
    }

    @Ignore
    @Test
    public void testUnmarshalFromXml() throws IOException {
        File testFile = new File("src/test/resources/vdm-model.xml");
        Model testModel = VdmTranslator.unmarshalFromXml(testFile);

        Model controlModel = VdmTest.createControlModel();
        Assertions.assertThat(testModel).usingRecursiveComparison().isEqualTo(controlModel);
    }

    @Test
    public void testXml() throws IOException {
        File controlFile = new File("src/test/resources/vdm-model.xml");
        Model controlModel = VdmTranslator.unmarshalFromXml(controlFile);

        File testFile = File.createTempFile("vdm-model", ".xml");
        testFile.deleteOnExit();
        VdmTranslator.marshalToXml(controlModel, testFile);
        Assertions.assertThat(testFile).exists();
    }
}
