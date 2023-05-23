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

import com.ge.verdict.vdm.VdmTest;
import com.ge.verdict.vdm.VdmTranslator;
import java.io.File;
import java.io.IOException;
import org.assertj.core.api.Assertions;
import org.junit.Ignore;
import org.junit.Test;
import verdict.vdm.vdm_model.Model;

public class VerdictLustreTranslatorTest {

    @Test
    public void testMarshalToLustre1() throws IOException {
        Model controlModel =
                VdmTranslator.unmarshalFromXml(new File("src/test/resources/vdm-input1.xml"));

        File testFile = File.createTempFile("vdm-model", ".lus");
        testFile.deleteOnExit();
        VerdictLustreTranslator.marshalToLustre(controlModel, testFile);
        Assertions.assertThat(testFile).exists();

        File controlFile = new File("src/test/resources/lustre-output1.lus");
        Assertions.assertThat(testFile).hasSameTextualContentAs(controlFile);
    }

    @Test
    public void testMarshalToLustre2() throws IOException {
        Model controlModel =
                VdmTranslator.unmarshalFromXml(new File("src/test/resources/vdm-input2.xml"));

        File testFile = File.createTempFile("vdm-model", ".lus");
        testFile.deleteOnExit();
        VerdictLustreTranslator.marshalToLustre(controlModel, testFile);
        Assertions.assertThat(testFile).exists();

        File controlFile = new File("src/test/resources/lustre-output2.lus");
        Assertions.assertThat(testFile).hasSameTextualContentAs(controlFile);
    }

    @Ignore
    @Test
    public void testUnmarshalFromLustre() throws IOException {
        File testFile = new File("src/test/resources/vdm-model.lus");
        Model testModel = VerdictLustreTranslator.unmarshalFromLustre(testFile);

        Model controlModel = VdmTest.createControlModel();

        Assertions.assertThat(testModel).usingRecursiveComparison().isEqualTo(controlModel);
    }

    @Ignore
    @Test
    public void testUnmarshalFromInclude() throws IOException {
        File testFile = new File("src/test/resources/include-vdm-model.lus");
        Model testModel = VerdictLustreTranslator.unmarshalFromLustre(testFile);
        testModel.setName("vdm-model.lus");

        Model controlModel = VdmTest.createControlModel();

        Assertions.assertThat(testModel).usingRecursiveComparison().isEqualTo(controlModel);
    }
}
