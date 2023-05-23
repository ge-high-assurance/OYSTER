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
package com.ge.verdict.synthesis;

import java.io.File;
import org.apache.commons.math3.fraction.Fraction;
import org.assertj.core.api.Assertions;
import org.junit.Test;

public class CostModelTest {
    @Test
    public void testLoad() {
        CostModel costs =
                new CostModel(new File(getClass().getResource("sampleCosts.xml").getPath()));
        Assertions.assertThat(costs.cost("D1", "C1", 1)).isEqualTo(new Fraction(1));
        Assertions.assertThat(costs.cost("D1", "C1", 2)).isEqualTo(new Fraction(2));
        Assertions.assertThat(costs.cost("D2", "C2", 3)).isEqualTo(new Fraction(3));
    }

    @Test
    public void testDefaults() {
        CostModel costs =
                new CostModel(new File(getClass().getResource("defaultCosts.xml").getPath()));
        Assertions.assertThat(costs.cost("A", "A", 1)).isEqualTo(new Fraction(16));
        Assertions.assertThat(costs.cost("A", "B", 1)).isEqualTo(new Fraction(15));
        Assertions.assertThat(costs.cost("B", "A", 1)).isEqualTo(new Fraction(14));
        Assertions.assertThat(costs.cost("A", "A", 2)).isEqualTo(new Fraction(26));
        Assertions.assertThat(costs.cost("B", "B", 1)).isEqualTo(new Fraction(12));
        Assertions.assertThat(costs.cost("A", "B", 2)).isEqualTo(new Fraction(22));
        Assertions.assertThat(costs.cost("B", "A", 2)).isEqualTo(new Fraction(20));
        Assertions.assertThat(costs.cost("B", "B", 2)).isEqualTo(new Fraction(18));
    }
}
