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

import com.ge.verdict.synthesis.dtree.DLeaf;
import org.apache.commons.math3.fraction.Fraction;
import org.assertj.core.api.Assertions;
import org.junit.Test;

public class DLeafTest {
    @Test
    public void testUnique() {
        DLeaf.Factory factory = new DLeaf.Factory();

        Fraction[] costs = Util.fractionCosts(new double[] {0, 0, 0, 0, 0, 0, 0, 0, 0, 0});

        DLeaf leaf1 = new DLeaf("A", "A", "A", 0, 1, costs, factory);
        DLeaf leaf1Dup = new DLeaf("A", "A", "A", 0, 1, costs, factory);
        DLeaf leaf2 = new DLeaf("A", "B", "A", 0, 1, costs, factory);
        DLeaf leaf3 = new DLeaf("B", "A", "A", 0, 1, costs, factory);

        // should be aliases because the whole point is to uniquely identify instances
        Assertions.assertThat(leaf1.componentDefense == leaf1Dup.componentDefense).isTrue();
        Assertions.assertThat(leaf2.componentDefense == leaf1.componentDefense).isFalse();
        Assertions.assertThat(leaf3.componentDefense == leaf1.componentDefense).isFalse();
    }

    @Test
    public void testLookup() {
        DLeaf.Factory factory = new DLeaf.Factory();

        Fraction[] costs = Util.fractionCosts(new double[] {0, 0, 0, 0, 0, 0, 0, 0, 0, 0});

        DLeaf leaf1 = new DLeaf("A", "A", "A", 0, 1, costs, factory);
        DLeaf leaf2 = new DLeaf("B", "B", "A", 0, 1, costs, factory);

        Assertions.assertThat(factory.fromId(leaf1.componentDefense.id) == leaf1.componentDefense)
                .isTrue();
        Assertions.assertThat(factory.fromId(leaf2.componentDefense.id) == leaf2.componentDefense)
                .isTrue();
        Assertions.assertThat(factory.fromId(leaf1.componentDefense.id) == leaf2.componentDefense)
                .isFalse();
    }

    @Test
    public void testMultipleRequirements() {
        DLeaf.Factory factory = new DLeaf.Factory();

        Fraction[] costs = Util.fractionCosts(new double[] {0, 0, 0, 0, 0, 0, 0, 0, 0, 0});

        DLeaf leaf1 = new DLeaf("A", "A", "A", 0, 1, costs, factory);
        DLeaf leaf2 = new DLeaf("A", "A", "A", 0, 2, costs, factory);

        Assertions.assertThat(leaf1.targetDal).isEqualTo(1);
        Assertions.assertThat(leaf2.targetDal).isEqualTo(2);
    }
}
