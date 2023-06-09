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
package com.ge.research.osate.verdict.gui;

import java.io.Serializable;

/** Author: Daniel Larraz Date: Aug 6, 2020 */
public class ModelElement implements Serializable, Cloneable {

    private static final long serialVersionUID = 1L;
    private Category categ;
    private String name;

    public enum Category {
        ASSERTION {
            @Override
            public String toString() {
                return "Assertion";
            }
        },
        ASSUMPTION {
            @Override
            public String toString() {
                return "Assumption";
            }
        },
        ENSURE {
            @Override
            public String toString() {
                return "Ensure";
            }
        },
        EQUATION {
            @Override
            public String toString() {
                return "Equation";
            }
        },
        GUARANTEE {
            @Override
            public String toString() {
                return "Guarantee";
            }
        },
        NODE_CALL {
            @Override
            public String toString() {
                return "Node call";
            }
        },
        REQUIRE {
            @Override
            public String toString() {
                return "Require";
            }
        }
    }

    public void setCategory(Category categ) {
        this.categ = categ;
    }

    public Category getCategory() {
        return categ;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public boolean isAssumption() {
        return categ == Category.ASSUMPTION;
    }
}
