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
package com.ge.research.osate.verdict.dsl.type;

import java.util.List;

/** The type of a variable or field in threat models. */
public interface VerdictType {
    /**
     * @return the name of the class, e.g. AadlInteger
     */
    public String getFullName();

    /**
     * @return the name that the user may type, e.g. aadlinteger
     */
    public String getShortName();

    /**
     * @param fieldName
     * @return true iff this type has a field with name fieldName
     */
    public boolean hasField(String fieldName);

    /**
     * @return all fields present for this type
     */
    public List<VerdictField> getFields();

    /**
     * @param value
     * @return true iff value is a valid value for this type
     */
    public boolean isValue(String value);

    /**
     * @return true iff this type is a list type
     */
    public boolean isList();

    /**
     * Note that this may be used even on lists.
     *
     * <p>E.g. getListType() on "list of aadlstring" yields "list of list of aadlstring".
     *
     * @return the type corresponding to a list of this type
     */
    public VerdictType getListType();

    /**
     * @param type
     * @return true iff this type is the list type corresponding to type
     */
    public boolean isListOf(VerdictType type);

    /**
     * Some types can have infinitely many possible values, so it doesn't make sense to list all of
     * them. This method is used by content assist to provide suggestions. In particular, the values
     * of enumeration types are provided here.
     *
     * @return a list of possible values for this type
     */
    public List<String> getValueSuggestions();
}
