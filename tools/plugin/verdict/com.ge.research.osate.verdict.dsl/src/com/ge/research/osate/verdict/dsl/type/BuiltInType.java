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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * A type that is provided by default. Used in threat models. Currently system, connection, port,
 * and portDirection.
 */
public class BuiltInType implements VerdictType {
    private String fullName, shortName;
    private List<VerdictField> fields;

    /** If present, then this type is a list containing the type listChild. */
    private Optional<BuiltInType> listChild;

    /** The list of value suggestions. Currently used only for enumeration types. */
    private List<String> values;

    public BuiltInType(String fullName) {
        this.fullName = fullName;
        this.shortName = this.fullName;
        fields = new ArrayList<>();
        values = new ArrayList<>();
        listChild = Optional.empty();
    }

    public BuiltInType addField(String name, VerdictType type) {
        fields.add(new VerdictFieldImpl(name, type));
        return this;
    }

    public BuiltInType addValue(String name) {
        values.add(name);
        return this;
    }

    /**
     * Prevent concurrency issues by making the internal lists unmodifiable.
     *
     * <p>It is unclear why these issues happened in the first place, but this definitely makes the
     * issue appear where it should (where lists are being modified, not where they are being used).
     */
    public void lock() {
        values = Collections.unmodifiableList(values);
        fields = Collections.unmodifiableList(fields);
    }

    /**
     * @return a new instance corresponding to the list type of this type
     */
    private BuiltInType createListType() {
        BuiltInType base = new BuiltInType(fullName);
        base.listChild = Optional.of(this);
        base.fullName = "list of " + fullName;
        base.shortName = "list of " + shortName;
        return base;
    }

    @Override
    public String getFullName() {
        return fullName;
    }

    @Override
    public String getShortName() {
        return shortName;
    }

    @Override
    public boolean hasField(String fieldName) {
        return fields.stream().anyMatch(field -> field.getName().equals(fieldName));
    }

    @Override
    public List<VerdictField> getFields() {
        return fields;
    }

    @Override
    public boolean isValue(String value) {
        return values.contains(value);
    }

    @Override
    public boolean isList() {
        return listChild.isPresent();
    }

    /** This creates a new instance on every invocation. */
    @Override
    public VerdictType getListType() {
        return createListType();
    }

    @Override
    public boolean isListOf(VerdictType type) {
        return this.equals(type.getListType());
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof BuiltInType) {
            BuiltInType otherBuiltIn = (BuiltInType) other;
            // Shallow field comparison to prevent infinite loops
            return otherBuiltIn.getFullName().equals(fullName)
                    && VerdictField.equalFields(fields, otherBuiltIn.getFields())
                    && otherBuiltIn.listChild.equals(listChild);
        }

        return false;
    }

    @Override
    public List<String> getValueSuggestions() {
        return values;
    }
}
