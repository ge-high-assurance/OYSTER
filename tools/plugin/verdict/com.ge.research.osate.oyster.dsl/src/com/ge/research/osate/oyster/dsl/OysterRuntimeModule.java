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
package com.ge.research.osate.oyster.dsl;

import com.ge.research.osate.oyster.dsl.generator.NullGenerator;
import com.ge.research.osate.oyster.dsl.scoping.OysterResourceDescriptionStrategy;
import com.ge.research.osate.oyster.dsl.serializer.OysterCrossReferenceSerializer;
import com.ge.research.osate.oyster.dsl.serializer.OysterSerializer;
import com.google.inject.Binder;
import org.eclipse.xtext.generator.IGenerator;
import org.eclipse.xtext.resource.IDefaultResourceDescriptionStrategy;
import org.eclipse.xtext.serializer.ISerializer;

/**
 * Use this class to register components to be used at runtime / without the Equinox extension
 * registry.
 */
public class OysterRuntimeModule
        extends com.ge.research.osate.oyster.dsl.AbstractOysterRuntimeModule {

    @Override
    public void configure(final Binder binder) {
        super.configure(binder);
        binder.bind(IDefaultResourceDescriptionStrategy.class)
                .to(OysterResourceDescriptionStrategy.class);
    }

    public Class<? extends IGenerator> bindIGenerator() {
        return NullGenerator.class;
    }

    public Class<? extends org.eclipse.xtext.resource.EObjectAtOffsetHelper>
            bindEObjectAtOffsetHelper() {
        return org.osate.xtext.aadl2.util.Aadl2EObjectAtOffsetHelper.class;
    }

    @Override
    public Class<? extends ISerializer> bindISerializer() {
        return OysterSerializer.class;
    }

    // @SuppressWarnings("restriction")
    public Class<? extends org.eclipse.xtext.serializer.tokens.ICrossReferenceSerializer>
            bindICrossReferenceSerializer() {
        return OysterCrossReferenceSerializer.class;
    }

    /**
     * @since 3.0
     */
    public Class<? extends org.eclipse.xtext.resource.IDefaultResourceDescriptionStrategy>
            bindIDefaultResourceDescriptionStrategy() {
        return OysterResourceDescriptionStrategy.class;
    }
}
