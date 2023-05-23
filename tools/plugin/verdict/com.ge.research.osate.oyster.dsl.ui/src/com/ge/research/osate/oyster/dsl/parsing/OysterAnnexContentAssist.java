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
package com.ge.research.osate.oyster.dsl.parsing;

import com.ge.research.osate.oyster.dsl.ui.contentassist.OysterProposalProvider;
import com.ge.research.osate.oyster.dsl.ui.internal.DslActivator;
import com.google.inject.Injector;
import java.util.ArrayList;
import java.util.List;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.resource.EObjectAtOffsetHelper;
import org.osate.annexsupport.AnnexContentAssist;
import org.osate.xtext.aadl2.properties.ui.contentassist.PropertiesProposalProvider;

public class OysterAnnexContentAssist implements AnnexContentAssist {
    private final Injector injector =
            DslActivator.getInstance()
                    .getInjector(DslActivator.COM_GE_RESEARCH_OSATE_OYSTER_DSL_OYSTER);

    private PropertiesProposalProvider propPropProv;
    private EObjectAtOffsetHelper offsetHelper;

    protected PropertiesProposalProvider getLinkingService() {
        if (propPropProv == null) {
            propPropProv = injector.getInstance(OysterProposalProvider.class);
        }
        return propPropProv;
    }

    protected EObjectAtOffsetHelper getOffsetHelper() {
        if (offsetHelper == null) {
            offsetHelper = injector.getInstance(EObjectAtOffsetHelper.class);
        }
        return offsetHelper;
    }

    @Override
    public List<String> annexCompletionSuggestions(EObject defaultAnnex, int offset) {
        List<String> res = new ArrayList<>();
        return res;
    }
}
