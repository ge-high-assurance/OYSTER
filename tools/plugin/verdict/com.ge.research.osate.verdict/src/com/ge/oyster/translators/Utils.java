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
package com.ge.oyster.translators;

import org.eclipse.emf.ecore.EObject;
import org.osate.aadl2.AbstractNamedValue;
import org.osate.aadl2.ModalPropertyValue;
import org.osate.aadl2.PropertyAssociation;
import org.osate.aadl2.PropertyExpression;
import org.osate.aadl2.Subcomponent;
import org.osate.aadl2.SystemImplementation;
import org.osate.aadl2.SystemType;
import org.osate.aadl2.impl.EnumerationLiteralImpl;
import org.osate.aadl2.impl.NamedValueImpl;

import java.util.List;

public class Utils {

    public static boolean isType(String comp, IMATypes type, List<EObject> aadlObjects) {
        for (EObject object : aadlObjects) {
            if (object instanceof SystemImplementation) {
                SystemImplementation sysImpl = (SystemImplementation) object;
                if (sysImpl.getName().equals("IMA.Impl")) {
                    List<Subcomponent> subcomponents = sysImpl.getAllSubcomponents();
                    for (Subcomponent sub : subcomponents) {
                        if (sub.getName().equals(comp)) {
                            SystemType sysType = (SystemType) sub.getComponentType();
                            for (PropertyAssociation pa : sysType.getOwnedPropertyAssociations()) {
                                if (pa.getProperty().getName().equals("componentType")) {
                                    List<ModalPropertyValue> modalValues = pa.getOwnedValues();
                                    for (ModalPropertyValue modalValue : modalValues) {
                                        PropertyExpression pexp = modalValue.getOwnedValue();
                                        if (pexp instanceof NamedValueImpl) {
                                            AbstractNamedValue value =
                                                    ((NamedValueImpl) pexp).getNamedValue();
                                            if (value instanceof EnumerationLiteralImpl) {
                                                String componentyType =
                                                        ((EnumerationLiteralImpl) value)
                                                                .getFullName();
                                                if (componentyType.equals(type.getValue())) {
                                                    return true;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }
}
