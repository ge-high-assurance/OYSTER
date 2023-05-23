/*
 * BSD 3-Clause License
 * 
 * Copyright (c) 2019-2020, General Electric Company and Board of Trustees of
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
package edu.uiowa.clc.verdict.blm;

import jakarta.xml.bind.annotation.XmlAccessType;
import jakarta.xml.bind.annotation.XmlAccessorType;
import jakarta.xml.bind.annotation.XmlElement;
import jakarta.xml.bind.annotation.XmlSchemaType;
import jakarta.xml.bind.annotation.XmlType;

/**
 * Java class for Attack complex type.
 *
 * <p>The following schema fragment specifies the expected content contained within this class.
 *
 * <pre>
 * &lt;complexType name="Attack">
 *   &lt;complexContent>
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *       &lt;sequence>
 *         &lt;element name="AttackId" type="{http://www.example.org/BlameAssignment}AttackType"/>
 *         &lt;element name="AttackDescription" type="{http://www.w3.org/2001/XMLSchema}string"/>
 *       &lt;/sequence>
 *     &lt;/restriction>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(
        name = "Attack",
        propOrder = {"attackId", "attackDescription"})
public class Attack {

    @XmlElement(name = "AttackId", required = true)
    @XmlSchemaType(name = "string")
    protected AttackType attackId;

    @XmlElement(name = "AttackDescription", required = true)
    protected String attackDescription;

    /**
     * Gets the value of the attackId property.
     *
     * @return possible object is {@link AttackType }
     */
    public AttackType getAttackId() {
        return attackId;
    }

    /**
     * Sets the value of the attackId property.
     *
     * @param value allowed object is {@link AttackType }
     */
    public void setAttackId(AttackType value) {
        this.attackId = value;
    }

    /**
     * Gets the value of the attackDescription property.
     *
     * @return possible object is {@link String }
     */
    public String getAttackDescription() {

        if (attackId == AttackType.LS) {
            attackDescription = "Location Spoofing";
        } else if (attackId == AttackType.LB) {
            attackDescription = "Logic Bomb";
        } else if (attackId == AttackType.HT) {
            attackDescription = "Hardware Trojan";
        } else if (attackId == AttackType.SV) {
            attackDescription = "Software Virus/Trojan";
        } else if (attackId == AttackType.RI) {
            attackDescription = "Remote Code Injection";
        } else if (attackId == AttackType.NI) {
            attackDescription = "Network Injection";
        } else if (attackId == AttackType.IT) {
            attackDescription = "Insider Threat";
        } else if (attackId == AttackType.OT) {
            attackDescription = "Outsider Threat";
        }

        return attackDescription;
    }

    /**
     * Sets the value of the attackDescription property.
     *
     * @param value allowed object is {@link String }
     */
    public void setAttackDescription(String value) {
        this.attackDescription = value;
    }

    public String toString() {

        if (attackDescription == null) {
            attackDescription = "";
        }

        return attackDescription;
    }
}
