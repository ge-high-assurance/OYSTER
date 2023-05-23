/*
 * BSD 3-Clause License
 * 
 * Copyright (c) 2020, General Electric Company and Board of Trustees of
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
import jakarta.xml.bind.annotation.XmlAttribute;
import jakarta.xml.bind.annotation.XmlElement;
import jakarta.xml.bind.annotation.XmlType;
import java.util.ArrayList;
import java.util.List;

/**
 * Java class for ViolatedProperty complex type.
 *
 * <p>The following schema fragment specifies the expected content contained within this class.
 *
 * <pre>
 * &lt;complexType name="ViolatedProperty"&gt;
 *   &lt;complexContent&gt;
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType"&gt;
 *       &lt;sequence&gt;
 *         &lt;element name="PropertyDescription" type="{http://www.w3.org/2001/XMLSchema}string" minOccurs="0"/&gt;
 *         &lt;element name="MinA" type="{http://www.example.org/BlameAssignment}MinA"/&gt;
 *         &lt;element name="ApplicableThreat" type="{http://www.example.org/BlameAssignment}Attack" maxOccurs="unbounded"/&gt;
 *       &lt;/sequence&gt;
 *       &lt;attribute name="PropertyID" type="{http://www.w3.org/2001/XMLSchema}string" /&gt;
 *       &lt;attribute name="Status" type="{http://www.w3.org/2001/XMLSchema}boolean" /&gt;
 *     &lt;/restriction&gt;
 *   &lt;/complexContent&gt;
 * &lt;/complexType&gt;
 * </pre>
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(
        name = "ViolatedProperty",
        propOrder = {"propertyDescription", "minA", "applicableThreat"})
public class ViolatedProperty {

    @XmlElement(name = "PropertyDescription")
    protected String propertyDescription;

    @XmlElement(name = "MinA", required = true)
    protected MinA minA;

    @XmlElement(name = "ApplicableThreat", required = true)
    protected List<Attack> applicableThreat;

    @XmlAttribute(name = "PropertyID")
    protected String propertyID;

    @XmlAttribute(name = "Status")
    protected Boolean status;

    /**
     * Gets the value of the propertyDescription property.
     *
     * @return possible object is {@link String }
     */
    public String getPropertyDescription() {
        return propertyDescription;
    }

    /**
     * Sets the value of the propertyDescription property.
     *
     * @param value allowed object is {@link String }
     */
    public void setPropertyDescription(String value) {
        this.propertyDescription = value;
    }

    /**
     * Gets the value of the minA property.
     *
     * @return possible object is {@link MinA }
     */
    public MinA getMinA() {
        return minA;
    }

    /**
     * Sets the value of the minA property.
     *
     * @param value allowed object is {@link MinA }
     */
    public void setMinA(MinA value) {
        this.minA = value;
    }

    /**
     * Gets the value of the applicableThreat property.
     *
     * <p>This accessor method returns a reference to the live list, not a snapshot. Therefore any
     * modification you make to the returned list will be present inside the JAXB object. This is
     * why there is not a <CODE>set</CODE> method for the applicableThreat property.
     *
     * <p>For example, to add a new item, do as follows:
     *
     * <pre>
     * getApplicableThreat().add(newItem);
     * </pre>
     *
     * <p>Objects of the following type(s) are allowed in the list {@link Attack }
     */
    public List<Attack> getApplicableThreat() {
        if (applicableThreat == null) {
            applicableThreat = new ArrayList<Attack>();
        }
        return this.applicableThreat;
    }

    /**
     * Gets the value of the propertyID property.
     *
     * @return possible object is {@link String }
     */
    public String getPropertyID() {
        return propertyID;
    }

    /**
     * Sets the value of the propertyID property.
     *
     * @param value allowed object is {@link String }
     */
    public void setPropertyID(String value) {
        this.propertyID = value;
    }

    /**
     * Gets the value of the status property.
     *
     * @return possible object is {@link Boolean }
     */
    public Boolean isStatus() {
        return status;
    }

    /**
     * Sets the value of the status property.
     *
     * @param value allowed object is {@link Boolean }
     */
    public void setStatus(Boolean value) {
        this.status = value;
    }
}
