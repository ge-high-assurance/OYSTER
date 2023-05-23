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
import jakarta.xml.bind.annotation.XmlType;
import java.util.ArrayList;
import java.util.List;

/**
 * Java class for MinA complex type.
 *
 * <p>The following schema fragment specifies the expected content contained within this class.
 *
 * <pre>
 * &lt;complexType name="MinA">
 *   &lt;complexContent>
 *     &lt;restriction base="{http://www.w3.org/2001/XMLSchema}anyType">
 *       &lt;sequence>
 *         &lt;element name="Components" type="{http://www.example.org/BlameAssignment}Component" maxOccurs="unbounded" minOccurs="0"/>
 *         &lt;element name="Links" type="{http://www.example.org/BlameAssignment}Link" maxOccurs="unbounded" minOccurs="0"/>
 *       &lt;/sequence>
 *     &lt;/restriction>
 *   &lt;/complexContent>
 * &lt;/complexType>
 * </pre>
 */
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType(
        name = "MinA",
        propOrder = {"components", "links"})
public class MinA {

    @XmlElement(name = "Components")
    protected List<Component> components;

    @XmlElement(name = "Links")
    protected List<Link> links;

    /**
     * Gets the value of the components property.
     *
     * <p>This accessor method returns a reference to the live list, not a snapshot. Therefore any
     * modification you make to the returned list will be present inside the JAXB object. This is
     * why there is not a <CODE>set</CODE> method for the components property.
     *
     * <p>For example, to add a new item, do as follows:
     *
     * <pre>
     * getComponents().add(newItem);
     * </pre>
     *
     * <p>Objects of the following type(s) are allowed in the list {@link Component }
     */
    public List<Component> getComponents() {
        if (components == null) {
            components = new ArrayList<Component>();
        }
        return this.components;
    }

    /**
     * Gets the value of the links property.
     *
     * <p>This accessor method returns a reference to the live list, not a snapshot. Therefore any
     * modification you make to the returned list will be present inside the JAXB object. This is
     * why there is not a <CODE>set</CODE> method for the links property.
     *
     * <p>For example, to add a new item, do as follows:
     *
     * <pre>
     * getLinks().add(newItem);
     * </pre>
     *
     * <p>Objects of the following type(s) are allowed in the list {@link Link }
     */
    public List<Link> getLinks() {
        if (links == null) {
            links = new ArrayList<Link>();
        }
        return this.links;
    }

    public String toString() {

        StringBuffer strBuf = new StringBuffer();
        boolean print_flag = false;

        if (components.size() > 0) {
            strBuf.append("{");
            for (Component comp : components) {

                if (comp.isCompromised()) {

                    strBuf.append(comp.getComponentID() + ",");
                    print_flag = true;
                }
            }
            strBuf.setLength(strBuf.length() - 1);
            if (print_flag) {
                strBuf.append("}");
                print_flag = false;
            }
        }

        if (links.size() > 0) {

            strBuf.append("{");
            for (Link link : links) {
                if (link.isCompromised()) {
                    strBuf.append(link.getLinkID() + ",");
                    print_flag = true;
                }
            }
            strBuf.setLength(strBuf.length() - 1);

            if (print_flag) {
                strBuf.append("}");
                print_flag = false;
            }
        }

        return strBuf.toString();
    }
}
