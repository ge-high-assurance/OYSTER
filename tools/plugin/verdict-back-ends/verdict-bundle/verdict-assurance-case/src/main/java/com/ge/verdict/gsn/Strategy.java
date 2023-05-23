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
package com.ge.verdict.gsn;

import jakarta.xml.bind.annotation.XmlElement;

/**
 * @author Saswata Paul
 */
public class Strategy {

    @XmlElement
    /** An unique Id */
    protected String id;

    @XmlElement
    /** Some text to display */
    protected String displayText;

    @XmlElement
    /** Strategy status true if all sub-goals passed false if even one sub-goal failed */
    protected boolean status;

    @XmlElement
    /** Additional information as string */
    protected String moreInfo;

    @XmlElement
    /** A clickable URL */
    protected String url;

    /**
     * Gets the value of the URL property.
     *
     * @return possible object is {@link String }
     */
    protected String getUrl() {
        return url;
    }

    /**
     * Sets the value of the Url property.
     *
     * @param value allowed object is {@link String }
     */
    protected void setUrl(String value) {
        this.url = value;
    }

    /**
     * Gets the value of the id property.
     *
     * @return possible object is {@link String }
     */
    protected String getId() {
        return id;
    }

    /**
     * Sets the value of the id property.
     *
     * @param value allowed object is {@link String }
     */
    protected void setId(String value) {
        this.id = value;
    }

    /**
     * Gets the value of the displayText property.
     *
     * @return possible object is {@link String }
     */
    protected String getDisplayText() {
        return displayText;
    }

    /**
     * Sets the value of the displayText property.
     *
     * @param value allowed object is {@link String }
     */
    protected void setDisplayText(String value) {
        this.displayText = value;
    }

    /**
     * Gets the value of the status property.
     *
     * @return possible object is {@link boolean }
     */
    protected boolean getStatus() {
        return status;
    }

    /**
     * Sets the value of the status property.
     *
     * @param value allowed object is {@link boolean }
     */
    protected void setStatus(boolean value) {
        this.status = value;
    }

    /**
     * Gets the value of the moreInfo property.
     *
     * @return possible object is {@link String }
     */
    protected String getExtraInfo() {
        return moreInfo;
    }

    /**
     * Sets the value of the extraInfo property.
     *
     * @param value allowed object is {@link String }
     */
    protected void setExtraInfo(String value) {
        this.moreInfo = value;
    }
}
