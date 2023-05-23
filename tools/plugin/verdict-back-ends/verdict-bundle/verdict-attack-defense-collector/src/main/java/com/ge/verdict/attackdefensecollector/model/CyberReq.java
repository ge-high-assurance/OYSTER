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
package com.ge.verdict.attackdefensecollector.model;

import com.ge.verdict.attackdefensecollector.Prob;
import java.util.ArrayList;
import java.util.List;

/**
 * A cyber requirement. Comprised of a name, a mission to which it belongs, a severity (probability
 * target), and a condition cyber expression.
 *
 * <p>This class has different constructors for VDM and CSV input. The VDM constructor is more
 * powerful and is intended for use when the VDM input method is implemented. CSV input does not
 * support arbitrary logical expressions, for example.
 */
public class CyberReq {
    /** The name of the cyber requirement. */
    private String name;
    /** The name of the mission to which this cyber requirement belongs. */
    private String mission;
    /** The severity (probability target) of this cyber requirement. */
    private int severityDal;
    /** The condition cyber expression. */
    private CyberExpr condition;

    /**
     * Construct a new cyber requirement. (Used for VDM input.)
     *
     * @param name the name of the cyber requirement
     * @param mission the mission to which this cyber requirement belongs
     * @param severity the severity (probability target)
     * @param condition the condition cyber expression
     */
    public CyberReq(String name, String mission, int severity, CyberExpr condition) {
        this.name = name;
        this.mission = mission;
        this.severityDal = severity;
        this.condition = condition;
    }

    /**
     * Construct a new cyber requirement. (Used for CSV input.)
     *
     * @param name the name of the cyber requirement
     * @param mission the mission to which this cyber requirement belongs
     * @param severityDal the severity (probability target)
     * @param portName the condition port name
     * @param portCia the condition port CIA concern
     */
    public CyberReq(String name, String mission, int severityDal, String portName, CIA portCia) {
        this.name = name;
        this.mission = mission;
        this.severityDal = severityDal;
        condition = new PortConcern(portName, portCia);
    }

    /**
     * Modify the existing condition to be disjoint with the specified expression, i.e. if the
     * existing condition is "A" and the specified expression is "B", the new condition is "A or B".
     *
     * <p>This method is used by the CSV loading method because cyber requirements are split over
     * multiple rows.
     *
     * @param term the expression to add to the disjunction
     */
    public void addDisjunct(CyberExpr term) {
        if (condition instanceof CyberOr) {
            // If we already have an OR, then we can simply add another child
            ((CyberOr) condition).getCyberExprs().add(term);
        } else {
            // Otherwise, make a new OR expression
            List<CyberExpr> list = new ArrayList<>();
            list.add(condition);
            list.add(term);
            condition = new CyberOr(list);
        }
    }

    /**
     * @return the name of this cyber requirement
     */
    public String getName() {
        return name;
    }

    /**
     * @return the name of the mission to which this cyber requirement belongs
     */
    public String getMission() {
        return mission;
    }

    /**
     * @return the severity (probability target) of this cyber requirement
     */
    public Prob getSeverity() {
        return Prob.fromDal(severityDal);
    }

    /**
     * @return the severity DAL (target DAL) of this cyber requirement
     */
    public int getSeverityDal() {
        return severityDal;
    }

    /**
     * @return the condition cyber expression under which this cyber requirement is triggered
     */
    public CyberExpr getCondition() {
        return condition;
    }
}
