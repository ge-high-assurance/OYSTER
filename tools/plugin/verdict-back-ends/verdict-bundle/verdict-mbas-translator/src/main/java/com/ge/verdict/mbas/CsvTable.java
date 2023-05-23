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
package com.ge.verdict.mbas;

import java.util.ArrayList;
import java.util.List;

public class CsvTable {
    private String[] tags;
    private List<String[]> contents;

    public CsvTable(String[] tags) {
        this.tags = tags;
        this.contents = new ArrayList<>();
    }

    /**
     * Write a line to the CSV table.
     *
     * @param row Line of strings to be written to the table
     * @return Successfully written or not
     */
    public boolean writeToTable(String[] row) {
        // Check to see if the entered row is consistent with the tags.
        if (row == null || row.length != tags.length) {
            return false;
        }
        contents.add(row);
        return true;
    }

    /**
     * Print the CsvTable object to CSV string.
     *
     * @return CSV string
     */
    public String printToCSV() {
        StringBuilder sb = new StringBuilder();
        // Print tags first
        sb.append(printLine(tags));
        // Then print contents row by row
        for (String[] row : contents) {
            sb.append(printLine(row));
        }
        return sb.toString();
    }

    /**
     * Print array of strings to CSV string.
     *
     * @param row Line of strings to be printed
     * @return CSV string
     */
    private String printLine(String[] row) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < row.length; i++) {
            String element = row[i];
            sb.append(element);
            if (i != row.length - 1) {
                sb.append(',');
            } else {
                sb.append('\n');
            }
        }
        return sb.toString();
    }
}
