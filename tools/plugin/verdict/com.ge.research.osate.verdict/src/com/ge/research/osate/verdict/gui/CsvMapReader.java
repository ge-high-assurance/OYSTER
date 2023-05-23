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
package com.ge.research.osate.verdict.gui;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class CsvMapReader {
    /**
     * Used to read a CSV file with at least two columns, and build a map from one column (the keys)
     * to another (the values). The key and value columns are identified by headers. Cells may
     * contain semicolons to separate multiple key-value pairs in the same row.
     *
     * <p>This is currently used for reading CAPEC.csv and Defenses2NIST.csv.
     *
     * @param file
     * @param keyColumn
     * @param valueColumn
     * @return
     */
    public static Map<String, String> readCsvMap(File file, String keyColumn, String valueColumn) {
        List<String> lines;
        try {
            lines = Files.readAllLines(file.toPath());
        } catch (IOException e) {
            System.err.println("Failed to read CSV: " + file.getAbsolutePath());
            e.printStackTrace();
            return Collections.emptyMap();
        }
        if (lines.isEmpty()) {
            System.err.println("Failed to read CSV, empty: " + file.getAbsolutePath());
            return Collections.emptyMap();
        }

        int keyIndex = -1, valueIndex = -1;
        String[] headers = lines.get(0).split(",");
        for (int i = 0; i < headers.length; i++) {
            if (keyColumn.equals(headers[i])) {
                keyIndex = i;
            } else if (valueColumn.equals(headers[i])) {
                valueIndex = i;
            }
        }
        if (keyIndex == -1 || valueIndex == -1) {
            System.err.println(
                    "Failed to read CSV, missing expected header: " + file.getAbsolutePath());
            return Collections.emptyMap();
        }

        Map<String, String> result = new LinkedHashMap<>();

        for (int i = 1; i < lines.size(); i++) {
            String[] cells = lines.get(i).split(",");
            if (keyIndex >= cells.length || valueIndex >= cells.length) {
                System.err.println(
                        "Failed to read CSV, missing cells on line "
                                + i
                                + ": "
                                + file.getAbsolutePath());
                continue;
            }
            String[] keys = cells[keyIndex].split(";");
            String[] values = cells[valueIndex].split(";");
            if (keys.length != values.length) {
                System.err.println(
                        "Failed to read CSV, inequal keys and values on line "
                                + i
                                + ": "
                                + file.getAbsolutePath());
                continue;
            }
            for (int j = 0; j < keys.length; j++) {
                result.put(keys[j].replace("\"", ""), values[j].replace("\"", ""));
            }
        }

        return result;
    }
}
