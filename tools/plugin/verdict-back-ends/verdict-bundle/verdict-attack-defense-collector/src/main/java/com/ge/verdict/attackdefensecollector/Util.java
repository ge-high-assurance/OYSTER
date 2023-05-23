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
package com.ge.verdict.attackdefensecollector;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Various utility functions. */
public class Util {
    /**
     * Given a mapping of keys to lists of values, add a new element to the list corresponding to
     * the given key, adding the binding to the map if necessary.
     *
     * @param <K> the type of keys
     * @param <V> the type of values
     * @param map the map from keys to lists of values
     * @param key the key
     * @param value the new value
     */
    public static <K, V> void putListMap(Map<K, List<V>> map, K key, V value) {
        if (!map.containsKey(key)) {
            map.put(key, new ArrayList<>());
        }
        map.get(key).add(value);
    }

    /**
     * Given a mapping of keys to sets of values, add a new element to the set corresponding to the
     * given key, adding the binding to the map if necessary.
     *
     * @param <K> the type of keys
     * @param <V> the type of values
     * @param map the map from keys to sets of values
     * @param key the key
     * @param value the new value
     */
    public static <K, V> void putSetMap(Map<K, Set<V>> map, K key, V value) {
        if (!map.containsKey(key)) {
            map.put(key, new LinkedHashSet<>());
        }
        map.get(key).add(value);
    }

    /**
     * Given a mapping of keys to lists of values, retrieve the list of values corresponding to the
     * given key, or an empty list if the key is not bound.
     *
     * @param <K> the type of keys
     * @param <V> the type of values
     * @param map the map from keys to lists of values
     * @param key the key
     * @return the list of values bound to the key
     */
    public static <K, V> List<V> guardedGet(Map<K, List<V>> map, K key) {
        if (!map.containsKey(key)) {
            return Collections.emptyList();
        }
        return map.get(key);
    }
}
