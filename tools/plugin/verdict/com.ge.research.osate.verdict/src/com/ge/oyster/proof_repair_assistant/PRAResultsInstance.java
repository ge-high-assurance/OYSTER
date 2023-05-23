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
package com.ge.oyster.proof_repair_assistant;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/**
 * The result of the proof repair assistant operation. This class is deserializable to XML. It This
 * class is also fully immutable.
 */
public class PRAResultsInstance {

    /** The list of remove recommendations. */
    public final List<RemoveItem> removes;

    /** The list of add recommendations. */
    public final List<AddItem> adds;

    // these are the names of the XML tags

    private static final String ROOT_TAG = "Repair";

    private static final String ITEM_TAG = "RepairNode";
    private static final String ITEM_COMPONENT = "component";
    private static final String ITEM_ACTION = "action";

    private static final String LEMMA_TYPE = "lemma";
    private static final String LIFT_TYPE = "lift";
    private static final String ASSERT_TYPE = "assert";
    private static final String NODE_TYPE = "node";
    private static final String FUNCTION_TYPE = "function";
    private static final String CONST_TYPE = "const";
    private static final String PROPERTY_TYPE = "property";
    private static final String EQ_TYPE = "eq";
    private static final String GUARANTEE_TYPE = "guarantee";
    private static final String ASSUME_TYPE = "assume";

    /** A single remove recommendation. */
    public static class RemoveItem {
        /** The component/connection to which a recommendation applies. */
        public final String component;
        /** The type of property to which a recommendation applies. */
        public final String type;
        /** The name of the property to be removed. */
        public final String name;

        public RemoveItem(String component, String type, String name) {
            super();
            this.component = component;
            this.type = type;
            this.name = name;
        }

        @Override
        public int hashCode() {
            return Objects.hash(component, type, name);
        }

        @Override
        public boolean equals(Object other) {
            if (other instanceof RemoveItem) {
                RemoveItem otherItem = (RemoveItem) other;
                return component.equals(otherItem.component)
                        && type.equals(otherItem.type)
                        && name == otherItem.name;
            }
            return false;
        }
    }

    /** A single add recommendation. */
    public static class AddItem {
        /** The component/connection to which a recommendation applies. */
        public final String component;
        /** The type of statement that the recommendation wants to add. */
        public final PRATypeNode node;

        public AddItem(String component, PRATypeNode node) {
            super();
            this.component = component;
            this.node = node;
        }

        @Override
        public int hashCode() {
            return Objects.hash(component, node);
        }

        @Override
        public boolean equals(Object other) {
            if (other instanceof RemoveItem) {
                AddItem otherItem = (AddItem) other;
                return component.equals(otherItem.component) && node == otherItem.node;
            }
            return false;
        }
    }

    public PRAResultsInstance(List<RemoveItem> removes, List<AddItem> adds) {
        super();
        this.removes = Collections.unmodifiableList(removes);
        this.adds = Collections.unmodifiableList(adds);
    }

    /**
     * Deserialize a results instance from an XML file.
     *
     * @param file the XML file
     * @return the deserialized results instance
     * @throws SAXException
     * @throws IOException
     * @throws ParserConfigurationException
     */
    public static PRAResultsInstance fromFile(File file)
            throws SAXException, IOException, ParserConfigurationException {
        Document doc = DocumentBuilderFactory.newInstance().newDocumentBuilder().parse(file);
        Element root = doc.getDocumentElement();

        List<RemoveItem> removes = new ArrayList<>();
        List<AddItem> adds = new ArrayList<>();

        NodeList nodes = root.getElementsByTagName(ITEM_TAG);
        for (int i = 0; i < nodes.getLength(); i++) {
            Node node = nodes.item(i);
            if (node instanceof Element) {
                Element elem = (Element) node;

                if (elem.getAttribute(ITEM_ACTION).equals("add")) {
                    NodeList components = elem.getElementsByTagName("component");
                    Element component = (Element) components.item(0);
                    final String componentVal = component.getNodeValue();

                    if (elem.getElementsByTagName(LEMMA_TYPE).getLength() > 0) {
                        NodeList lemmas = elem.getElementsByTagName(LEMMA_TYPE);
                        Element lemma = (Element) lemmas.item(0);

                        final String name =
                                lemma.getElementsByTagName("name").item(0).getNodeValue();
                        final String expr =
                                lemma.getElementsByTagName("expr").item(0).getNodeValue();
                        adds.add(new AddItem(componentVal, new PRALemmaNode(name, expr)));
                    }

                    if (elem.getElementsByTagName(LIFT_TYPE).getLength() > 0) {
                        NodeList lifts = elem.getElementsByTagName(LIFT_TYPE);
                        Element lift = (Element) lifts.item(0);

                        final String dotID =
                                lift.getElementsByTagName("dotID").item(0).getNodeValue();
                        adds.add(new AddItem(componentVal, new PRALiftNode(dotID)));
                    }

                    if (elem.getElementsByTagName(ASSERT_TYPE).getLength() > 0) {
                        NodeList asserts = elem.getElementsByTagName(ASSERT_TYPE);
                        Element assertElem = (Element) asserts.item(0);

                        final String expr =
                                assertElem.getElementsByTagName("expr").item(0).getNodeValue();
                        adds.add(new AddItem(componentVal, new PRAAssertNode(expr)));
                    }

                    if (elem.getElementsByTagName(NODE_TYPE).getLength() > 0) {
                        NodeList nodeVals = elem.getElementsByTagName(NODE_TYPE);
                        Element nodeVal = (Element) nodeVals.item(0);

                        final String name =
                                nodeVal.getElementsByTagName("name").item(0).getNodeValue();
                        final String expr =
                                nodeVal.getElementsByTagName("expr").item(0).getNodeValue();

                        List<PRAArg> args = new ArrayList<>();

                        NodeList argNodes = nodeVal.getElementsByTagName("arg");
                        for (int j = 0; j < argNodes.getLength(); j++) {
                            Element curArg = (Element) argNodes.item(j);
                            String curArgType = curArg.getAttribute("type");
                            String argName = curArg.getNodeValue();
                            args.add(new PRAArg(argName, curArgType));
                        }

                        List<PRAArg> returns = new ArrayList<>();

                        NodeList returnNodes = nodeVal.getElementsByTagName("return");
                        for (int j = 0; j < argNodes.getLength(); j++) {
                            Element curArg = (Element) returnNodes.item(j);
                            String curArgType = curArg.getAttribute("type");
                            String argName = curArg.getNodeValue();
                            returns.add(new PRAArg(argName, curArgType));
                        }

                        adds.add(
                                new AddItem(
                                        componentVal, new PRANodeNode(name, args, returns, expr)));
                    }

                    // These options are currently unimplemented

                    if (elem.getElementsByTagName(FUNCTION_TYPE).getLength() > 0) {}

                    if (elem.getElementsByTagName(CONST_TYPE).getLength() > 0) {}

                    if (elem.getElementsByTagName(PROPERTY_TYPE).getLength() > 0) {}

                    if (elem.getElementsByTagName(EQ_TYPE).getLength() > 0) {}

                    if (elem.getElementsByTagName(GUARANTEE_TYPE).getLength() > 0) {
                        NodeList guarantees = elem.getElementsByTagName(GUARANTEE_TYPE);
                        Element guarantee = (Element) guarantees.item(0);

                        final String name =
                                guarantee.getElementsByTagName("name").item(0).getNodeValue();
                        final String expr =
                                guarantee.getElementsByTagName("expr").item(0).getNodeValue();
                        adds.add(new AddItem(componentVal, new PRALemmaNode(name, expr)));
                    }

                    if (elem.getElementsByTagName(ASSUME_TYPE).getLength() > 0) {}

                } else if (elem.getAttribute(ITEM_ACTION).equals("remove")) {

                    NodeList components = elem.getElementsByTagName("component");
                    Element component = (Element) components.item(0);
                    final String componentVal = component.getNodeValue();

                    NodeList types = elem.getElementsByTagName("type");
                    Element type = (Element) types.item(0);
                    final String typeVal = type.getNodeValue();

                    NodeList names = elem.getElementsByTagName("name");
                    Element name = (Element) names.item(0);
                    final String nameVal = name.getNodeValue();

                    removes.add(new RemoveItem(componentVal, typeVal, nameVal));

                } else {
                    System.out.println("Invalid XML File! Incorrect action listed");
                }
            }
        }

        return new PRAResultsInstance(removes, adds);
    }

    @Override
    public int hashCode() {
        return Objects.hash(removes, adds);
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof PRAResultsInstance) {
            PRAResultsInstance otherRes = (PRAResultsInstance) other;
            return removes.equals(otherRes.removes) && adds.equals(otherRes.adds);
        }
        return false;
    }
}
