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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.part.ViewPart;

/** Author: Daniel Larraz Date: Aug 6, 2020 */
public class MeritAssignmentView extends ViewPart {

    private Composite composite;
    public static final String ID = "com.ge.research.osate.verdict.gui.meritAssignmentView";
    // public static List<IVCNode> treeContents = new ArrayList<IVCNode>();
    public static ModelSet mustSet = new ModelSet();
    public static List<Set<ModelNode>> mInvTreeContents = new ArrayList<>();
    public static List<Set<ModelNode>> aInvTreeContents = new ArrayList<>();

    @Override
    public void setFocus() {
        if (composite != null) {
            composite.setFocus();
        }
    }

    @Override
    public void createPartControl(Composite parent) {

        composite = new Composite(parent, SWT.NONE);

        composite.setSize(1130, 600);
        composite.setLayout(new FillLayout());

        Tree tree = new Tree(composite, SWT.BORDER);

        Set<ModelNode> mustSetNodes = mustSet.getNodes();
        if (!mustSetNodes.isEmpty()) {
            TreeItem topLevelNodeItem = new TreeItem(tree, 0);
            processNodes(topLevelNodeItem, "MUST set", mustSetNodes);
        }

        if (!mInvTreeContents.isEmpty()) {
            for (int i = 0; i < mInvTreeContents.size(); ++i) {
                TreeItem topLevelNodeItem = new TreeItem(tree, 0);

                Set<ModelNode> mIvcs = mInvTreeContents.get(i);
                processNodes(
                        topLevelNodeItem, "Minimal Inductive Validity Core #" + (i + 1), mIvcs);
            }
        }

        if (!aInvTreeContents.isEmpty()) {
            for (int i = 0; i < aInvTreeContents.size(); ++i) {
                TreeItem topLevelNodeItem = new TreeItem(tree, 0);

                Set<ModelNode> aIvcs = aInvTreeContents.get(i);
                processNodes(topLevelNodeItem, "Inductive Validity Core #" + (i + 1), aIvcs);
            }
        }

        tree.pack();
        composite.pack();
    }

    private void processNodes(TreeItem topLevel, String title, Set<ModelNode> nodes) {
        topLevel.setText(title);
        Map<Boolean, List<ModelNode>> partitioned =
                nodes.stream().collect(Collectors.partitioningBy(ModelNode::hasAssumption));
        fillTree(topLevel, partitioned.get(true));
        fillTree(topLevel, partitioned.get(false));
    }

    private void fillTree(TreeItem topLevel, List<ModelNode> nodes) {
        for (ModelNode node : nodes) {
            TreeItem nodeItem = new TreeItem(topLevel, 0);
            nodeItem.setText("Component '" + node.getNodeName() + "'");
            for (ModelElement e : node.getNodeElements()) {
                TreeItem eItem = new TreeItem(nodeItem, 0);
                eItem.setText(e.getCategory().toString() + " '" + e.getName() + "'");
            }
        }
    }
}
