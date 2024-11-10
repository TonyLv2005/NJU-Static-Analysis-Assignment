/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me

        // Attention:
        //   Mind the data structure you choose here
        //   if we use HashSet, the first block will not be the successor of Entry
        //   Better use Queue here

        Queue<Node> worklist = new LinkedList<>();
        //initialize: add all blocks except exit into worklist
        for (Node node : cfg.getNodes()){
            // We shouldn't address the Entry and Exit here
            if(!(cfg.isExit(node) || cfg.isEntry(node))){
                worklist.add(node);
            }
        }

        //start loop
        while(!worklist.isEmpty()){
            Node block = worklist.peek();
            worklist.remove();
            //Fact temp = result.getOutFact(block);
            Fact in = result.getInFact(block);
            Fact out = result.getOutFact(block);
            //meet into
            for (Node pre : cfg.getPredsOf(block)){
                analysis.meetInto(result.getOutFact(pre), in);
            }
            if(analysis.transferNode(block,in,out)){
                for(Node succ : cfg.getSuccsOf(block)){
                    // We shouldn't address Exit
                    if(!cfg.isExit(succ)){
                        worklist.add(succ);
                    }
                }
            }

            //Test outputs
            //System.out.println(block);
            //System.out.println("In :" + in);
            //System.out.println("Out: " + out);


            // The sequence of this line doesn't matter as we are removing the front in a queue.
            // The node we add later doesn't interfere with it.
        }

    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
