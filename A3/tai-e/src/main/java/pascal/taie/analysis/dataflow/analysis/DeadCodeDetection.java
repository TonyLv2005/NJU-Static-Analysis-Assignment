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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.lang.annotation.Target;
import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    private Map<Stmt, Integer> node_sign = new HashMap<>();
    //sign 0: not accessed
    //sign 1: accessed but yet totally processed
    //sign 2: accessed and already processed

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        //initialize sign for each node in cfg
        for(Stmt stmt : cfg){
            node_sign.put(stmt,0);
        }

        /*
        *  Attention: must modify "deadCode" when traversing cfg
        *  but not keep a global variable to store the deadCode we discovered
        *  Which means, we must pass deadCode as argument to dfs_cfg
        * */

        //dfs start from the entry
        dfs_cfg(cfg.getEntry(),cfg,constants,liveVars,deadCode);

        //add control-flow unreachable nodes
        for(Stmt stmt : cfg){
            if(!cfg.isExit(stmt)  && node_sign.get(stmt) == 0){
                deadCode.add(stmt);
            }
        }

        // Entry and Exit isn't a part of IR, thus we shouldn't include them in deadCode
        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());


        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }

    private void dfs_cfg(Stmt stmt,CFG<Stmt> cfg,DataflowResult<Stmt, CPFact> constants,DataflowResult<Stmt, SetFact<Var>> liveVars
    ,Set<Stmt> deadCode){
      if(node_sign.get(stmt) == 1){ //already or being processed
          return;
      }

      //set sign
      node_sign.put(stmt,1);

      CPFact cp_infact = constants.getInFact(stmt);
      SetFact<Var> lv_outfact= liveVars.getOutFact(stmt);
      //process
        // Unreachable branch
      if(stmt instanceof If ifStmt){
          ConditionExp cc_exp = ifStmt.getCondition();
          Value cc_val = ConstantPropagation.evaluate(cc_exp,cp_infact);

          if(cc_val.isConstant()){
              int result = cc_val.getConstant();
              for(Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)){
                  if(result == 1 && edge.getKind() == Edge.Kind.IF_TRUE){
                      dfs_cfg(edge.getTarget(),cfg,constants,liveVars,deadCode);
                      break;
                  }
                  if (result == 0 && edge.getKind() == Edge.Kind.IF_FALSE) {
                      dfs_cfg(edge.getTarget(),cfg,constants,liveVars,deadCode);
                      break;
                  }
              }
          }else{
              dfs_successors(stmt,cfg,constants,liveVars,deadCode);
          }
      }
      else if (stmt instanceof SwitchStmt sw_stmt) {
          Var cc = sw_stmt.getVar();
          Value cc_value = ConstantPropagation.evaluate(cc,cp_infact);
          if(cc_value.isConstant()){
              int value = cc_value.getConstant();
              boolean has = false;
              List<Pair<Integer, Stmt>> CaseTargets = sw_stmt.getCaseTargets();
              for(Pair<Integer,Stmt> CaseTarget : CaseTargets){
                  int c = CaseTarget.first();
                  Stmt target = CaseTarget.second();

                  if(value == c){
                      has = true;
                      dfs_cfg(target,cfg,constants,liveVars,deadCode);
                  }
              }

              //default switch case
              if(!has){
                  dfs_cfg(sw_stmt.getDefaultTarget(),cfg,constants,liveVars,deadCode);
              }
          }
          else{
              dfs_successors(stmt,cfg,constants,liveVars,deadCode);
          }

      }
      // Useless Assignment
      else if (stmt instanceof Invoke inv_stmt) {
          /*"本次作业中所有可能的无用赋值都只可能是 AssignStmt 的实例。
                你只需要关注 AssignStmt 这个类即可。"
          *
          *     Procession to Invoke might be unnecessary

           */

          /*
          LValue l_val = inv_stmt.getLValue();
          RValue r_val = inv_stmt.getRValue();
          if(l_val instanceof Var && hasNoSideEffect(r_val)){
              if(!lv_outfact.contains((Var) l_val)){
                deadCode.add(stmt);
              }
          }*/


          // if invoke just let it pass
          dfs_successors(stmt,cfg,constants,liveVars,deadCode);

      }
      else if (stmt instanceof AssignStmt<?,?> as_stmt) {
          LValue l_val = as_stmt.getLValue();
          RValue r_val = as_stmt.getRValue();
          if(l_val instanceof Var ){
              if(!lv_outfact.contains((Var) l_val) && hasNoSideEffect(r_val)){
                  deadCode.add(stmt);
              }
          }

          dfs_successors(stmt,cfg,constants,liveVars,deadCode);
      }
      else{ //drop it and visit successors
          dfs_successors(stmt,cfg,constants,liveVars,deadCode);
      }


    }

    private void dfs_successors(Stmt stmt,CFG<Stmt> cfg,DataflowResult<Stmt, CPFact> constants,DataflowResult<Stmt, SetFact<Var>> liveVars
            ,Set<Stmt> deadCode){
        for(Stmt succ : cfg.getSuccsOf(stmt)){
            dfs_cfg(succ,cfg,constants,liveVars,deadCode);
        }
    }
}


