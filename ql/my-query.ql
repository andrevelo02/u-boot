/**
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking

class NetworkByteSwap extends Expr {
  NetworkByteSwap () {
    exists(MacroInvocation minv | 
      minv.getMacro().getName() in ["ntohl", "ntohs", "ntohll"] and
      this = minv.getExpr()
    )
  }
}

module MyConfig implements DataFlow::ConfigSig {

  predicate isSource(DataFlow::Node source) {
    source.asExpr() instanceof NetworkByteSwap
  }
  
  predicate isBarrier(DataFlow::Node node) {
  exists(Variable v, BinaryOperation comp, FunctionCall memcpy_call |
    //variabile in una comparazione
    comp.getOperator() in ["<", ">", "<=", ">="] and
    node.asExpr() = v.getAnAccess() and
    comp.getAnOperand() = v.getAnAccess() and
    
    //quella variabile ha un flusso verso il memcpy
    memcpy_call.getTarget().getName() = "memcpy" and
    exists(DataFlow::Node sink_node |
      DataFlow::localFlow(node, sink_node) and
      sink_node.asExpr() = memcpy_call.getArgument(2)
    )
  )
}





  predicate isSink(DataFlow::Node sink) {
    exists(FunctionCall call | 
      call.getTarget().getName() = "memcpy" and
      sink.asExpr() = call.getArgument(2)
      )
  }
}

module MyTaint = TaintTracking::Global<MyConfig>;
import MyTaint::PathGraph

from MyTaint::PathNode source, MyTaint::PathNode sink
where MyTaint::flowPath(source, sink) 
select sink, source, sink, "Network byte swap flows to memcpy"
