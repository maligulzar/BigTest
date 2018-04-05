package symexScala

import gov.nasa.jpf.JPF
import gov.nasa.jpf.Config
import gov.nasa.jpf.symbc.SymbolicListener

import udfExtractor.Runner
import udfExtractor.JPFDAGNode
import java.util.ArrayList

import NumericUnderlyingType._
import NonNumericUnderlyingType._

object Main {

    def convertList(dag: ArrayList[JPFDAGNode]): Array[Tuple2[String, String]] = {
        //println("removing first map function: assuming its a textFile op -------------------------")
        val result: Array[Tuple2[String, String]] = new Array[Tuple2[String, String]](dag.size-1)
        var i = 0
        for(i <- 1 to dag.size-1) {
            val node = dag.get(i)

            //TODO: assuming that we are numbering df operators with only 1 digit!
            val op = node.getOperatorName.substring(0, node.getOperatorName.size-1)
            result(i-1) = (op, node.getJPFFileName)
        }
        result
    }

    def main(args: Array[String]): Unit = {

        // if(args.size < 2) {
        //     println("Please provide operator name and JPF file pathname as arguments.")
        //     exit(1)
        // }

        // Runner.main(args)
        // println(Runner.getDataFlowDAG)
           // convertList(Runner.getDataFlowDAG)
        val dagOpList: Array[Tuple2[String, String]] = new Array[Tuple2[String, String]](4)
        dagOpList(1) = ("map", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/map3.jpf")
        dagOpList(2) = ("filter", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/filter2.jpf")
        dagOpList(3) = ("map", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/map3.jpf")
        // dagOpList(3) = ("reduce", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/reduce1.jpf")

        val result = SymbolicEngine.executeSymbolicDF(dagOpList)
        // println(result)
    }


}