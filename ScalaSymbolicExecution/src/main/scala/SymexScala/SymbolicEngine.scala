package SymexScala

import org.apache.spark.rdd._
import sys.process._

object SymbolicEngine {

    var afterMap: SetOfConstraints = null

    def run(data: RDD[Int], source: String): SetOfConstraints = {
        //1) parse source code to create AST
        //2) lift UDFs off the tree

        val op = "map"

        //3) run SPF on lifted udfs to get their path constraints
        // val result: String = "java -cp .:../../jpf/jpf-symbc/build/jpf-symbc-classes.jar -jar ../../jpf/jpf-core/build/RunJPF.jar spf/UDF.jpf".!!
        // println(result)
        val udfPaths = new Array[Conjunction](2)
        udfPaths(0) = Conjunction.parseConjunction("x > 100")
        udfPaths(1) = Conjunction.parseConjunction("x <= 100")
        
        // //4) call SetOfConstraints spark operation APIs according to the source code operations
        // //   to get the final set of path constraints for whole program

        val start = new SetOfConstraints() //default: "true" as path constraint
        // afterMap = start.map(udfPaths)


        // val fFilter = new Function1[Int, Boolean] {
        //     def apply(x: Int): Boolean = {x%2 == 0}
        // }

        // val afterMapFilter = afterMap.filter(fFilter)

        start

    }
}