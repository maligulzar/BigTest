package SymexScala

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

        // val props = System.getProperties()
        // println(System.getProperty("java.class.path"))

        // if(args.size < 2) {
        //     println("Please provide operator name and JPF file pathname as arguments.")
        //     exit(1)
        // }

        Runner.main(args)
        println(Runner.getDataFlowDAG)
        val dagOpList: Array[Tuple2[String, String]] = convertList(Runner.getDataFlowDAG)

        // val dagOpList: Array[Tuple2[String, String]] = new Array[Tuple2[String, String]](1)
        // dagOpList(0) = new Tuple2("map", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/Example2.jpf")
        val result2 = SymbolicEngine.executeSymbolicDF(dagOpList)
        // println(result2)


        // Logger.getLogger("org").setLevel(Level.OFF)
        // Logger.getLogger("akka").setLevel(Level.OFF)

        // val conf = new SparkConf()
        //     .setAppName("Scala Symex")
        //     .setMaster("local[4]")
        // val sc = new SparkContext(conf)
        // val srcPath = args(0)

        // val numbers = sc.textFile(srcPath)
        //             .map(line => Integer.parseInt(line))

        // val output = SymbolicEngine.run(numbers, "text")
        // println(output)
        //inputDataSet: RDD[Int], udf: Function1[Int,Int], constraint: Constraint
        // val pc1 = new PathAndEffect(numbers, new Constraint("true && x > 100"), new Function1[Int, Int] {def apply(x: Int) = x})
        // val pc2 = new PathAndEffect(numbers, new Constraint("true && x <= 100"), new Function1[Int, Int] {def apply(x: Int) = 0})
    }
}