package SymexScala

// import org.apache.spark.{ SparkContext, SparkConf }
// import org.apache.log4j.{ Logger, Level }
// import org.apache.spark.rdd._
//import java.util.Properties

// import gov.nasa.jpf.util.Pair
import gov.nasa.jpf.JPF
import gov.nasa.jpf.Config
import gov.nasa.jpf.symbc.SymbolicListener
// import gov.nasa.jpf.symbc.numeric.Expression
// import gov.nasa.jpf.symbc.numeric.PathCondition
// import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression
// import gov.nasa.jpf.symbc.numeric.SymbolicInteger
// import gov.nasa.jpf.symbc.numeric.Operator._
// import gov.nasa.jpf.symbc.numeric.IntegerConstant
// import gov.nasa.jpf.symbc.numeric.Comparator._


import NumericUnderlyingType._
import NonNumericUnderlyingType._

object Main {

    def main(args: Array[String]): Unit = {

        // val props = System.getProperties()
        // println(System.getProperty("java.class.path"))

        if(args.size < 2) {
            println("Please provide operator name and JPF file pathname as arguments.")
            exit(1)
        }

        //TODO: assuming that we are numbering df operators with only 1 digit!
        // val truncated = args(0).substring(0, args(0).size-1)
        // //println(truncated+" "+args(1))
        // val result = SymbolicEngine.executeDFOperator(truncated, args(1))
        // println(result)

        val inputArgs = new Array[Tuple2[String, String]](2)
        inputArgs(0) = ("map", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/map2.jpf")
        inputArgs(1) = ("filter", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/filter1.jpf")
        val result2 = SymbolicEngine.executeSymbolicDF(inputArgs)
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