package SymexScala

// import org.apache.spark.{ SparkContext, SparkConf }
// import org.apache.log4j.{ Logger, Level }
// import org.apache.spark.rdd._
//import java.util.Properties

import gov.nasa.jpf.tool.RunJPF
import gov.nasa.jpf.JPF
import gov.nasa.jpf.Config
import gov.nasa.jpf.util.Pair
import gov.nasa.jpf.symbc.SymbolicListener
import gov.nasa.jpf.symbc.numeric.Expression
import gov.nasa.jpf.symbc.numeric.PathCondition
import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression
import gov.nasa.jpf.symbc.numeric.SymbolicInteger
import gov.nasa.jpf.symbc.numeric.Operator._
import gov.nasa.jpf.symbc.numeric.IntegerConstant
import gov.nasa.jpf.symbc.numeric.Comparator._


import NumericUnderlyingType._
import NonNumericUnderlyingType._

object Main {

    def main(args: Array[String]): Unit = {

        // val props = System.getProperties()
        // println(System.getProperty("java.class.path"))

        if(args.size < 1) {
            println("Please provide JPF file pathname as an argument.")
            exit(1)
        }

        val injectedListener = new PathEffectListenerImp()
        //sending args directly to jpf --> jpf will check their validity
        val config: Config = JPF.createConfig(args)
        val jpf: JPF = new JPF(config)
        val symbc: SymbolicListener = new SymbolicListener(config, jpf)
        symbc.registerPathEffectListener(injectedListener)
        jpf.addListener(symbc)
        jpf.run()

        injectedListener.convertAll("x")


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