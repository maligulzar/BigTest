package SymexScala

import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }
import org.apache.spark.rdd._

object Main {

    def main(args: Array[String]): Unit = {
        // val x = Conjunction.parseConjunction("x < 1 && y == 2 && z>y")
        import ComparisonOp._
        import ArithmeticOp._
        import NumericUnderlyingType._
        import NonNumericUnderlyingType._

        val c = new Clause(new NonTerminal(new SymVar(Numeric(_Int), "x"),
                                            new Operator(Numeric(_Int), Addition),
                                            new ConcreteValue(Numeric(_Int), "5")),
                            LessThanOrEq,
                            new ConcreteValue(Numeric(_Int), "7")
                            )
        println(c)

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
        // val pc1 = new PathConstraint(numbers, new Constraint("true && x > 100"), new Function1[Int, Int] {def apply(x: Int) = x})
        // val pc2 = new PathConstraint(numbers, new Constraint("true && x <= 100"), new Function1[Int, Int] {def apply(x: Int) = 0})
    }
}