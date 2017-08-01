package SymexScala

import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }
import org.apache.spark.rdd._

object Main {

    def main(args: Array[String]): Unit = {
        val x = new Constraint("x < 1 && y == 2 && z>y")
        println(x)

        Logger.getLogger("org").setLevel(Level.OFF)
        Logger.getLogger("akka").setLevel(Level.OFF)

        val conf = new SparkConf()
        conf.setAppName("Scala Symex")
        conf.setMaster("local[4]")
        val sc = new SparkContext(conf)
        val srcPath = args(0)

        val numbers = sc.textFile(srcPath)
                    .map(line => Integer.parseInt(line))

        //inputDataSet: RDD[Int], udf: Function1[Int,Int], constraint: Constraint
        // val pc1 = new PathConstraint(numbers, new Constraint("true && x > 100"), new Function1[Int, Int] {def apply(x: Int) = x})
        // val pc2 = new PathConstraint(numbers, new Constraint("true && x <= 100"), new Function1[Int, Int] {def apply(x: Int) = 0})
    }
}