package SymexScala

import org.apache.spark.{ SparkConf, SparkContext }
import org.apache.spark.rdd._

abstract class SymbolicData {
    // var inputDataSet: RDD[Int] = null
    // var pA: PathConstraint = null
    // var udf: Any = null

    def toString: String
    def getData: RDD[_]
}

case class MapSymbolicOutput(input: RDD[Int], f: Function1[Int, Int], p: MapPathConstraint) extends SymbolicData {
    val inputDataSet = input
    val udf : Function1[Int, Int] = f
    val pA = p

    override def toString: String = {
        "{"+ f.toString +"(t) | for all t member of A ^ " + p.toString + "(t) }"
    }

    def getData: RDD[Int] = {
        //RDD[Int] -> P(ta) -> apply f -> RDD[Int]
        inputDataSet.filter(p.apply(_).toBoolean).map(record => f.apply(record)) 
    }
}

case class FilterSymbolicOutput(input: RDD[Int], f: Function1[Int, Boolean], p: FilterPathConstraint) extends SymbolicData {
    val inputDataSet = input
    val udf: Function1[Int, Boolean] = f
    val pA = p

    override def toString: String = {
        "{ t | for all t member of A ^ " + f.toString +"(t) }"
    }

    def getData: RDD[Int] = {
        //RDD[Int] -> f(ta) -> RDD[Int]
        inputDataSet.filter(f.apply(_))  
    }
}

case class ReduceSymbolicOutput(input: RDD[Int], f: Function2[Int, Int, Int], p: ReducePathConstraint) extends SymbolicData {
    val inputDataSet = input
    val udf: Function2[Int, Int, Int] = f
    val pA = p 

    override def toString: String = {
        "{ lambda(f, A) | A = union of all different path constraints }"
    }

    def getData: RDD[Int] = {
        //TODO: needs sc from outside
        // val conf = new SparkConf().setAppName("temp").setMaster("local[4]")
        // val sc = new SparkContext(conf)
        // sc.parallelize(Array(input.reduce(f)))


        //or a java-like manner like this
        var acc: Int = input.first
        val all: Array[Int] = input.collect()
        for(x <- all) {
            acc = f(acc, x)
        }
        acc

    }
}



