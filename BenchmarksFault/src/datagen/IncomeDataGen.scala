package datagen

import org.apache.spark.{SparkConf, SparkContext}

import scala.util.Random

/**
  * Created by malig on 4/10/18.
  */
object IncomeDataGen {
  def main(args:Array[String]) =
  {
    val sparkConf = new SparkConf()
    var logFile = ""
    var partitions = 20
    var dataper  = 5000000
    if(args.length < 2) {
      sparkConf.setMaster("local[6]")
      sparkConf.setAppName("TermVector_LineageDD").set("spark.executor.memory", "2g")
      logFile =  "/Users/malig/workspace/up_jpf/benchmarks/src/datasets/"
    }else{
      logFile = args(0)
      partitions =args(1).toInt
      dataper = args(2).toInt
    }
    val trips = logFile + "trips"
    val zip = logFile + "zipcode"

    val sc = new SparkContext(sparkConf)
    sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
      (1 to dataper).map { _ =>

        val num = (Random.nextInt(10000) + 50).toString
        if(Random.nextBoolean()) "$"+num else num
      }.toIterator
    }.saveAsTextFile(trips)
  }
}

/***
  *
  *
  *
import scala.util.Random
var partitions = 400
    var dataper  = 10000000
sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
      (1 to dataper).map { _ =>

        val num = (Random.nextInt(10000) + 50).toString
        if(Random.nextBoolean()) "$"+num else num
      }.toIterator
    }.saveAsTextFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/bigsift/income")


  */
