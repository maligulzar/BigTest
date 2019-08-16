package wordcount

import org.apache.spark.rdd.RDD
import org.apache.spark.{SparkConf, SparkContext}
import utils.SparkRDDGenerator

object WordCountMutateOperatorAdd extends SparkRDDGenerator {
  def main(args: Array[String]): Unit = {

    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")
    val data1 = Array("\n",  "\n ,", " ,\n" , " ,\n ,")

    val startTime = System.currentTimeMillis();
    val sc = new SparkContext(conf)
    for (i <- 0 to data1.length - 1) {
      try {

        val map1 = sc.parallelize(Array(data1(i))).flatMap(line => line.split("\n")).flatMap(l => l.split(" "))
        .map(w => (w, 1))
    .reduceByKey(_ - _) // Fault injected by mutating the operator + to - ==> should produce wrong output
      }
      catch {
        case e: Exception =>
          e.printStackTrace()
      }
    }
    println("Time: " + (System.currentTimeMillis() - startTime))
  }
  override def execute(input1: RDD[String], input2: RDD[String]): RDD[String] = {
    input1.flatMap(line => line.split("\n")).flatMap(l => l.split(","))
      .map(w => (w, 1))
      .reduceByKey(_ - _) // Fault injected by mutating the operator + to - ==> should produce wrong output
      .map(m => m._1 + "," + m._2)
  }


}
/*
* reduceByKey1 > {1,2,3,4}
map2 > ""
flatMap3 >""
DAG >reduceByKey1-map2:map2-flatMap3
* */