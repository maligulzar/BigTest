package pigmixl2

import org.apache.spark.rdd.RDD
import org.apache.spark.{SparkConf, SparkContext}
import utils.SparkRDDGenerator

/**
  * Created by malig on 1/11/19.
  */
object L2FaultWrongColumn extends SparkRDDGenerator{

  def main(args: Array[String]) {
    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("CommuteTime")

    val data1 = Array(", , , , , , ",
      "",
      "",
      "A, , , , , , ",
      "A, , , , , , "
    )
    val data2 =
      Array("","","","","")

    val startTime = System.currentTimeMillis();
    val sc = new SparkContext(conf)
    for (i <- 0 to data1.length - 1) {
      try {
        val pageViews = sc.parallelize(Array(data1(i)))
        val powerUsers = sc.parallelize(Array(data2(i)))
        val A = pageViews.map(x => (x.split(",")(0), x.split(",")(8))) // injecting fault by accessing the wrong column ==> Should lead to crash
        val alpha = powerUsers.map(x => x.split(",")(0))
        val beta = alpha.map(x => (x, 1))
        val C = A.join(beta).map(x => (x._1, x._2._1))
        C.collect.foreach(println)
      } catch {
        case e: Exception =>
          e.printStackTrace()
      }
    }
    println("Time: " + (System.currentTimeMillis() - startTime))
  }

  override def execute(input1: RDD[String], input2: RDD[String]): RDD[String] = {
    val pageViews = input1
    val powerUsers = input2
    val A = pageViews.map(x => (x.split(",")(0), x.split(",")(8))) // injecting fault by accessing the wrong column ==> Should lead to crash
    val alpha = powerUsers.map(x => x.split(",")(0))
    val beta = alpha.map(x => (x, 1))
    A.join(beta).map(x => x._1 + "," + x._2._1)
  }

}
