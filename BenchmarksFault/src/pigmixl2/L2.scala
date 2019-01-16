package pigmixl2

import org.apache.spark.rdd.RDD
import org.apache.spark.{SparkConf, SparkContext}
import utils.SparkRDDGenerator

/**
  * Created by malig on 5/15/18.
  */

object L2 extends SparkRDDGenerator {
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
      Array("", "", "", "", "")

    val startTime = System.currentTimeMillis();
    val sc = new SparkContext(conf)
    for (i <- 0 to data1.length - 1) {
      try {
        val pageViews = sc.parallelize(Array(data1(i)))
        val powerUsers = sc.parallelize(Array(data2(i)))
        val A = pageViews.map(x => (x.split(",")(0), x.split(",")(6)))
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
    val A = pageViews.map(x => (x.split(",")(0), x.split(",")(6)))
    val alpha = powerUsers.map(x => x.split(",")(0))
    val beta = alpha.map(x => (x, 1))
  A.join(beta).map(x => x._1 + "," + x._2._1)
  }
}
/**
val logFile = "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/bigsift/"
    val page = logFile + "page_views"
    val users = logFile + "power_users"


val pageViews = sc.textFile(page)
        val powerUsers = sc.textFile(users)
        val A = pageViews.map(x => (x.split(",")(0), x.split(",")(6)))
        val alpha = powerUsers.map(x => x.split(",")(0))
        val beta = alpha.map(x => (x, 1))
        val C = A.join(beta).map(x => (x._1, x._2._1, x._1))
        C.count()

A.sample(false,0.001).map(s=> s._1).distinct().count - alpha.sample(false,0.001).count

  map1>","
map3>","
map2> ""
map4>"1",1, "1"
K_BOUND>2
DAG >map4-join:join-map1,map3:map2-map1


   */

/*
*     val sum = sc
      .textFile("input")
      val sum1 = sc
      .textFile("input1")

    val A = sum.map(line1 => (line1.split("\u0001")(0) , line1.split("\u0001")(6)))

    val alpha = sum1.map(line2 => line2.split("\u0001")(0))

    val beta = alpha.map(p => (p, 1))

    val C = A.join(beta).map{v =>
     // val v1 = v._1
    //  val v2 = v._2._1
     /// val v3 = v._2._2
      (v._1, v._2._1)
      }
* */