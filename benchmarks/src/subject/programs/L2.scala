package subject.programs

/**
  * Created by malig on 5/15/18.
  */

import org.apache.spark.SparkContext._

import org.apache.spark.{SparkConf, SparkContext}

object L2 {
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
        val A = pageViews.map(x => (x.split(",")(0), x.split(",")(6)))
        val alpha = powerUsers.map(x => x.split(",")(0))
        val beta = alpha.map(x => (x, 1))
        val C = A.join(beta).map(x => (x._1, x._2._1, x._1))
        C.collect.foreach(println)
      } catch {
        case e: Exception =>
          e.printStackTrace()
      }
    }
    println("Time: " + (System.currentTimeMillis() - startTime))
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