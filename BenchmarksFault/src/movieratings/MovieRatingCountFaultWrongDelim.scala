package movieratings

import org.apache.spark.rdd.RDD
import org.apache.spark.{SparkConf, SparkContext}
import utils.SparkRDDGenerator

/**
  * Created by malig on 1/11/19.
  */
object MovieRatingCountFaultWrongDelim extends SparkRDDGenerator{

  def main(args: Array[String]): Unit = {

    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")
    val data1 = Array(" : _5",
      "",
      " :",
      ": _",
      ": _0")

    val startTime = System.currentTimeMillis();
    val sc = new SparkContext(conf)
    for (i <- 0 to data1.length - 1) {
      try {
        val averageRating = sc
          .parallelize(Array(data1(i)))
          .map { line =>
            val arr = line.split(":")
            val movie_str = arr(0)
            val ratings = arr(1).split("_")(0).split("_")(1) // Injecting fault by using a wrong delimiter ==> should lead to crash
            (movie_str, ratings.substring(0, 1))
          }
          .map { c =>
            val str = c._1
            (str, Integer.parseInt(c._2))
          }
          .filter { b =>
            val t1 = b._1
            val t2 = b._2
            t2 > 4
          }.reduceByKey(_ + _).collect().foreach(println)
      }
      catch {
        case e: Exception =>
          e.printStackTrace()
      }
    }
    println("Time: " + (System.currentTimeMillis() - startTime))
  }

  override def execute(input1: RDD[String], input2: RDD[String]): RDD[String] = {
    input1.map { line =>
      val arr = line.split(":")
      val movie_str = arr(0)
      val ratings = arr(1).split("_")(0).split("_")(1) // Injecting fault by using a wrong delimiter ==> should lead to crash
      (movie_str, ratings.substring(0, 1))
    }
      .map { c =>
        val str = c._1
        (str, Integer.parseInt(c._2))
      }
      .filter { b =>
        val t1 = b._1
        val t2 = b._2
        t2 > 4
      }.reduceByKey(_ + _).map(m=>m._1 +","+m._2)
  }

}
