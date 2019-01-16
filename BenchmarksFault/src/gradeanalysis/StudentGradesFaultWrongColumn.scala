package gradeanalysis

import org.apache.spark.rdd.RDD
import org.apache.spark.{SparkConf, SparkContext}
import utils.SparkRDDGenerator

/**
  * Created by malig on 1/11/19.
  */
object StudentGradesFaultWrongColumn extends SparkRDDGenerator {

  def main(args: Array[String]): Unit = {
    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")

    val data1 = Array(":0\n:0",	":0\n:41",	":0\n ,:0",	":0\n ,:41",	":41\n:0"	,":41\n:41"	,":41\n ,:0",	":41\n ,:41",	" ,:0\n:0"	,
      " ,:0\n:41"	," ,:0\n ,:0",	" ,:0\n ,:41"	," ,:41\n ,:0",	" ,:41\n:41",	" ,:41\n ,:0",	" ,:41\n ,:41",	"",	" ,")

    val startTime = System.currentTimeMillis();
    val sc = new SparkContext(conf)
    for (i <- 0 to data1.length - 1) {
      try {
        val map1 = sc.parallelize(Array(data1(i))).flatMap(l => l.split("\n")).flatMap{ line =>
          val arr = line.split(",")
          arr
        }
          .map{  s =>
            val a = s.split(":")
            (a(0) , a(2).toInt)   // Injecting fault by accessing the wrong column ==> Should lead to crash
          }
          .map { a =>
            if (a._2 > 40)
              (a._1 + " Pass", 1)
            else
              (a._1 + " Fail", 1)
          }
          .reduceByKey(_ + _)
          .filter(v => v._2 > 1)
          .collect
          .foreach(println)
      }
      catch {
        case e: Exception =>
          e.printStackTrace()
      }
    }
    println("Time: " + (System.currentTimeMillis() - startTime))
  }

  override def execute(input1: RDD[String], input2: RDD[String]): RDD[String] = {
    input1.flatMap(l => l.split("\n")).flatMap{ line =>
      val arr = line.split(",")
      arr
    }
      .map{  s =>
        val a = s.split(":")
        (a(0) , a(2).toInt)   // Injecting fault by accessing the wrong column ==> Should lead to crash
      }
      .map { a =>
        if (a._2 > 40)
          (a._1 + " Pass", 1)
        else
          (a._1 + " Fail", 1)
      }
      .reduceByKey(_ + _)
      .filter(v => v._2 > 1).map(m => m._1 +","+ m._2)
  }
}
