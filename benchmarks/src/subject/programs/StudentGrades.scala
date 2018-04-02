package subject.programs

import org.apache.spark.{SparkConf, SparkContext}

/**
  * Created by malig on 3/27/18.
  */
object StudentGrades {

  def main(args: Array[String]): Unit = {
    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")
    val sc = new SparkContext(conf)
    sc.textFile("/Users/malig/workspace/up_jpf/benchmarks/src/datasets/student.csv")
      .map { s =>
        val arr = s.split(":")
        (arr(0), arr(1))
      }
      .flatMap { s =>
        s._2.split(",").map(v => (s._1, Integer.parseInt(v)))
      }
      .map { a =>
        if (a._2 > 40)
          (a._1 + " Pass", 1)
        else
          (a._1 + " Fail", 1)
      }
      .reduceByKey(_ + _)
      .filter(v => v._2 > 5)
      .collect
      .foreach(println)

  }
}
