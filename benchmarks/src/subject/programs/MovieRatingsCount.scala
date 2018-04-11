package subject.programs

import org.apache.spark.{SparkConf, SparkContext}

/**
  * Created by malig on 4/10/18.
  */
object MovieRatingsCount {

  def main(args: Array[String]): Unit = {

    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")
    val sc = new SparkContext(conf)
    val averageRating = sc
      .textFile("/Users/malig/workspace/up_jpf/benchmarks/src/datasets/movie/*")
      .map { line =>
        val arr = line.split(":")
        val movie_str = arr(0)
        val ratings = arr(1).split(",")(0).split("_")(1)
        (movie_str, ratings.substring(0,1))
      }
      .map{c =>
        val str = c._1
        (str, Integer.parseInt(c._2))}
      .filter{b =>
        val t1  = b._1
        val t2 = b._2
        t2 > 4}.reduceByKey(_+_)
  }
}

/**
  *
  *

sc.textFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/bigsift/kmeans/*").map { line =>
        val arr = line.split(":")
        val movie_str = arr(0)
        val ratings = arr(1).split(",")(0).split("_")(1)
        (movie_str, ratings.substring(0,1))
      }.map{c =>
        val str = c._1
        (str, Integer.parseInt(c._2))}.filter{b =>
        val t1  = b._1
        val t2 = b._2
        t2 > 4}.reduceByKey(_+_).collect.foreach(println)


  */
