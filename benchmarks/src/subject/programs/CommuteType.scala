package subject.programs

import org.apache.spark.{SparkConf, SparkContext}

/**
  * Created by malig on 3/27/18.
  */
object CommuteType {

  def main(args: Array[String]) {
    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("CommuteTime")
    val sc = new SparkContext(conf)
    val trips = sc
      .textFile(
        "/Users/malig/workspace/up_jpf/benchmarks/src/datasets/trips.csv")
      .map { s =>
        val cols = s.split(",")
        (cols(1), (cols(4).toFloat / cols(3).toFloat))
      }
    val locations = sc
      .textFile(
        "/Users/malig/workspace/up_jpf/benchmarks/src/datasets/zipcode.csv")
      .map { s =>
        val cols = s.split(",")
        (cols(0), cols(1))
      }
     .filter(s => s._2.equals("Culver City"))
    val joined = trips.join(locations)
    joined
      .map { s =>
        // Checking if speed is < 25mi/hr
        if (s._2._1 > 40) {
          ("car", 1)
        } else if (s._2._1 > 15) {
          ("public", 1)
        } else {
          ("onfoot", 1)
        }
      }
      .reduceByKey(_ + _)
      .collect
      .foreach(println)

  }
}
