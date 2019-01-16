package airporttransit

import org.apache.spark.rdd.RDD
import org.apache.spark.{SparkConf, SparkContext}
import utils.SparkRDDGenerator

/**
  * Created by malig on 1/11/19.
  */

object AirportTransitFaultSwapKV extends SparkRDDGenerator {

  def main(args: Array[String]): Unit = {

    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")
    val data1 = Array(" , ,90A0,-0A0,",
      " , ,-0A0,-0A0,",
      "",
      " , , ,",
      "",
      " , ,",
      " , ,",
      " , , ,",
      " , ,",
      " , , ,",
      " , ,",
      " , , ,",
      " , ,-0A9,-0A0,",
      " , ,-0A0,00A0,")

    val startTime = System.currentTimeMillis();
    val sc = new SparkContext(conf)
    for (i <- 0 to data1.length - 1) {
      try {

        val map1 = sc.parallelize(Array(data1(i))).map { s =>
          def getDiff(arr: String, dep: String): Int = {
            val a_min = Integer.parseInt(arr.substring(3, 5))
            val a_hr = Integer.parseInt(arr.substring(0, 2))
            val d_min = Integer.parseInt(dep.substring(3, 5))
            val d_hr = Integer.parseInt(dep.substring(0, 2))

            val arr_min = a_hr * 60 + a_min
            val dep_min = d_hr * 60 + d_min


            if (dep_min - arr_min < 0) {
              return 24 * 60 + dep_min - arr_min
            }
            return dep_min - arr_min
          }

          val tokens = s.split(",")
          val arrival_hr = tokens(2).split(":")(0)
          val diff = getDiff(tokens(3), tokens(2))  // Injecting fault by swapping the KV pair. ==> Should get wrong output.
          val airport = tokens(4)
          (airport + arrival_hr, diff)
        }
        val fil = map1.filter { v =>
          val t1 = v._1
          val t2 = v._2
          t2 < 45
        }
        val out = fil.reduceByKey(_ + _)
        out.collect().foreach(println)
      }
      catch {
        case e: Exception =>
          e.printStackTrace()
      }
    }

    println("Time: " + (System.currentTimeMillis() - startTime))
  }
  override def execute(input1: RDD[String], input2: RDD[String]): RDD[String] = {
    input1.map { s =>
      def getDiff(arr: String, dep: String): Int = {
        val a_min = Integer.parseInt(arr.substring(3, 4))
        val a_hr = Integer.parseInt(arr.substring(0, 2))
        val d_min = Integer.parseInt(dep.substring(3, 4))
        val d_hr = Integer.parseInt(dep.substring(0, 2))

        val arr_min = a_hr * 60 + a_min
        val dep_min = d_hr * 60 + d_min


        if (dep_min - arr_min < 0) {
          return 24 * 60 + dep_min - arr_min
        }
        return dep_min - arr_min
      }

      val tokens = s.split(",")
      val arrival_hr = tokens(2).split(":")(0)
      val diff = getDiff(tokens(3), tokens(2))  // Injecting fault by swapping the KV pair. ==> Should get wrong output.
      val airport = tokens(4)
      (airport + arrival_hr, diff)
    }.filter { v =>
      val t1 = v._1
      val t2 = v._2
      t2 < 45
    }.reduceByKey(_ + _).map(m=> m._1 +","+m._2)
  }

}
