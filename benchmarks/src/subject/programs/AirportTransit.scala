package subject.programs

import org.apache.spark.{SparkConf, SparkContext}

/**
  * Created by malig on 3/27/18.
  */
object AirportTransit {


  def main(args:Array[String]): Unit ={

    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")
    val sc = new SparkContext(conf)

    val map1 = sc.textFile("/Users/malig/workspace/up_jpf/benchmarks/src/datasets/airportdata/part-00000").map { s =>
      def getDiff(arr: String, dep: String): Int = {
        val a_min = Integer.parseInt(arr.substring(3,5))
        val a_hr = Integer.parseInt(arr.substring(0,2))
        val d_min = Integer.parseInt(dep.substring(3,5))
        val d_hr = Integer.parseInt(dep.substring(0,2))

        val arr_min = a_hr * 60 + a_min
        val dep_min = d_hr * 60 + d_min


        if(dep_min - arr_min < 0){
          return 24*60 + dep_min - arr_min
        }
        return dep_min - arr_min
      }
      val tokens = s.split(",")
      val arrival_hr = tokens(2).split(":")(0)
      val diff = getDiff(tokens(2), tokens(3))
      val airport = tokens(4)
      (airport+ arrival_hr, diff)
    }
    val fil = map1.filter { v =>
      val t1  = v._1
      val t2 = v._2
      t2 < 45
    }
    val out = fil.reduceByKey(_ + _)
    out.collect().foreach(println)
  }


}
/*
*
 sc.textFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/bigsift/airport").map { s =>
      def getDiff(arr: String, dep: String): Int = {
       val arr_min = Integer.parseInt(arr.split(":")(0)) * 60 + Integer.parseInt(arr.split(":")(1))
        val dep_min = Integer.parseInt(dep.split(":")(0)) * 60 + Integer.parseInt(dep.split(":")(1))
        if(dep_min - arr_min < 0){
          return 24*60 + dep_min - arr_min
        }
        return dep_min - arr_min
      }
      val tokens = s.split(",")
      val arrival_hr = tokens(2).split(":")(0)
      val diff = getDiff(tokens(2), tokens(3))
      val airport = tokens(4)
      (airport+ arrival_hr, diff)}.filter { v =>
      val t1  = v._1
      val t2 = v._2
      t2 < 45}.reduceByKey(_ + _).collect().foreach(println)





* */