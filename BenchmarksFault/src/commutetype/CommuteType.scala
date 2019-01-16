package commutetype

import org.apache.spark.rdd.RDD
import org.apache.spark.{SparkConf, SparkContext}
import utils.SparkRDDGenerator

/**
  * Created by malig on 3/27/18.
  */
object CommuteType extends SparkRDDGenerator{

  def main(args: Array[String]) {
    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("CommuteTime")


    val data1 = Array(",, ,0,1",
      ",, ,16,1",
      ",, ,41,1",
      " , , ,",
      " , , , ,0",
      " , , , ,",
      "","","",
      ",A, ,-0,1",
      ",A, ,-0,1")

    val data2 = Array(",Palms",
      ",Palms",
      ",Palms",
      "",
      "",
      "",
      "",
      ",",
      ",",
      ",",
      ",")

    val startTime = System.currentTimeMillis();
    val sc = new SparkContext(conf)
    for(i <- 0 to data1.length-1){
      try{
      val trips = sc.parallelize(Array(data1(i)))
        .map { s =>
          val cols = s.split(",")
          (cols(1), Integer.parseInt(cols(3)) / Integer.parseInt(cols(4)))
        }
      val locations = sc.parallelize(Array(data2(i)))
        .map { s =>
          val cols = s.split(",")
          (cols(0), cols(1))
        }
        .filter(s => s._2.equals("Palms"))
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
        println("Job Finished")
      }
      catch {
        case e: Exception =>
            e.printStackTrace()
      }
    }

    println("Time: " + (System.currentTimeMillis() - startTime))

  }

  override def execute(input1: RDD[String], input2: RDD[String]): RDD[String] = {
    val trips = input1
      .map { s =>
        val cols = s.split(",")
        (cols(1), Integer.parseInt(cols(3)) / Integer.parseInt(cols(4)))
      }
    val locations = input2
      .map { s =>
        val cols = s.split(",")
        (cols(0), cols(1))
      }
      .filter(s => s._2.equals("Palms"))
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
      .reduceByKey(_ + _).map(m => m._1 +","+ m._2)
  }
}

//    val trips = sc
//      .textFile(
//        "/Users/malig/workspace/up_jpf/benchmarks/src/datasets/trips/*")
//      .map { s =>
//        val cols = s.split(",")
//        (cols(1), Integer.parseInt(cols(3)) / Integer.parseInt(cols(4)))
//      }
//    val locations = sc
//      .textFile(
//        "/Users/malig/workspace/up_jpf/benchmarks/src/datasets/zipcode/*")
//      .map { s =>
//        val cols = s.split(",")
//        (cols(0), cols(1))
//      }
//      .filter(s => s._2.equals("34"))
//    val joined = trips.join(locations)
//    joined
//      .map { s =>
//        // Checking if speed is < 25mi/hr
//        if (s._2._1 > 40) {
//          ("car", 1)
//        } else if (s._2._1 > 15) {
//          ("public", 1)
//        } else {
//          ("onfoot", 1)
//        }
//      }
//      .reduceByKey(_ + _)
//      .collect
//      .foreach(println)


/* *
  *
  * map1>","
map3>","
filter2>"",""
map5>"1" , 2, "1"
reduceByKey4> {1,2,3,4}
K_BOUND>2
DAG >reduceByKey4-map5:map5-join:join-map1,filter2:filter2-map3


   val logFile = "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/bigsift/"
   val trip = logFile + "trips/*"
   val zip = logFile + "zipcode/*"

   val locations = sc.textFile(zip).sample(false, 1)
  locations.count()

  val trips = sc.textFile(trip).sample(false, 1)
   val j_trips = trips.map { s => val cols = s.split(","); (cols(1), (cols(3).toInt / cols(4).toInt))}

val j_locations = locations.map { s => val cols = s.split(","); (cols(0), cols(1))}.filter(s => s._2.equals("34"))

  val joined = j_trips.join(j_locations)
  joined.map { s => if (s._2._1 > 40) {  ("car", 1) } else if (s._2._1 > 15) { ("public", 1) } else { ("onfoot", 1) }} .reduceByKey(_ + _).count()
collect.foreach(println)


     val logFile = "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/bigsift/"
   val trip = logFile + "trips/*"
   val zip = logFile + "zipcode/*"

   val locations = sc.textFile(zip).zipWithIndex().filter(v => v._2 < 100).map(s=> s._1)
  locations.count()

  val trips = sc.textFile(trip).zipWithIndex().filter(v => v._2 < 1*320000000).map(s=> s._1)
   val j_trips = trips.map { s => val cols = s.split(","); (cols(1), (cols(3).toInt / cols(4).toInt))}

val j_locations = locations.map { s => val cols = s.split(","); (cols(0), cols(1))}.filter(s => s._2.equals("34"))

  val joined = j_trips.join(j_locations)
  joined.map { s => if (s._2._1 > 40) {  ("car", 1) } else if (s._2._1 > 15) { ("public", 1) } else { ("onfoot", 1) }} .reduceByKey(_ + _).count()


  *
  **/*/*/

  */
*/