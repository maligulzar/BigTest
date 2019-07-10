package datagen

import org.apache.spark.{SparkConf, SparkContext}

import scala.util.Random

/**
  * Created by malig on 5/14/18.
  */
object StudentGradeDataGen {

    def main(args:Array[String]) =
    {
      val sparkConf = new SparkConf()
      var logFile = ""
      var partitions = 2
      var dataper  = 50
      if(args.length < 2) {
        sparkConf.setMaster("local[6]")
        sparkConf.setAppName("TermVector_LineageDD").set("spark.executor.memory", "2g")
        logFile =  "/Users/malig/workspace/up_jpf/benchmarks/src/datasets/"
      }else{
        logFile = args(0)
        partitions =args(1).toInt
        dataper = args(2).toInt
      }
      val trips = logFile + "studentGrades"

      val sc = new SparkContext(sparkConf)
      sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
        (1 to dataper).map { _ =>

          val course= (Random.nextInt(570) + 30).toString
          val f = if(Random.nextBoolean()) "EE" else "CS"
          val students = Random.nextInt(190) + 10
          var list_std = List[Int]()
          for(i <- 0 to students){
            list_std  =  (Random.nextInt(90)+10) :: list_std
          }
          val str = list_std.map(s => f+course +":"+s).reduce(_+","+_)
          str
        }.toIterator
      }.saveAsTextFile(trips)
    }
  }

  /***
    *
    *
    *
import scala.util.Random
var partitions = 400
var dataper  = 100000
sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
        (1 to dataper).map { _ =>
          val course= (Random.nextInt(570) + 30).toString
          val f = if(Random.nextBoolean()) "EE" else "CS"
          val students = Random.nextInt(190) + 10
          var list_std = List[Int]()
          for(i <- 0 to students){
            list_std  =  (Random.nextInt(90)+10) :: list_std
          }
          val str = list_std.map(s => f+course +":"+s).reduce(_+","+_)
          str
        }.toIterator
      }.saveAsTextFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/bigsift/studentGrades")
    */
