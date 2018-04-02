package evaluation.programs

import org.apache.spark.{SparkConf, SparkContext}

/**
  * Created by malig on 3/27/18.
  */
object L2 {
  def main(args: Array[String]) {
    val conf = new SparkConf()
    var saveToHdfs = false
    var path =
      "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/pigmix_"
    conf.setAppName("SparkMix-L2-" + path)

    val sc = new SparkContext(conf)

    val pageViewsPath = path + "page_views/"
    val powerUsersPath = path + "power_users/"

    val pageViews = sc.textFile(pageViewsPath)
    val powerUsers = sc.textFile(powerUsersPath)
    val A = pageViews.map { x =>
      val a = x.split(" ")
      (a(0),a(1) , a(7) , a(8))
    }

    val A1 = A.map{s =>

      if(s._2 == "1"){
        (s._1 ,  s._3)
        }
      else{
        (s._1 ,  s._4)
        }
    }
    val B = A.map(x => (x._1, x._2))

    val alpha = powerUsers.map { x =>
      val a = x.split(" ")
      a(0)
    }

    val beta = alpha.map(x => (x, 1))

    val C = B.join(beta).map(x => (x._1, x._2._1, x._1))

      C.collect.foreach(println)
  }
}
