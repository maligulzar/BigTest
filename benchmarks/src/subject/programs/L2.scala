package subject.programs

/**
  * Created by malig on 5/15/18.
  */
import org.apache.spark.SparkContext._
import org.apache.spark.{SparkConf, SparkContext}

object L2 {
  def main(args: Array[String]) {
    val conf = new SparkConf()
    var saveToHdfs = false
    var path = "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/pigmix_"
    if (args.size < 1) {
      path = "../../datasets/pigMix/" + "pigmix_10M/"
      conf.setMaster("local[2]")
    } else {
      path += args(0) + "G"
      conf.setMaster("spark://SCAI01.CS.UCLA.EDU:7077")
      saveToHdfs = true
    }
    conf.setAppName("SparkMix-L2-" + path)

    val sc = new SparkContext(conf)

    val pageViewsPath = path + "page_views/"
    val powerUsersPath = path + "power_users/"

    val pageViews = sc.textFile(pageViewsPath)
    val powerUsers = sc.textFile(powerUsersPath)

    val A = pageViews.map(x => (x.split("\u0001")(0) , x.split("\u0001")(6) ))

    val B = A.map(x => (x._1, x._2))

    val alpha = powerUsers.map(x => x.split("\u0001")(0))

    val beta = alpha.map(x => (x, 1))

    val C = B.join(beta).map(x => (x._1, x._2._1, x._1))

    if (saveToHdfs) {
      C.saveAsTextFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/output-L2-" + args(0) + "G")
    } else {
      C.collect.foreach(println)
    }

  }

  def safeSplit(string: String, delim: String, int: Int):String = {
    val split = string.split(delim)
    if (split.size > int)
      split(int)
    else
      ""
  }

  def createMap(mapString:String):Map[String, String] = {
    val map = mapString.split("\u0003").map(x => (x.split("\u0004")(0),x.split("\u0004")(1))).toMap
    map
  }

  def createBag(bagString:String):Array[Map[String, String]] = {
    val bag = bagString.split("\u0002").map(x => createMap(x))
    bag
  }
}