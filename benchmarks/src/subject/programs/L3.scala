package subject.programs

/**
  * Created by malig on 5/16/18.
  */
import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.SparkContext._

object L3 {
  def main(args: Array[String]) {
    val conf = new SparkConf()
    var saveToHdfs = false
    var path = "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/pigmix_"
    if(args.size < 1) {
      path = "../../datasets/pigMix/"  + "pigmix_10M/"
      conf.setMaster("local[2]")
    } else {
      path += args(0) + "G/"
      conf.setMaster("spark://SCAI01.CS.UCLA.EDU:7077")
      saveToHdfs = true
    }
    conf.setAppName("SparkMix-L3-" + path)

    val sc = new SparkContext(conf)

    val pageViewsPath = path + "page_views/"
    val usersPath = path + "users/"

    val pageViews = sc.textFile(pageViewsPath)
    val users = sc.textFile(usersPath)

    val A = pageViews.map(x => (x.split("\u0001")(0),x.split("\u0001")(6)))

    val B = A.map(x => (x._1, x._2.toDouble))

    val alpha = users.map(x => x.split("\u0001")(0))

    val beta = alpha.map(x => (x, 1))

    val C = B.join(beta)

    val D = C.map(x => (x._1, x._1, x._2._1)).groupBy(_._1)

    //val E = D.map(x => (x._1, x._2.reduce((a, b) => (a._1 + b._1, a._2 + b._2, a._3 + b._3)))).map(x => (x._1, x._2._3))

    if(saveToHdfs) {
      D.saveAsTextFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/output-L3-" + args(0) + "G")
    } else {
      D.collect.foreach(println)
    }

    sc.stop()
  }
  def safeDouble(string: String):Double = {
    if (string == "")
      0
    else
      string.toDouble
  }
}
