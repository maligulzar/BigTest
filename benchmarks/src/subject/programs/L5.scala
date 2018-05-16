package subject.programs
import org.apache.spark.SparkContext._
import org.apache.spark.{SparkConf, SparkContext}

object L5 {
  def main(args: Array[String]) {
    val conf = new SparkConf()
    var saveToHdfs = false
    var path = "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/pigmix_"
    if(args.size < 1) {
      path = "../../datasets/pigMix/"  + "pigmix_10M/"
      conf.setMaster("local[2]")
    } else {
      path += args(0) + "G"
      conf.setMaster("spark://SCAI01.CS.UCLA.EDU:7077")
      saveToHdfs = true
    }
    conf.setAppName("SparkMix-L5-" + path)

    val sc = new SparkContext(conf)

    val pageViewsPath = path + "page_views/"
    val usersPath = path + "users/"

    val pageViews = sc.textFile(pageViewsPath)
    val users = sc.textFile(usersPath)

    val A = pageViews.map(x => x.split("\u0001")(0))

    val B = A.map(x => (x, x))

    val alpha = users.map(x => x.split("\u0001")(0))

    val beta = alpha.map(x => (x, x))

    val C = B.join(beta).map(x => (x._1, 1)).reduceByKey(_+_)


    val D = C.filter(x => x._2 > 1)


    if(saveToHdfs) {
      D .saveAsTextFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/output-L5-" + args(0) + "G")
    } else {
      D .collect.foreach(println)
    }

    sc.stop()
  }
}