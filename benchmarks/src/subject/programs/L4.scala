package subject.programs

/**
  * Created by malig on 5/16/18.
  */

import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.SparkContext._


object L4 {
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
    conf.setAppName("SparkMix-L4-" + path)

    val sc = new SparkContext(conf)

    val pageViewsPath = path + "page_views/"

    val pageViews = sc.textFile(pageViewsPath)

    val A = pageViews.map(x => (x.split("\u0001")(0), x.split("\u0001")(1)))
    val B = A.map(x => (x._1 , 1))
    val C = B.reduceByKey(_+_)

    if(saveToHdfs) {
      C.saveAsTextFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/output-L4-" + args(0) + "G")
    } else {
      C.collect.foreach(println)
    }

    sc.stop()

  }
}
