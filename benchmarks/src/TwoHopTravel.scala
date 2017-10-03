import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.SparkContext._

/**
  * The dataset of this program is available on GoogleDrive
  * https://drive.google.com/open?id=0ByF054fDjBClMzVyT1pXc2czM1E
  */

object TwoHopTravel {
  def main(args: Array[String]): Unit = {
      //set up spark configuration
      val sparkConf = new SparkConf().setMaster("local[6]")
      sparkConf.setAppName("Destination")
        .set("spark.executor.memory", "2g")

      //set up lineage
      var lineage = true
      var logFile = "hdfs://scai01.cs.ucla.edu:9000/clash/data/"
      if (args.size < 2) {
        logFile = "test_log"
        lineage = true
      } else {
        lineage = args(0).toBoolean
        logFile += args(1)
        sparkConf.setMaster("spark://SCAI01.CS.UCLA.EDU:7077")
      }
      val ctx = new SparkContext(sparkConf)

      val lines = ctx.textFile("/Users/inter/datasets/xaa", 10)
      val destination_key = lines.map(s => {
        val list = s.split(",")
        (list(3), (list(2), list(5).toInt))
      })
    val departure_key = lines.map(s => {
        val list = s.split(",")
        (list(2), (list(3), list(5).toInt))
      })

      val double_hop = destination_key
        .join(departure_key)
        .filter(pair => pair._2._2._1.substring(1, pair._2._2._1.length - 1).equals("PHL"))
        .map(pair => ((pair._2._1._1, pair._2._2._1), pair._2._1._2 * pair._2._2._2))
      val out = double_hop.collect()
  }
}