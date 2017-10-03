import org.apache.spark.{SparkConf, SparkContext}

object SparkGrep {

  def main(args: Array[String]): Unit = {
    var logFile = ""
    val conf = new SparkConf().setAppName("Spark Pi")
    var local = true
    if (args.size < 2) {
      logFile = "README.md"
      conf.setMaster("local[2]")
    } else {
      logFile = args(1)
    }
    val sc = new SparkContext(conf)
    // Job
    val lines = sc.textFile(logFile, 2)
    val result = lines.filter(line => line.contains("congress"))
    result.count
  }
}