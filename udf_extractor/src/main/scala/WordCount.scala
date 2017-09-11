import org.apache.spark.{SparkConf, SparkContext}

object WordCount {
  def main(args: Array[String]): Unit = {
    val sparkContext = new SparkContext(new SparkConf().setMaster("local[1]").setAppName("ok"))
    sparkContext.setCodeAnalyzer(new ClosureCleaner())
    sparkContext.textFile("/Users/malig/workspace/spark2.2.0/spark-2.2.0/README.md").filter { s =>
      true
    }.flatMap(s => s.split(" "))
      .map { p =>
        (p, 1)
      }
      .reduceByKey((s1, s2) => s1 + s2)
      .map(s => s)
  }
}