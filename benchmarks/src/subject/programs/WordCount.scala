package subject.programs
import org.apache.spark.{SparkConf, SparkContext}

object WordCount {
  def main(args: Array[String]): Unit = {

    val conf = new SparkConf()
    .setMaster("local[*]")
    .setAppName("Wordcount")
    val sc = new SparkContext(conf)
    val lines =
      sc.textFile("/Users/malig/workspace/git/bigdebug/spark-lineage/README.md")
        .flatMap(l => l.split(" "))
        .map(w => (w, 1))
    .reduceByKey(_ + _)

  }
}
