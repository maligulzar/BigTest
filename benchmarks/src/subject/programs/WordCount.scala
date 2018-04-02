package subject.programs
import org.apache.spark.{SparkConf, SparkContext}

object WordCount {
  def main(args: Array[String]): Unit = {

    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Wordcount")
    val sc = new SparkContext(conf)
    val lines =
      sc.textFile("/Users/malig/workspace/git/bigdebug/spark-lineage/README.md")
    val words = lines.flatMap(l => l.split(" "))
    val pairs = words.map(w => (w, 1))
    val count = pairs.reduceByKey(_ + _)
    count.collect().foreach(println)
  }
}
