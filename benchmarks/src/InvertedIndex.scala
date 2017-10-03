import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.SparkContext._
import scala.collection.mutable.MutableList


/**
  *
  * bug in inverted index is dependent on combination of words and doc name ==
  * Given a doc and word in it throw fault
  *
  */
object InvertedIndex {

  private val exhaustive = 0

  def main(args: Array[String]): Unit = {
    var logFile = ""
    val conf = new SparkConf().setAppName("Inverted Index")
    var local = true
    if (args.size < 2) {
      logFile = "README.md"
      conf.setMaster("local[2]")
    } else {
      logFile = args(1)
    }
    val spark = new SparkContext(conf)
    val lines = spark.textFile(logFile, 1)
    val wordDoc = lines.flatMap(s => {
      val wordDocList: MutableList[(String, String)] = MutableList()
      val colonIndex = s.lastIndexOf("^")
      val docName = s.substring(0, colonIndex).trim()
      val content = s.substring(colonIndex + 1)
      val wordList = content.trim.split(" ")
      for (w <- wordList) {
        wordDocList += Tuple2(w, docName)
      }
      wordDocList.toList
    }).map {
      p =>
        val docSet = scala.collection.mutable.Set[String]()
        docSet += p._2
        (p._1, (p._1, docSet))
    }.reduceByKey {
      (s1, s2) =>
        val s = s1._2.union(s2._2)
        (s1._1, s)
    }
    val output = wordDoc.collect

    spark.stop()

  }
}