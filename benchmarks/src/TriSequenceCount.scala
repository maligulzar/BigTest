
import java.util.StringTokenizer
import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.SparkContext._
import scala.collection.mutable.MutableList


object TriSequenceCount {

  private val exhaustive = 0

  def main(args: Array[String]): Unit = {
    var logFile = ""
    val conf = new SparkConf().setAppName("TriSequenceCount")
    var local = true
    if (args.size < 2) {
      logFile = "README.md"
      conf.setMaster("local[2]")
    } else {
      logFile = args(1)
    }
    val spark = new SparkContext(conf)

    val lines = spark.textFile(logFile, 5)
    val sequence = lines.flatMap(s => {

      var wordStringP1 = new String("")
      var wordStringP2 = new String("")
      var wordStringP3 = new String("")

      val sequenceList: MutableList[(String, Int)] = MutableList()
      // val colonIndex = s.lastIndexOf(':')
      //val docName = s.substring(0, colonIndex)
      val contents = s
      val itr = new StringTokenizer(contents)
      while (itr.hasMoreTokens) {
        wordStringP1 = wordStringP2
        wordStringP2 = wordStringP3
        wordStringP3 = itr.nextToken
        if (wordStringP1.equals("")) {
          //Do nothing if not all three have values
        }
        else {
          val finalString = wordStringP1 + "|" + wordStringP2 + "|" + wordStringP3 //+ "|" + docName
          sequenceList += Tuple2(finalString, 1)
        }
      }
      sequenceList.toList
    }).reduceByKey(_ + _)
    val out = sequence.collect()
    ctx.stop()
  }
}
