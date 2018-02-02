           import org.apache.spark.{ SparkContext, SparkConf }
import scala.language.postfixOps //for zipWithIndex

object Test8 {

    def main(args: Array[String]): Unit = {

        val conf = new SparkConf()
                    .setAppName("Scala Toy Example 9: Simple join")
                    .setMaster("local[4]")
        val sc = new SparkContext(conf)

        val firstRDD = sc.textFile("small_data/in1")
                    .map(line => line.split(" "))
                    .map{ arr =>
                        val rand = scala.util.Random
                        (rand.nextInt(5), arr)
                    }
                    .map(pair => (pair._1, pair._2.length))

        val secondRDD = sc.textFile("small_data/in2")
                    .map(line => line.split(" "))
                    .map{ arr =>
                        val rand = scala.util.Random
                        (rand.nextInt(5), arr)
                    }
                    .map(pair => (pair._1, pair._2.length))

        val joined = firstRDD.join(secondRDD)
                    .collect()
                    
        // println("Join: "+joined.mkString("\n"))

    }
}