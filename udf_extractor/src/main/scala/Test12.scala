import org.apache.spark.{ SparkContext, SparkConf }
import scala.language.postfixOps //for zipWithIndex

object Test12 {

    def main(args: Array[String]): Unit = {

        val conf = new SparkConf()
                    .setAppName("Scala Toy Example 9: Join with a path in one of RDDs")
                    .setMaster("local[4]")
        val sc = new SparkContext(conf)

        val firstRDD = sc.textFile("small_data/tuple1")
                    .map(line => {
                        val parts = line.split(" ")
                        (Integer.parseInt(parts(0)), Integer.parseInt(parts(1)))
                    })
                    .filter(pair => pair._1 < 5)

        val secondRDD = sc.textFile("small_data/tuple2")
                    .map(line => {
                        val parts = line.split(" ")
                        (Integer.parseInt(parts(0)), Integer.parseInt(parts(1)))
                    })
                    .filter(pair => pair._1 < 10)

        val joined = firstRDD.join(secondRDD)
                        .filter(joinedPair =>  //(Int, (Int, Int)) <- (k, (v1, v2))
                            joinedPair._2._1 < joinedPair._2._2
                        )
                    .collect()
                    
        println("Join: "+joined.mkString("\n"))

    }
}