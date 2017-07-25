import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }

object AddIntegers {

    def main(args: Array[String]): Unit = {

        Logger.getLogger("org").setLevel(Level.OFF)
        Logger.getLogger("akka").setLevel(Level.OFF)

        val conf = new SparkConf()
        conf.setAppName("Scala Toy Example 1: Add Integers")
        conf.setMaster("local[4]")
        val sc = new SparkContext(conf)
        val srcPath = args(0)
        val sum = sc.textFile(srcPath)
                    .map(line => Integer.parseInt(line))
                    .reduce(_+_)
        println("Sum: "+sum)

    }
}
