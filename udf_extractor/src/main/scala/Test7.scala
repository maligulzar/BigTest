import org.apache.spark.{ SparkContext, SparkConf }

object Test7 {

    def main(args: Array[String]): Unit = {

        val conf = new SparkConf()
                    .setAppName("Scala Toy Example 1: Add Integers")
                    .setMaster("local[4]")
        val sc = new SparkContext(conf)
        val sum = sc.textFile("input")
                    .flatMap(line => line.split(" "))
                    .map(number => Integer.parseInt(number))
                    // .map(x => if(x > 100) x else 0)
                    .reduce(_+_)

        // println("Sum: "+sum)

    }
}