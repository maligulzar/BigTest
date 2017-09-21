import org.apache.spark.{ SparkContext, SparkConf }

object Test4 {

    def main(args: Array[String]): Unit = {

        val conf = new SparkConf()
                    .setAppName("Scala Toy Example 1: Add Integers")
                    .setMaster("local[4]")
        val sc = new SparkContext(conf)
        val sum = sc.textFile("input")
                    .map(line => Integer.parseInt(line))
                    .map(x => if(x > 100) x else 0)
                    .filter(x => x > 10)
                    .map(x => if(x < 200) -200 else x)
                    .filter(x => x > 0)
                    //.reduce(_+_)

        // println("Sum: "+sum)

    }
}