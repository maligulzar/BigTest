import org.apache.spark.{ SparkContext, SparkConf }

object Test5 {

    def main(args: Array[String]): Unit = {

        val conf = new SparkConf()
                    .setAppName("Scala Toy Example 5: Join preparation")
                    .setMaster("local[4]")
        val sc = new SparkContext(conf)
        val sum = sc.textFile("input")
                    .map(line => Integer.parseInt(line))
                    .map(x => (x, 1))
                    .map((x, y) => if(x > 100) x else 0)
                    
                    //.reduce(_+_)

        // println("Sum: "+sum)

    }
}