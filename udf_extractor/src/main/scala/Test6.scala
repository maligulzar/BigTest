import org.apache.spark.{ SparkContext, SparkConf }

object Test6 {

    def main(args: Array[String]): Unit = {

        val conf = new SparkConf()
                    .setAppName("Scala Toy Example 6: two maps")
                    .setMaster("local[4]")
        val sc = new SparkContext(conf)
        val sum = sc.textFile("input")
                    .map(line => Integer.parseInt(line))
                    .map(x => if(x > 100) x+1 else 0)
                    .map(y => if(y < 200) -200 else y-1)
                    
                    //.reduce(_+_)

        // println("Sum: "+sum)

    }
}