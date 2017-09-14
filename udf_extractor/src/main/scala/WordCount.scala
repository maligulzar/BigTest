import org.apache.spark.{ SparkConf, SparkContext }

object WordCount {
    def main(args: Array[String]): Unit = {
        val sparkContext = new SparkContext(new SparkConf().setMaster("local[1]").setAppName("ok"))
        ///Users/malig/workspace/spark2.2.0/spark-2.2.0/README.md
        val result = 
        sparkContext.textFile("input")
        .map(s => s.toInt)
        .map { p =>
            def multiple(value: Int): Int = {
                if (value > 0) {
                    value * 2
                } else
                    value
            }
            if (p > 10) {
                multiple(p)
            } else if (p < 5) {
                -1
            } else {
                0
            }
        }
        .filter(p => p > 0)

        //println(result.collect().mkString("\n"))
    }
}