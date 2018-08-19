package subject.programs

import org.apache.spark.{SparkConf, SparkContext}

/**
  * Created by malig on 3/27/18.
  */
object FindSalarySum {
  def main(args: Array[String]): Unit = {
    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")
    val data1 = Array("0",
      "$0",
      "",
      "800",
      "$800",
      "$")

    val startTime = System.currentTimeMillis();
    val sc = new SparkContext(conf)
    for (i <- 0 to data1.length - 1) {
      try {
        val lines = sc.parallelize(Array(data1(i)))
        val sum = lines.map {
          line =>
            if (line.substring(0, 1).equals("$")) {
              var i = line.substring(1, 6)
              i
            } else {
              line
            }
        }
          .map(p => Integer.parseInt(p))
          .filter(r => r < 300)
          .reduce(_ + _)
        println(sum)
      }
      catch {
        case e: Exception =>
          e.printStackTrace()
      }

    }
    println("Time: " + (System.currentTimeMillis() - startTime))
  }
}

//.textFile("/Users/malig/workspace/up_jpf/benchmarks/src/datasets/salary.csv")

/** *
  * *
  *
  *
  *
  *
  *
  *
  *
  *
  *
  val text = sc.textFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/bigsift/income/*").sample(false, 0.001)
text.cache()
  text.count()
text.map{ line => if (line.substring(0, 1).equals("$")) { var i = line.substring(1); i } else {line}}.map(p => Integer.parseInt(p)).filter( r => r < 300).reduce(_+_)

  text.map{ line => if (line.substring(0, 1).equals("$")) { var i = line.substring(1); i } else {line}}.map(p => Integer.parseInt(p)).filter( r => r >= 300).count()

  text.filter{ line => line.substring(0, 1).equals("$")}.count()


  text.filter{ line => !line.substring(0, 1).equals("$")}.count()
  * *
  *
  *
  * (define-fun integer ((x!1 String) (x!2 String) (x!3 String)) Bool
  * (str.in.re x!1 (re.++ (str.to.re x!2) (re.* (re.++ (str.to.re x!3) (str.to.re x!2) ))))
  * )
  * *
  * (declare-fun s () String)
  * (assert ( integer s) )
  * (check-sat)
  * (get-model)
  *
  *
  *
  */ */


/**
  *
  *
        .map {
          line =>
            if (line.substring(0, 1).equals("$")) {
              var i = line.substring(1, 6)
              i
            } else {
              line
            }
          }
          .map(p => Integer.parseInt(p))
          .filter(r => r < 300)
          .reduce(_ + _)

filter2 > 1
map3> "1"
map4 > "123"
reduce1> {1,2,3,4}
DAG >reduce1-filter2:filter2-map3:map3-map4
K_BOUND >5
  */

