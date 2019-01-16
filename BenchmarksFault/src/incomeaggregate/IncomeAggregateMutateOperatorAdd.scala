package incomeaggregate

import org.apache.spark.rdd.RDD
import org.apache.spark.{SparkConf, SparkContext}

/**
  * Created by malig on 1/11/19.
  */
object IncomeAggregateMutateOperatorAdd {

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
              var i = line.substring(1)
              i
            } else {
              line
            }
        }
          .map(p => Integer.parseInt(p))
          .filter(r => r < 300)
          .reduce(_ - _) // Injecting fault by mutating + with - ==> Should produce wrong output
        println(sum)
      }
      catch {
        case e: Exception =>
          e.printStackTrace()
      }

    }
    println("Time: " + (System.currentTimeMillis() - startTime))
  }

  def execute(input1: RDD[String]): String = {
    val sum = input1.map {
      line =>
        if (line.substring(0, 1).equals("$")) {
          var i = line.substring(1)
          i
        } else {
          line
        }
    }
      .map(p => Integer.parseInt(p))
      .filter(r => r < 300)
      .reduce(_ - _) // Injecting fault by mutating + with - ==> Should produce wrong output
      .toString
    sum
  }
}
