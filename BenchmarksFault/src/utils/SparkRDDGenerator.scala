package utils

import org.apache.spark.rdd.RDD

/**
  * Created by malig on 1/14/19.
  */
trait SparkRDDGenerator {
  def execute(input1 : RDD[String] , input2 : RDD[String] = null) : RDD[String]
}
