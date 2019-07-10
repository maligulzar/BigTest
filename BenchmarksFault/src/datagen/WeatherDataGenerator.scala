package datagen

import org.apache.spark.{SparkConf, SparkContext}

import scala.util.Random

/**
  * Created by ali on 2/25/17.
  */
object WeatherDataGenerator {
  def main(args:Array[String]) =
  {
    val sparkConf = new SparkConf()
    var logFile = ""
    var partitions = 16
    var dataper  = 2
    if(args.length < 2) {
      sparkConf.setMaster("local[6]")
      sparkConf.setAppName("TermVector_LineageDD")//.set("spark.executor.memory", "2g")
      logFile =  "/Users/malig/workspace/git/BigSiftUI/weatherdata"
      //logFile = args(0)
      partitions = 1
      dataper = 50
    }else{
      logFile = args(0)
      partitions =args(1).toInt
      dataper = args(2).toInt
    }
    val sc = new SparkContext(sparkConf)
    sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
      (1 to dataper).flatMap{_ =>
        var zipcode = (Random.nextInt(9)+1).toString + Random.nextInt(10).toString + Random.nextInt(10).toString + Random.nextInt(10).toString + Random.nextInt(10).toString
        var list = List[String]()
        for(day <- 1 to 30){
          for(m <- 1 to 12){
            for( y <- 1900 to 2016){
              var snow = "0mm"
              if(zipcode.startsWith("3") || zipcode.startsWith("7") || zipcode.startsWith("9")){
                snow = getLowSnow()
                list = s"""$zipcode,$day/$m/$y,$snow""" :: list
              }else{
                snow = getHighSnow()
                list = s"""$zipcode,$day/$m/$y,$snow""" :: list
              }
            }
          }
        }
        list}.iterator}.saveAsTextFile(logFile)


  }
  def getLowSnow(): String = {
    if(Random.nextInt(90000000) == 99999){
      return  "90in"
    }
    if(Random.nextInt(2) == 0){
      return Random.nextInt(160) + "mm"
    }else{
      return (Random.nextFloat()/2) + "ft"
    }
  }
  def getHighSnow(): String ={
    if(Random.nextInt(90000000) == 99999){
      return  "90in"
    }
    if(Random.nextInt(2) == 0){
      return Random.nextInt(4000) + "mm"
    }else{
      return (Random.nextFloat()*13) + "ft"
    }
  }
}