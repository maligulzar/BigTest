package datagen

import java.io.File

import org.apache.spark.{SparkConf, SparkContext}

import scala.util.Random

/**
  * Created by ali on 7/20/17.
  */
object AirportTransitDataGenerator {

  def addTime(arr: String, fl: Float) : String = {
    val arr_min = arr.split(":")(0).toInt*60 + arr.split(":")(1).toInt
    val dep_min = (arr_min + fl*60).toInt
    val hours = dep_min/60 % 24
    val min = dep_min % 60
    return hours.toInt+":"+min.toInt

  }
  def getAirportCode(): String ={
    val arr = Array("LAX" , "SFO" , "JFK" , "ORD" , "MDW" , "SEA" , "SJC" , "BNA" , "LGA" , "DAL" , "FTW" , "PHX" , "BUR" , "JAX" , "ATL" , "MNN"
    )//, "KOX", "OAK" , "RNO" , "ANC" , "MIA" , "MCO" , "BOS" , "DTW" , "MSP" , "EWR" , "ROC" , "SYR" , "CLE" , "PDX" , "PHL" , "PVD" , "HOU" , "SLC",
    // "MSN" , "MKE" , "LHR" , "LHE" , "IST" , "ISB" , "RYD" , "DBX" , "ADU" , "FRK"  , "FRN" , "IRN" , "JAP" , "SUL" , "POL" , "PUP" , "SYX",
    // "MLB" , "PRT" , "MNA" , "MUX" , "MLA" , "SPB" , "MOS" , "CAR" , "CUZ" , "RDJ" , "SPO" , "OCA" , "LBG" , "BUB" , "LAK" , "LUT" , "XYK" ,
    // "ZUT" , "AUZ" , "AUX" , "ZUN" , "ZXA" , "NPW" , "NBA" , "NVM" , "PNA" , "EWQ" , "QWS" , "QRD"  , "LAS" , "NOW" , "WER" , "WRT" , "WPO")

    val one = Random.nextInt(arr.length)
    arr(one)
  }
  def main(args:Array[String]) =
  {
    val sparkConf = new SparkConf()
    var logFile = ""
    var partitions = 1
    var dataper  = 9000000
    if(args.length < 2) {
      sparkConf.setMaster("local[6]")
      sparkConf.setAppName("TermVector_LineageDD").set("spark.executor.memory", "2g")
      logFile =  "/Users/malig/workspace/git/BigSiftUI/airportdata"
    }else{
      logFile = "hdfs://scai01.cs.ucla.edu:9000//clash/datasets/bigsift/weather"
      logFile = args(3)
      partitions =args(1).toInt
      dataper = args(2).toInt
    }
    if(new File(logFile).exists()){
      deleteDir(new File(logFile))
    }

    val sc = new SparkContext(sparkConf)
    sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
      (1 to dataper).map{_ =>
        val airportcode = getAirportCode()
        val date = (Random.nextInt(12)+1).toString +"/" + Random.nextInt(31).toString + "/" +  (Random.nextInt(8)+10).toString
        val passid = (Random.nextInt(8)+10).toString +(Random.nextInt(8)+10).toString +(Random.nextInt(8)+10).toString
        val arrival = (Random.nextInt(24)).toString + ":" + (Random.nextInt(60)).toString
        val transit:Float = (Random.nextInt(4)+1).toFloat/2f
        val dep  = addTime(arrival, transit)

        s"""$date,$passid,$arrival,$dep,$airportcode"""
      }.iterator}.saveAsTextFile(logFile)


  }

  def deleteDir(file: File): Unit = {
    val contents = file.listFiles
    if (contents != null) for (f <- contents) {
      deleteDir(f)
    }
    file.delete
  }

}


/*
For Spark Shell



import scala.util.Random

 def addTime(arr: String, fl: Float) : String = {
    val arr_min = arr.split(":")(0).toInt*60 + arr.split(":")(1).toInt
    val dep_min = (arr_min + fl*60).toInt
    val hours = dep_min/60 % 24
    val min = dep_min % 60
    return hours.toInt+":"+min.toInt

  }
  def getAirportCode(): String ={
    val arr = Array("LAX" , "SFO" , "JFK" , "ORD" , "MDW" , "SEA" , "SJC" , "BNA" , "LGA" , "DAL" , "FTW" , "PHX" , "BUR" , "JAX" , "ATL" , "MNN" , "KOX",
                    "OAK" , "RNO" , "ANC" , "MIA" , "MCO" , "BOS" , "DTW" , "MSP" , "EWR" , "ROC" , "SYR" , "CLE" , "PDX" , "PHL" , "PVD" , "HOU" , "SLC",
                    "MSN" , "MKE" , "LHR" , "LHE" , "IST" , "ISB" , "RYD" , "DBX" , "ADU" , "FRK"  , "FRN" , "IRN" , "JAP" , "SUL" , "POL" , "PUP" , "SYX",
                    "MLB" , "PRT" , "MNA" , "MUX" , "MLA" , "SPB" , "MOS" , "CAR" , "CUZ" , "RDJ" , "SPO" , "OCA" , "LBG" , "BUB" , "LAK" , "LUT" , "XYK" ,
                    "ZUT" , "AUZ" , "AUX" , "ZUN" , "ZXA" , "NPW" , "NBA" , "NVM" , "PNA" , "EWQ" , "QWS" , "QRD"  , "LAS" , "NOW" , "WER" , "WRT" , "WPO")

    val one = Random.nextInt(arr.length)
    arr(one)
  }
       val logFile = "hdfs://scai01.cs.ucla.edu:9000//clash/datasets/bigsift/airport20"
       val partitions = 32
       val dataper = 20000000
      sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
        (1 to dataper).map{_ =>
          val airportcode = getAirportCode()
          val date = (Random.nextInt(12)+1).toString +"/" + Random.nextInt(31).toString + "/" +  (Random.nextInt(8)+10).toString
          val passid = (Random.nextInt(8)+10).toString +(Random.nextInt(8)+10).toString +(Random.nextInt(8)+10).toString
          val arrival = (Random.nextInt(24)).toString + ":" + (Random.nextInt(60)).toString
          val transit:Float = (Random.nextInt(4)+1).toFloat/2f
          val dep  = addTime(arrival, transit)

          s"""$date,$passid,$arrival,$dep,$airportcode"""
        }.iterator}.saveAsTextFile(logFile)


*/