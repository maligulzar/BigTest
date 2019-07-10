package datagen

import org.apache.spark.{SparkConf, SparkContext}

import scala.util.Random

/**
  * Created by malig on 8/8/18.
  */
object L2DataGen {
  def main(args:Array[String]) =
  {
    val sparkConf = new SparkConf()
    var logFile = ""
    var partitions = 2
    var dataper  = 50
    if(args.length < 2) {
      sparkConf.setMaster("local[6]")
      sparkConf.setAppName("TermVector_LineageDD").set("spark.executor.memory", "2g")
      logFile =  "/Users/malig/workspace/up_jpf/benchmarks/src/datasets/"
    }else{
      logFile = args(0)
      partitions =args(1).toInt
      dataper = args(2).toInt
    }
    val page = logFile + "page_views"
    val users = logFile + "power_users"

    val sc = new SparkContext(sparkConf)
    sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
      (1 to dataper).flatMap{_ =>
        var list = List[String]()
        list = s"""${getKey()},${getThreeLetter()},${getTime()},${getInfoString(15)},${getIp()},${getTime()},${getRevenue()},${getInfoString(20)},${getInfoString(20)}""" :: list
        list}.iterator}.saveAsTextFile(page)

    sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
      (1 to dataper/100).flatMap{_ =>
        var list = List[String]()
        list = s"""${getKey()},${getPhoneNumber()},${getInfoString(20)},${getInfoString(10)},${getInfoString(2)},${zipcode}""" :: list
        list}.iterator}.saveAsTextFile(users)

  }


  def randomStringFromCharList(length: Int, chars: Seq[Char]): String = {
    val sb = new StringBuilder
    for (i <- 1 to length) {
      val randomNum = util.Random.nextInt(chars.length)
      sb.append(chars(randomNum))
    }
    sb.toString
  }

  def randomString(length: Int) = {
    val chars = ('a' to 'z') ++ ('A' to 'Z')
      randomStringFromCharList(length, chars)
  }
  def getThreeLetter(): String ={
        return randomString(3)
  }
  def getTime(): Long = {
    Random.nextLong();
  }
  def getIp(): String ={
    return Random.nextInt(1000) +"."+Random.nextInt(1000) +"."+Random.nextInt(1000) +"."+Random.nextInt(1000)
  }
  def getRevenue(): String ={
    Random.nextInt(1000000).toString
  }
  def getInfoString(n:Int): String ={
    randomString(n)
  }
  def getPhoneNumber(): Int = {
    100000000 + Random.nextInt(899999999)
  }

  def getKey(): String ={
    return randomString(2) + Random.nextInt(100)
  }
  def zipcode = "9" + "0"+ "0" + Random.nextInt(10).toString + Random.nextInt(10).toString

}


/***
  *
  *
  *

import scala.util.Random
    val logFile = "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/bigsift/"
    val page = logFile + "page_views"
    val users = logFile + "power_users"
    var partitions = 32
    var dataper  = 5000000

    def getThreeLetter(): String ={
        return Random.nextString(3)
  }
  def getTime(): Long = {
    Random.nextLong();
  }
  def getIp(): String ={
    return Random.nextInt(1000) +"."+Random.nextInt(1000) +"."+Random.nextInt(1000) +"."+Random.nextInt(1000)
  }
  def getRevenue(): String ={
    Random.nextInt(1000000).toString
  }
  def getInfoString(n:Int): String ={
    Random.nextString(n)
  }
  def getPhoneNumber(): Int = {
    100000000 + Random.nextInt(899999999)
  }

  def getKey(): String ={
    return Random.nextString(2) + Random.nextInt(100)
  }
  def zipcode = "9" + "0"+ "0" + Random.nextInt(10).toString + Random.nextInt(10).toString

    sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
      (1 to dataper).flatMap{_ =>
        var list = List[String]()
        list = s"""${getKey()},${getThreeLetter()},${getTime()},${getInfoString(15)},${getIp()},${getTime()},${getRevenue()},${getInfoString(20)},${getInfoString(20)}""" :: list
        list}.iterator}.saveAsTextFile(page)

    sc.parallelize(Seq[Int]() , partitions).mapPartitions { _ =>
      (1 to dataper/2).flatMap{_ =>
        var list = List[String]()
        list = s"""${getKey()},${getPhoneNumber()},${getInfoString(20)},${getInfoString(10)},${getInfoString(2)},${zipcode}""" :: list
        list}.iterator}.saveAsTextFile(users)
  */