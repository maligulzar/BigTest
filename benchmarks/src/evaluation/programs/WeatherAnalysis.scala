package evaluation.programs

import org.apache.spark.{SparkConf, SparkContext}

object WeatherAnalysis{

  def main(args:Array[String]) : Unit = {

    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")
    val sc = new SparkContext(conf)

    val lines = sc.textFile("/Users/malig/workspace/up_jpf/benchmarks/src/datasets/weatherdata/*", 1)
    val split = lines.flatMap{s =>
      val tokens = s.split(",")
      // finds the state for a zipcode
      var state = zipToState(tokens(0))
      var date = tokens(1)
      // gets snow value and converts it into millimeter
      val snow = convert_to_mm(tokens(2))
      //gets year
      val year = date.substring(date.lastIndexOf("/"))
      // gets month / date
      val monthdate= date.substring(0,date.lastIndexOf("/")-1)
      Array[((String, String), Float)](
        ((state, monthdate), snow),
        ((state, year), snow)
      )
    }
    val deltaSnow = split.groupByKey().map{ s  =>
      val delta =  s._2.max - s._2.min
      (s._1 , delta)
    }.filter(s => s._2 > 6000)

    val output = deltaSnow.collect().foreach(println)

  }

  def convert_to_mm(s: String): Float = {
    val unit = s.substring(s.length - 2)
    val v = s.substring(0, s.length - 2).toFloat
    if(unit.equals("mm")){
      return v
    }else{
      return v * 304.8f
    }

  }
  def zipToState(str : String):String = {
    return (str.toInt % 50).toString
  }
}