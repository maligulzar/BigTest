import org.apache.spark.SparkContext._
import org.apache.spark.{SparkContext, SparkConf}

/**
  * Created by ali on 2/25/17.
  */
object WeatherAnalysis {

  def main(args: Array[String]) {

    var logFile = ""
    val conf = new SparkConf().setAppName("Inverted Index")
    var local = true
    if (args.size < 2) {
      logFile = "README.md"
      conf.setMaster("local[2]")
    } else {
      logFile = args(1)
    }
    val spark = new SparkContext(conf)
      val lines = spark.textFile(logFile, 1)
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
        List[((String , String) , Float)](
          ((state , monthdate) , snow) ,
          ((state , year)  , snow)
        ).iterator
      }
      val deltaSnow = split.groupByKey().map{ s  =>
        val delta =  s._2.max - s._2.min
        (s._1 , delta)
      }
    val output = deltaSnow.collect
      spark.stop()
    }
  }

  def convert_to_mm(s: String): Float = {
    val unit = s.substring(s.length - 2)
    val v = s.substring(0, s.length - 2).toFloat
    unit match {
      case "mm" => return v
      case _ => return v * 304.8f
    }
  }
  def failure(record:Float): Boolean ={
    record > 6000f
  }
  def zipToState(str : String):String = {
    return (str.toInt % 50).toString
  }


}