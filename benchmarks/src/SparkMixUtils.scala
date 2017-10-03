
import java.io.FileInputStream
import java.util.Properties

/**
 * Created by shrinidhihudli on 2/10/15.
 */

object SparkMixUtils {

  def createMap(mapString:String):Map[String, String] = {
    val map = mapString.split("\u0003").map(x => (x.split("\u0004")(0),x.split("\u0004")(1))).toMap
    map
  }

  def createBag(bagString:String):Array[Map[String, String]] = {
    val bag = bagString.split("\u0002").map(x => createMap(x))
    bag
  }

  def safeInt(string: String):Int = {
    if (string == "")
      0
    else
      string.toInt
  }

  def safeDouble(string: String):Double = {
    if (string == "")
      0
    else
      string.toDouble
  }

  def safeSplit(string: String, delim: String, int: Int):String = {
    val split = string.split(delim)
    if (split.size > int)
      split(int)
    else
      ""
  }

  def loadPropertiesFile():Properties = {
    val properties = new Properties()
    val propFile = getClass.getResourceAsStream("/app.properties")
    properties.load(propFile)
    propFile.close()
    properties
  }
}
