/**
  * Created by malig on 3/27/18.
  */
object Split {

  val sample = "23,4,,5,5,6,24:4"

  def main(args: Array[String]): Unit = {
    println(split(sample, 5, ","))
  }

  def split(s: String, index: Int, d: String): String = {
    var c = 0
    var i = s.indexOf(d)
    var o = 0
    if (i == -1 && index == 0) {
      return s
    } else {
      c = c + 1
    }
    o = 0
    while (c <= index && i != -1) {
      o = i + 1
      i = s.indexOf(d, i + 1)
      c = c + 1
    }
    if (i == -1) {
      return s.substring(o, s.length)
    } else {
      return s.substring(o, s.indexOf(d, i))
    }
  }
}
