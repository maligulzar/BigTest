/**
  * Created by malig on 5/3/16.
  *
  * Sample Configuration File
  *
  * TARGETOPERATORS=+*-/
  * MUTATIONMAPPING=+ -> -,- -> + , * -> / , / ->
  *
  */

import scala.collection.mutable.Map
object Configuration{
  val dataflowOperations: List[String] = List(
    "map",
    "flatMap",
    "filter",
    "mapPartitions",
    "mapPartitionsWithIndex",
    "sample",
    "groupByKey",
    "reduceBykey")
}

class Configuration(filename: String) {



  val operatorMap: Map[String, String] = Map[String, String](
    "&&" -> "$amp$amp",
    "+" -> "$plus",
    "/" -> "$div",
    "*" -> "$times",
    "-" -> "$minus",
    "<" -> "$less",
    ">" -> "$greater",
    ">=" -> "$greater$eq",
    "<=" -> "$less$eq",
    "==" -> "$eq$eq",
    "!=" -> "$bang$eq")

  var inverseOpMap: Map[String, String] = Map[String, String]()
  for (k <- operatorMap.keySet) {
    inverseOpMap += (operatorMap(k) -> k)
  }

  var sparkMutationMapping: Map[String, Array[String]] = Map[String, Array[String]]()
  sparkMutationMapping("union") = Array("intersection")
  sparkMutationMapping("intersection") = Array("union")
  sparkMutationMapping("distinct") = Array("sortByKey")
  sparkMutationMapping("sortByKey") = Array("distinct")
  sparkMutationMapping("join") = Array("leftOuterJoin", "rightOuterJoin", "fullOuterJoin")
  sparkMutationMapping("leftOuterJoin") = Array("join", "rightOuterJoin", "fullOuterJoin")
  sparkMutationMapping("rightOuterJoin") = Array("leftOuterJoin", "join", "fullOuterJoin")
  sparkMutationMapping("fullOuterJoin") = Array("leftOuterJoin", "rightOuterJoin", "join")
  sparkMutationMapping("coalesce") = Array("repartition")
  sparkMutationMapping("repartition") = Array("coalesce")

  var targetOp: List[String] = List()
  var mutationMapping: Map[String, String] = Map[String, String]()
  var enableSparkCompatibleMutation = false
  var enablePMutation = false
  var probab = 1f
  val r = scala.util.Random

  def matchMutationTarget(s: String): Boolean = {
    targetOp.contains(s)
  }

  def enableSparkMutation(): Configuration = {
    this.enableSparkCompatibleMutation = true;
    this
  }

  def enableProbablisticMutation(f: Float): Configuration = {
    enablePMutation = true
    probab = f
    this
  }

  def getSparkConf(): Boolean = {
    this.enableSparkCompatibleMutation
  }

  def loadMapping(): Configuration = {
    val source = scala.io.Source.fromFile(filename)
    try {
      val iter = source.getLines()
      for (a <- iter) {
        if (a.startsWith("TARGETOPERATORS=")) {
          val st = a.replaceFirst("TARGETOPERATORS=", "")
          targetOp = st.trim.filter(a => operatorMap.keySet.contains(a.toString)).map(a => operatorMap(a.toString)).toList
        } else if (a.startsWith("MUTATIONMAPPING=")) {
          val st = a.replaceFirst("MUTATIONMAPPING=", "")
          for (e <- st.trim.split(",")) {
            val op = e.split("->")(0).trim
            val t_op = e.split("->")(1).trim
            if (!operatorMap.keySet.contains(op) || !operatorMap.keySet.contains(t_op)) {
              println("Invalid mappings")
            } else {
              mutationMapping += (op -> t_op)
            }
          }
        }
      }
    } catch {
      case e: Exception =>
        println("Invalid Configuration File format")
    } finally source.close()

    return this
  }

  def getMutation(s: String, op: String): String = {
    val inverse = inverseOpMap(s)
    if (inverse == op && r.nextFloat() < probab) {
      val b = operatorMap(mutationMapping(inverse))
      println(s""" $s -> $b """)
      return b
    }
    return s
  }

  def getSparkMutation(original: String): String = {
    if (!sparkMutationMapping.contains(original))
      return original
    val mapped = sparkMutationMapping(original)
    if (mapped.length == 1)
      return mapped(0)
    else if (mapped.length > 1)
      return mapped(r.nextInt(mapped.length))
    else
      return original
  }

}
