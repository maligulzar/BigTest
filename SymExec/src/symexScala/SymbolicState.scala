package symexScala

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Map

import NumericUnderlyingType._
import NonNumericUnderlyingType._

object SymbolicState {
  def getVType(primitive: String): VType = {
    primitive match {
      case "int"              => Numeric(_Int)
      case "double"           => Numeric(_Double)
      case "int[]"            => CollectionNumeric(_Int)
      case "java.lang.String" => NonNumeric(_String)
      case _                  => NonNumeric(_Unit)
    }
  }
}
class SymbolicState() {

  val symbolicEnv: Map[String, SymbolicVarDef] = Map[String, SymbolicVarDef]()
  var index: Int = -1

  /*
    def updateVarInEnv(name: String, vt: VType, newSymValue: Expr) = {
        var varDef = symbolicEnv.getOrElse(name, null)
        if(varDef == null) {
            symbolicEnv += (name -> new SymbolicVarDef(name, vt, index))
        } else {
            //name already exists in our env
            if(varDef.variable.actualType == vt) {
                //both name and type is the same -> we assume this is the same variable
                //TODO: might need to think about differentiating scopes between 2 different udfs with same variable name and type!
                varDef.updateEffect(newSymValue)
            }
            else {
                //same name, though different types -> "alpha renaming"
                //------->  update path constraint ---> has to return the new generated name!
                val ranStrGen = scala.util.Random.alphanumeric
                val newName = ranStrGen.take(5).mkString("")
                symbolicEnv += (newName -> new SymbolicVarDef(newName, vt, index))
            }
        }
    }
   */

  def isDefined(x: SymVar): Boolean = {
    val found = symbolicEnv.getOrElse(x.getName, null)
    if (found != null && found.equals(x)) true
    else false
  }

  //returns null if no variable is defined under such a name!
  def getSymVar(name: String): SymVar = {
    val found = symbolicEnv.getOrElse(name, null)
    if (found != null) found.variable
    else null
  }

  def getVType(primitive: String): VType = {
    primitive match {
      case "int"              => Numeric(_Int)
      case "double"           => Numeric(_Double)
      case "int[]"            => CollectionNumeric(_Int)
      case "java.lang.String" => NonNumeric(_String)
      case _                  => NonNumeric(_Unit)
    }
  }

  def getFreshName: String = {
    index = index + 1
    "x" + index.toString
  }

  def getFreshSymVar(primitive: String): SymVar = {
    val vType = getVType(primitive)
    val varName = getFreshName
    val newVar = new SymVar(vType, varName)

    val newVarDef = new SymbolicVarDef(newVar)
    symbolicEnv += (varName -> newVarDef)

    newVar
  }

}

class SymbolicVarDef(v: SymVar) {
  val variable: SymVar = v
  var symbolicValue: Expr = v //initially it is same as symbolicVariable

  override def toString: String = {
    variable.toString + " -> " + symbolicValue.toString
  }

  def updateEffect(effect: Expr) = {
    println(
      "Variable " + v.getName + " updated from " + symbolicValue + " to " + effect)
    symbolicValue = effect
  }
}
