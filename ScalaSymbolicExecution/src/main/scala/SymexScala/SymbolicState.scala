package SymexScala

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Map

import NumericUnderlyingType._
import NonNumericUnderlyingType._

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
        val found = symbolicEnv.getOrElse(x.name, null)
        if(found != null && found.equals(x)) true
        else false
    }

    //returns null if no variable is defined under such a name!
    def getSymVar(name: String): SymVar = {
        val found = symbolicEnv.getOrElse(name, null)
        if(found != null) found.variable
        else null   
    }

    def getFreshName: String = {
        index = index+1
        "x"+index.toString
    }

    def getFreshSymVar(varType: String): SymVar = {
        val vType = varType match {
            case "int" => Numeric(_Int)
            case "double" => Numeric(_Double)
            case _ => NonNumeric(_Unit)
        }

        val varName = getFreshName
        val newVarDef = new SymbolicVarDef(varName, vType)
        symbolicEnv += (varName -> newVarDef)

        newVarDef.variable
    }

}

class SymbolicVarDef(name: String, vt: VType) {
    val variable: SymVar = new SymVar(vt, name) //!!
    var symbolicValue: Expr = variable //initially it is same as symbolicVariable

    override def toString: String = {
        variable.toString+" -> "+symbolicValue.toString
    }

    def updateEffect(effect: Expr) = {
        println("Variable "+name+" updated from "+symbolicValue+" to "+effect)
        symbolicValue = effect
    }
}


