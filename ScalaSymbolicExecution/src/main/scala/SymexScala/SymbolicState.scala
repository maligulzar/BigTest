package SymexScala

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Map

class SymbolicState(init: SetOfConstraints) {
    val symbolicEnv: Map[String, SymbolicVarDef] = Map[String, SymbolicVarDef]()
    val pc: SetOfConstraints = init
    val scopePointer: Int = 0

    def updateVarInEnv(name: String, vt: VType, newSymValue: Expr) = {
        var varDef = symbolicEnv.getOrElse(name, null)
        if(varDef == null) {
            symbolicEnv += (name -> new SymbolicVarDef(name, vt, scopePointer))
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
                symbolicEnv += (newName -> new SymbolicVarDef(newName, vt, scopePointer))
            }
        }
    }

    def isDefined(x: SymVar): Boolean = {
        val found = symbolicEnv.getOrElse(x.name, null)
        if(found != null && found.equals(x)) true
        else false
    }

    // def test() {
    //     symbolicEnv += new SymbolicVarDef[Int]("x")
    //     symbolicEnv += new SymbolicVarDef[String]("y")
    //     symbolicEnv += new SymbolicVarDef[Int]("z")

    //     println("------------------------------")
    //     println(symbolicEnv(0).variable.typeOfVar)
    //     println(symbolicEnv(1).variable.typeOfVar)
    //     println(symbolicEnv(2).variable.typeOfVar)
    //     println("------------------------------")
    // }

}

class SymbolicVarDef(name: String, vt: VType, sid: Int) {
    val variable: SymVar = new SymVar(vt, name) //!!
    var symbolicValue: Expr = variable //initially it is same as symbolicVariable
    val scopeID: Int = sid


    def updateEffect(effect: Expr) = {
        println("Variable "+name+" updated from "+symbolicValue+" to "+effect)
        symbolicValue = effect
    }
}


