package SymexScala

import scala.collection.mutable.ArrayBuffer
import scala.reflect.runtime.universe._

class SymbolicState(init: SetOfConstraints) {
    val symbolicEnv: ArrayBuffer[SymbolicVarDef[_]] = new ArrayBuffer[SymbolicVarDef[_]]()
    val pc: SetOfConstraints = init
    val programCounter: Int = 0 //usage?

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

    //add a new variable decl to the env and check for duplicate names
    //update path constraint
    //
}

class SymbolicVarDef[T <: VType](name: String) {
    val variable: SymVar[T] = new SymVar[T](name)
    val symbolicValue: Expr[T] = new SymVar[T](name)

    //update symbolicValue to another expr
}


