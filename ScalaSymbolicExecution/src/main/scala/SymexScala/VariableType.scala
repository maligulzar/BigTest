package SymexScala

import scala.collection.mutable.ArrayBuffer
import scala.reflect.runtime.universe._

object NumericUnderlyingType extends Enumeration {
    type NumericUnderlyingType = Value
    val _Byte = Value("Byte")
    val _Short = Value("Short")
    val _Int = Value("Int")
    val _Long = Value("Long")
    val _Double = Value("Double")
    val _Float = Value("Float")
}

object NonNumericUnderlyingType extends Enumeration {
    type NonNumericUnderlyingType = Value
    val _Boolean = Value("Boolean")
    val _Unit = Value("Unit")
}

import NumericUnderlyingType._
import NonNumericUnderlyingType._

abstract class VType {
    // type v <: AnyVal
    // def varVal: v
    def toZ3Query(): String
    def toConcretePythonExpr(value: String): String
}

case class Numeric(ut: NumericUnderlyingType) extends VType {
    val underlyingType: NumericUnderlyingType = ut
    def toZ3Query(): String = {
        ut.toString
    }
    
    // For Python, numeric strings are interpreted literally.
    // This is only intended for concrete expressions.
    override def toConcretePythonExpr(value: String): String = value
}

case class NonNumeric(ut: NonNumericUnderlyingType) extends VType {
    val underlyingType: NonNumericUnderlyingType = ut
    def toZ3Query(): String = {
        ut.toString
    }
    
    override def toConcretePythonExpr(value: String): String = ut match {
        case _Boolean =>
            // convert to boolean, than return the appropriate Python literal
            val pythonTrue = "True"
            val pythonFalse = "False"
            if(value.toBoolean) pythonTrue else pythonFalse
        case _Unit =>
            throw new NotImplementedError(s"Unknown non-numeric variable type: ${value} ($ut)")
        case _ =>
            throw new NotImplementedError(s"Unknown non-numeric variable type: ${value} ($ut)")
    }
}

case class Tuple(ut1: VType, ut2: VType) extends VType {
    val underlyingType: Tuple2[VType, VType] = new Tuple2(ut1, ut2)
    val _1Type = ut1
    val _2Type = ut2
    //Todo: Fix this
    def toZ3Query(): String = {
        ""
    }
    
    override def toConcretePythonExpr(value: String): String =
        throw new NotImplementedError("No python expression support for tuple data types")
}