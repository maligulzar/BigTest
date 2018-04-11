package symexScala

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
    val _String = Value("String")

}

import NumericUnderlyingType._
import NonNumericUnderlyingType._

abstract class VType {
    type t <: AnyRef
    def underlyingType: t
    def toZ3Query(): String
    override def equals(that: Any): Boolean = that match {
        case that: VType => this.underlyingType == that.underlyingType
        case _ => false
    }
}



//case class SString(ut: NonNumericUnderlyingType) extends VType {
//    val underlyingType: NonNumericUnderlyingType = ut
//    def toZ3Query(): String = {
//        ut.toString
//    }
//}

case class Numeric(ut: NumericUnderlyingType) extends VType {
    type t = NumericUnderlyingType
    val underlyingType = ut
    def toZ3Query(): String = {
        ut.toString
    }
}

case class NonNumeric(ut: NonNumericUnderlyingType) extends VType {
    type t = NonNumericUnderlyingType
    val underlyingType = ut
    def toZ3Query(): String = {
        ut.toString
    }
}


case class CollectionNonNumeric(ut: NonNumericUnderlyingType) extends VType {
    type t = NonNumericUnderlyingType
    val underlyingType = ut
    def toZ3Query(): String = {
        ut.toString
    }
}

case class CollectionNumeric(ut: NumericUnderlyingType) extends VType {
    type t = NumericUnderlyingType
    val underlyingType = ut
    def toZ3Query(): String = {
        ut.toString
    }
}

case class Tuple(ut1: VType, ut2: VType) extends VType {
    type t = Tuple2[VType, VType]
    val underlyingType = new Tuple2(ut1, ut2)
    val _1Type = ut1
    val _2Type = ut2
    //Todo: Fix this
    def toZ3Query(): String = {
        ""
    }
}