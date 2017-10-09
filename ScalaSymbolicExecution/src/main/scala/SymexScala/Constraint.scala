package SymexScala

import scala.collection.mutable.ArrayBuffer
import scala.reflect.runtime.universe._

import NumericUnderlyingType._
import NonNumericUnderlyingType._

object ComparisonOp extends Enumeration {
    type ComparisonOp = Value
    val Equality = Value("==")
    val Inequality = Value("!=")
    val LessThan = Value("<")
    val LessThanOrEq = Value("<=")
    val GreaterThan = Value(">")
    val GreaterThanOrEq = Value(">=")

    def isComparisonOp(s: String): Boolean = values.exists(_.toString == s)
}

object ArithmeticOp extends Enumeration {
    type ArithmeticOp = Value
    val Addition = Value("+")
    val Subtraction = Value("-")
    val Multiplication = Value("*")
    val Division = Value("/")
}

import ComparisonOp._
import ArithmeticOp._

class Constraint(c: Array[Clause]) {
    var clauses: Array[Clause] = c //there are (implicit) conjunctions among elements of array (clauses)

    def this() {
        this(new Array[Clause](0))
    }

    override def toString: String = {
        if (clauses.length == 0)
            return ""
        var result = clauses(0).toString
        for (i <- 1 to clauses.length - 1) {
            result += " && " + clauses(i)
        }
        result
    }

    override def equals(other: Any): Boolean = {
        if(other != null && other.isInstanceOf[Constraint]) {
            this.clauses.deep == other.asInstanceOf[Constraint].clauses.deep
        }
        else false
    }

    def conjunctWith(other: Constraint) = {
        //TODO: might want to simplify before merging, in case there are inconsistent clauses or repetitive ones
        //new Constraint(clauses ++ other.clauses)
        clauses = clauses ++ other.clauses
    }

    def applyEffect(x: SymVar, effect: Expr): Constraint = {
        /*
            map builds a new collection(Array)
        */
        val updated = clauses.map(_.applyEffect(x, effect))
        // for(c <- clauses) {
        //     // if(c.contains(x)) 
        //     c.applyEffect(x, effect)
        // }
        new Constraint(updated)
    }

    def checkValidity(ss: SymbolicState): Boolean = {
        var result: Boolean = true
        for (c <- clauses) {
            result &= c.checkValidity(ss)
        }
        result
    }

    def deepCopy: Constraint = {
        val newArray = new Array[Clause](this.clauses.size)
        this.clauses.copyToArray(newArray) //TODO TEST: might shallow copying the clauses
        new Constraint(newArray)
    }
}

//companion object
/*
object Constraint {
    def parseConstraint(str: String): Constraint = {
        val strClauses = str.replaceAll("\\s", "").split("&&")
        val clauses: Array[Clause] = strClauses.map(str => parseClause(str))
        new Constraint(clauses)
    }

    def parseClause(str: String): Clause = {
        //TODO: remove () from beginning and end of clause
        val op = """<=|>=|==|!=|<|>""".r
        val matched = op.findAllIn(str).toArray
        if (matched.length > 1) {
            println("Parse Error: More than one comparison operator in one clause: " + str)
            exit(1)
        } else if (matched.length == 0) {
            return new Clause(parseExpr(str)) //Expr
        }

        val comp = ComparisonOp.withName(matched(0))
        val index = str.indexOf(matched(0))

        val leftStr = parseExpr(str.substring(0, index))
        val rightStr = parseExpr(str.substring(index + matched(0).length))

        return new Clause(leftStr, comp, rightStr)
    }
}
*/

class Clause(left: Expr, op: ComparisonOp = null, right: Expr = null) {

    var leftExpr: Expr = left
    val compOp: ComparisonOp = op
    var rightExpr: Expr = right
    assert(left != null)

    override def toString: String = {
        if (compOp == null || rightExpr == null) leftExpr.toString
        else leftExpr.toString + " " + compOp.toString + " " + rightExpr.toString
    }

    override def equals(other: Any): Boolean = {
        if(other != null && other.isInstanceOf[Clause]) {
            this.toString == other.asInstanceOf[Clause].toString
        }
        else false
    }

    def applyEffect(x: SymVar, effect: Expr): Clause = {
        val newLeftExpr = leftExpr.applyEffect(x, effect)

        val newRightExpr =
            if (rightExpr != null) {
                rightExpr.applyEffect(x, effect)
            } else null

        new Clause(newLeftExpr, this.compOp, newRightExpr)
    }

    def checkValidity(ss: SymbolicState): Boolean = {
        var leftRes = leftExpr.checkValidity(ss)

        if (rightExpr != null) leftRes && rightExpr.checkValidity(ss)
        else leftRes
    }
}

abstract class Expr {
    val actualType: VType

    def toString: String
    def applyEffect(x: SymVar, effect: Expr): Expr
    def checkValidity(ss: SymbolicState): Boolean
}

abstract class Terminal extends Expr {}

case class SymOp(atype: VType, op: ArithmeticOp) /*extends Terminal*/ {
    val actualType = atype
    override def toString: String = { op.toString }
}

class SymVar(atype: VType, name: String) extends Terminal {
    val actualType = atype

    override def toString: String = { name /*+": "+actualType*/ }

    def getName: String = { name }

    override def applyEffect(x: SymVar, effect: Expr): Expr = {
        if (this.equals(x)) effect
        else this //TODO TEST: may need to do a deep-copy instead of returning the same instance, in case of further effects 
    }

    override def checkValidity(ss: SymbolicState): Boolean = {
        ss.isDefined(this)
    }
}

case class SymTuple(ttype: Tuple, name: String) extends SymVar(ttype, name) {
    override val actualType = ttype

    val _1: SymVar = new SymVar(ttype._1Type, name+"_1") 
    val _2: SymVar = new SymVar(ttype._2Type, name+"_2") 

    override def toString: String ={ name+"=("+_1.getName+", "+_2.getName+")"}

    //TODO: update this for tuple
    override def applyEffect(x: SymVar, effect: Expr): Expr = {
        if (this.equals(x)) effect
        else this
    }

    override def checkValidity(ss: SymbolicState): Boolean = {
        ss.isDefined(_1)
        ss.isDefined(_2)
    }

    def getFirst: SymVar = {_1}
    def getSecond: SymVar = {_2}

}
case class ConcreteValue(atype: VType, value: String) extends Terminal {
    val actualType = atype

    //check validity of passed ConcreteValue
    assert(atype match {
        case t: Numeric => try {
            val v = value.toDouble
            true
        } catch {
            case _: java.lang.NumberFormatException => false
        }
        case t: NonNumeric =>
            if (t.underlyingType == _Boolean) {
                try {
                    val b = value.toBoolean
                    true
                } catch {
                    case _: java.lang.IllegalArgumentException => false
                }
            } else true
    })

    override def toString: String = { value.toString /*+" of type "+actualType*/ }

    override def applyEffect(x: SymVar, effect: Expr): Expr = { this }

    override def checkValidity(ss: SymbolicState): Boolean = { true }
}

// case class UnaryExpr(op: SymOp, right: Expr) extends Expr{}

case class NonTerminal(left: Expr, middle: SymOp, right: Expr) extends Expr {
    val op: SymOp = middle

    val leftExpr: Expr = left
    val rightExpr: Expr = right

    //check validity of this partial expression before proceeding
    assert(left != null && right != null)
    assert(op.actualType == leftExpr.actualType && op.actualType == rightExpr.actualType)
    val actualType = op.actualType

    override def applyEffect(x: SymVar, effect: Expr): Expr = {
        new NonTerminal(left.applyEffect(x, effect), op, right.applyEffect(x, effect))
    }

    override def checkValidity(ss: SymbolicState): Boolean = {
        leftExpr.checkValidity(ss) && rightExpr.checkValidity(ss)
    }

    override def toString(): String = {
        left.toString + " " + op.toString + " " + right.toString
    }
}

