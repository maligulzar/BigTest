package SymexScala

import scala.collection.mutable.ArrayBuffer
import scala.reflect.runtime.universe._
// import SymexScala.TriState

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

class Conjunction(c: Array[Clause]) {
    val clauses: Array[Clause] = c //there are (implicit) conjunctions among elements of array (clauses)

    def conjunctWith(other: Conjunction): Conjunction = {
        //TODO: might want to simplify before merging, in case there are inconsistent clauses or repetitive ones
        new Conjunction(clauses ++ other.clauses)
    }

    override def toString: String = {
        if(clauses.length == 0)
            return ""
        var result = clauses(0).toString
        for(i <- 1 to clauses.length-1) {
            result += " && "+clauses(i)
        }
        result
    }
}

//companion object
object Conjunction {
    def parseConjunction(str: String): Conjunction = {
        val strClauses = str.replaceAll("\\s", "").split("&&")
        val clauses: Array[Clause] = strClauses.map(str => parseClause(str))
        new Conjunction(clauses)
    }

    def parseClause(str: String): Clause = {
        //TODO: remove () from beginning and end of clause
        val op = """<=|>=|==|!=|<|>""".r
        val matched = op.findAllIn(str).toArray
        if(matched.length > 1) {
            println("Parse Error: More than one comparison operator in one clause: "+str)
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

    def parseExpr(str: String): Expr[_] = {
        //first check for partialExpr
        val op = """\+|-|\*|/""".r
        return SymVar[Numeric](str)
        // op.findFirstIn(str) match {
        //     case Some(matched) => {
        //         //ArithmeticOp(matched)
        //         val index = str.indexOf(matched)
        //         val left = str.substring(0, index)
        //         val right = str.substring(index + 1)
        //         return PartialExpr(parseExpr(left), ArithmeticOp.withName(matched), parseExpr(right))
        //     }
        //     case None => { //it did not contain any arithmetic operator
        //         try {
        //             val parsed = Integer.parseInt(str)
        //             return ConcreteValue[Numeric](parsed)
        //         } catch {
        //             case e: NumberFormatException => {
        //                 try { 
        //                     val bool = str.toBoolean
        //                     return ConcreteValue[NonNumeric](parsed)
        //                 } catch {
        //                     case e: Exception => {
        //                         return SymVar[Numeric](str) //TODO: how should I know?
        //                     }
        //                 }
        //             }
        //         }
        //     }
        // }
    }
}

//may need to convert each clause to a partial evaluation
class Clause (left: Expr[_], op: ComparisonOp = null, right: Expr[_] = null) {

    var leftExpr: Expr[_] = left
    var compOp: ComparisonOp = op
    var rightExpr: Expr[_] = right

    override def toString: String = {
        if(compOp == null || rightExpr == null) leftExpr.toString
        else leftExpr.toString+" "+compOp.toString+" "+rightExpr.toString
    }
}


abstract class Expr[T <: VType] {
    def toString: String
    def check: Boolean
}

abstract class Terminal[T <: VType] extends Expr[T] {
    override def check: Boolean = {true}
}

case class Operator[T <: VType](op: ArithmeticOp) extends Terminal[T] {
    override def toString: String = {"op("+op+")"}
}

case class SymVar[T <: VType](name: String) extends Terminal[T] {
    // val typeOfVar: Type = typeOf[T]
    override def toString: String = {"SymVar("+name+")"}
}

case class ConcreteValue[T <: VType](value: AnyVal) extends Terminal[T] {
    override def toString: String = {value.toString}

    //TODO: check if ConcreteValue is parsed according to specified type successfully
    // override def check: Boolean = {
    //     typeOf[T] match {
    //         case x: Numeric => {
    //             try{
    //                 x.ut case 
    //             }
    //         }
    //         case y: NonNumeric =>
    //     }
    // }
}

case class NonTerminal[T <: VType](middle: Terminal[T], left: Expr[T] = null, right: Expr[T] = null) extends Expr[T] {
    val opOrLeaf: Terminal[T] = middle

    val leftExpr: Expr[T] = left
    val rightExpr: Expr[T] = right

    override def check: Boolean = {
        opOrLeaf match {
            case op: Operator[_] => 
                (leftExpr != null && rightExpr != null
                    && leftExpr.check && rightExpr.check)
            case _ => opOrLeaf.check //it's either a symVar or a concereteValue 
        }
    }

}


