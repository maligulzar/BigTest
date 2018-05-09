package symexScala

import java.util.HashSet
import scala.collection.mutable.ArrayBuffer
import scala.reflect.runtime.universe._

object ComparisonOp extends Enumeration {
  type ComparisonOp = Value
  val Equality = Value("=")
  val Inequality = Value("!=")
  val LessThan = Value("<")
  val LessThanOrEq = Value("<=")
  val GreaterThan = Value(">")
  val GreaterThanOrEq = Value(">=")
  val Equals = Value("equals")
  val Notequals = Value("notequals")
  val isIn = Value("isIn")
  val isNotIn = Value("isNotIn")

  //def isComparisonOp(s: String): Boolean = values.exists(_.toString == s)
}

object UniaryOp extends Enumeration {
  type UniaryOp = Value
  val IsInteger = Value("isinteger")
  val NotInteger = Value("notinteger")
}

import ComparisonOp._
import UniaryOp._
import gov.nasa.jpf.symbc.string.SymbolicCharAtInteger

class Constraint(c: Array[Clause]) {
  var clauses: Array[Clause] = c //there are (implicit) conjunctions among elements of array (clauses)

  def this() {
    this(new Array[Clause](0))
  }

  def replace(thisVar: SymVar, other: SymVar): Constraint = {
    val replacedArray = clauses.map(_.replace(thisVar, other))
    new Constraint(replacedArray)
  }

  def addSuffix(sfx: String): Constraint = {
    val replacedArray = clauses.map(_.addSuffix(sfx))
    new Constraint(replacedArray)
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
  def toZ3Query(initials: Z3QueryState): String = {
    if (clauses.length == 0)
      return ""
    if (clauses.length == 1) {
      return s"""(assert ${andClauses(0, initials)} )"""
    }
    val idx = 0
    //s"""(assert (${andClauses(idx , initials)}) )"""
    s"""(assert ${andClauses(idx, initials)} )"""
  }

  def andClauses(idx: Int, initials: Z3QueryState): String = {
    if (idx == clauses.length - 1) {
      clauses(idx).toZ3Query(initials)
    } else {
      s""" (and ${clauses(idx).toZ3Query(initials)} ${andClauses(idx + 1,
                                                                 initials)} )"""
    }
  }

  override def equals(other: Any): Boolean = {
    if (other != null && other.isInstanceOf[Constraint]) {
      this.clauses.deep == other.asInstanceOf[Constraint].clauses.deep
    } else false
  }

  def conjunctWith(other: Constraint) = {
    //TODO: might want to simplify before merging, in case there are inconsistent clauses or repetitive ones
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
    this.clauses
      .copyToArray(newArray) //TODO TEST: might shallow copying the clauses
    new Constraint(newArray)
  }
}
class UniaryClause(left: Expr, op: UniaryOp) extends Clause(left, null, null) {

  override def toString: String = {
    if (op == null) leftExpr.toString
    else leftExpr.toString + " " + op
  }
  override def toZ3Query(initials: Z3QueryState): String = {
    var isString = false;
    if (leftExpr.isInstanceOf[StringExpr]) {
      isString = true;
    }

    var leftstr = leftExpr.toZ3Query(initials)
    try {
      if (leftExpr.isInstanceOf[ConcreteValue] && isString) {
        leftstr = leftstr.toInt.toChar.toString()
        leftstr = s""" "${leftstr}" """
      }
    } catch {
      case e: Exception =>
    }

    //  if(op == UniaryOp.IsInteger){
    //     val gen_name = leftstr.replaceAll("[^A-Za-z0-9]","") + "i";
    //     initials.init.add((gen_name , Numeric(NumericUnderlyingType._Int)))
    //     initials.replacements(gen_name) = "\\Q( str.to.int  "+leftstr+"  )\\E" //( str.to.int  line5  )
    //     return s"""(= (int.to.str ${gen_name}) ${leftstr} )"""
    //  }
    return s"""(${op.toString()}  ${leftstr} )"""

  }
  override def applyEffect(x: SymVar, effect: Expr): Clause = {
    val newLeftExpr = leftExpr.applyEffect(x, effect)
    new UniaryClause(newLeftExpr, op)
  }

  override def checkValidity(ss: SymbolicState): Boolean = {
    var leftRes = leftExpr.checkValidity(ss)
    leftRes
  }
  
   override def addSuffix(sfx: String): Clause = {
      new UniaryClause(left.addSuffix(sfx), op)
  }
}
class Clause(left: Expr, op: ComparisonOp = null, right: Expr = null) {
  var leftExpr: Expr = left
  val compOp: ComparisonOp = op
  var rightExpr: Expr = right
  assert(left != null)

  override def toString: String = {
    if (compOp == null || rightExpr == null) leftExpr.toString
    else leftExpr.toString + " " + compOp.toString + " " + rightExpr.toString
  }

  def toZ3Query(initials: Z3QueryState): String = {
    var isString = false;
    if (leftExpr.actualType == NonNumeric(NonNumericUnderlyingType._String) || right.actualType == NonNumericUnderlyingType._String) {
      isString = true;
    }

    var leftstr = leftExpr.toZ3Query(initials)
    var rightstr = rightExpr.toZ3Query(initials)
    try {
      if (leftExpr.isInstanceOf[ConcreteValue] && isString) {
        leftstr = leftstr.toInt.toChar.toString()
        leftstr = s""" "${leftstr}" """
      } else if (rightExpr.isInstanceOf[ConcreteValue] && isString) {
        rightstr = rightstr.toInt.toChar.toString()
        rightstr = s""" "${rightstr}" """

      }
    } catch {
      case e: Exception =>
    }

    if (compOp == null || rightExpr == null)
      leftExpr.toString
    else {

      if (compOp == Notequals || compOp == Inequality) {
        return s""" (not (=  ${leftstr} ${rightstr} ))"""
      } else {
        //Z3 -- > Assertion (assert (> x 2))
        //  if(leftExpr.isInstanceOf[Terminal] && rightExpr.isInstanceOf[Terminal])
        return s"""(${if (compOp == Notequals || compOp == Equals) {
          "="
        } else {
          compOp.toString()
        }}  ${leftstr} ${rightstr} )"""
      }
    }
  }
  override def equals(other: Any): Boolean = {
    if (other != null && other.isInstanceOf[Clause]) {
      this.toString == other.asInstanceOf[Clause].toString
    } else false
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
  def replace(thisVar: SymVar, other: SymVar): Clause = {
    if (rightExpr != null)
      new Clause(leftExpr.replace(thisVar, other),
                 compOp,
                 rightExpr.replace(thisVar, other))
    else new Clause(leftExpr.replace(thisVar, other))
  }

  def addSuffix(sfx: String): Clause = {
    if (rightExpr != null)
      new Clause(leftExpr.addSuffix(sfx), compOp, rightExpr.addSuffix(sfx))
    else new Clause(leftExpr.addSuffix(sfx))
  }
}
