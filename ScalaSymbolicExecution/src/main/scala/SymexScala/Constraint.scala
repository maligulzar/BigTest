package SymexScala

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

//Need to add Type which shows type of the variable this constraint applies to
class Constraint(str: String) {
    //there are (implicit) conjunctions between elements of array
    val strClauses = str.replaceAll("\\s", "").split("&&")
    val clauses: Array[Clause] = strClauses.map(str => parseClause(str))

    override def toString: String = {
        if(clauses.length == 0)
            return ""
        var result = clauses(0).toString
        for(i <- 1 to clauses.length-1) {
            result += " && "+clauses(i)
        }
        result
    }

    def parseClause(str: String): Clause = {
        val op = """<=|>=|==|!=|<|>""".r
        val matched = op.findAllIn(str).toArray
        if(matched.length > 1) {
            println("Parse Error: More than one comparison operator in one clause!")
            exit(1)
        } else if (matched.length == 0) {
            return new Clause(str)
        }

        val comp = ComparisonOp.withName(matched(0))
        val index = str.indexOf(matched(0))
        val leftStr = str.substring(0, index)
        val rightStr = str.substring(index + matched(0).length)

        return new Clause(leftStr, comp, rightStr)
    }

    def apply(record: Int): Boolean = {
        true //TODO: symbolic execution on udf
    }
}

//may need to convert each clause to a partial evaluation
class Clause (left: String, op: ComparisonOp = null, right: String = null) {

    var leftExpr: Expr = parseExpr(left)
    var compOp: ComparisonOp = op
    var rightExpr: Expr = if(right != null) parseExpr(right) else null

    override def toString: String = {
        if(compOp == null || rightExpr == null) leftExpr.toString
        else leftExpr.toString+" "+compOp.toString+" "+rightExpr.toString
    }

    def parseExpr(str: String): Expr = {
        //first check for partialExpr
        //TODO: remove () from beginning and end of an expr
        val op = """\+|-|\*|/""".r
        op.findFirstIn(str) match {
            case Some(matched) => {
                //ArithmeticOp(matched)
                val index = str.indexOf(matched)
                val left = str.substring(0, index)
                val right = str.substring(index + 1)
                return PartialExpr(parseExpr(left), ArithmeticOp.withName(matched), parseExpr(right))
            }
            case None => { //it did not contain any arithmetic operator
                try {
                    val parsed = Integer.parseInt(str)
                    return ConcreteInt(parsed)
                } catch {
                    case e: NumberFormatException => {
                        try { 
                            val bool = str.toBoolean
                            return ConcreteBoolean(bool)
                        } catch {
                            case e: Exception => {
                                return SymVar(str)
                            }
                        }
                    }
                }
            }
        }
    }
}

abstract class Expr {
    def toString: String
}

case class SymVar(name: String) extends Expr {
    //TODO: What else?
    override def toString: String = {"Sym_"+name}
}

case class ConcreteInt(value: Int) extends Expr {
    //TODO: Need to make it more generalized and include type information
    //for now, we only support Int
    override def toString: String = {value.toString}
}

case class ConcreteBoolean(value: Boolean) extends Expr {
    val literal: Boolean = value

    override def toString: String = {
        literal.toString
    }
}

case class PartialExpr(left: Expr, op: ArithmeticOp, right: Expr) extends Expr {
    //TODO: probably need to add simplify method later
    override def toString: String = {left.toString+" "+op.toString+" "+right.toString}
}

