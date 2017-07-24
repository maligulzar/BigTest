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

class Constraint(str: String) {
    //there are (implicit) conjunctions between elements of array
    val strClauses = str.split("&&")
    val clauses: Array[Clause] = strClauses.map(str => new Clause(str))

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

class Clause(str: String) {

    var leftExpr: Expr = null
    var compOp: ComparisonOp = null
    var rightExpr: Expr = null
    parseClause(str)

    def parseClause(str: String) = {
        val op = """<=|>=|==|!=|<|>""".r
        val matched = op.findAllIn(str).toArray
        if(matched.length != 1) {
            println("Parse Error: More than one (or none) comparison operator in one clause!")
            exit(1)
        }

        this.compOp = ComparisonOp.withName(matched(0))
        val index = str.indexOf(matched(0))

        val left = str.substring(0, index)
        this.leftExpr = parseExpr(left)

        val right = str.substring(index + matched(0).length)
        this.rightExpr = parseExpr(right)
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
                    case e: NumberFormatException => return SymVar(str)
                }
            }
        }
    }

    override def toString: String = {
        leftExpr.toString+" "+compOp.toString+" "+rightExpr.toString
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

case class PartialExpr(left: Expr, op: ArithmeticOp, right: Expr) extends Expr {
    //TODO: probably need to add simplify method later
    override def toString: String = {left.toString+" "+op.toString+" "+right.toString}
}

