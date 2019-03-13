package SymexScala

import java.util
import java.util.HashSet

import scala.collection.JavaConverters._

object ComparisonOp extends Enumeration {
    type ComparisonOp = Value
    val Equality = Value("=")
    val Inequality = Value("!=")
    val LessThan = Value("<")
    val LessThanOrEq = Value("<=")
    val GreaterThan = Value(">")
    val GreaterThanOrEq = Value(">=")

    implicit class ComparisonOpPythonStr(op: ComparisonOp) {
        def toPythonComparison: String = {
            if(op == Equality) "==" else op.toString
        }
    }
    
    //def isComparisonOp(s: String): Boolean = values.exists(_.toString == s)
}

import SymexScala.ComparisonOp._

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
    
    def toZ3Query(initials: HashSet[(String , VType)]): String = {
        if (clauses.length == 0)
            return ""
        // jteoh: example usage of convertClausesToString, but original implementation continues to
        // be in use just to be safe.
        // s""" (assert (${convertClausesToString(initials, _.toZ3Query, _.mkString(" and "))}"""
        val idx = 0
        s""" (assert (${andClauses(idx , initials)}) )"""
        
    }
    
    /**
     * Produces a python lambda definition that evaluates the current constraint for its given
     * inputs (named according to `initials`) and returns a boolean value of satisfaction.
     *
     * Later implementation note: In python, there's argument expansion such that you could pass
     * in a collection of input arguments as a single list. e.g.:
     * f = lambda a, b: a >= b
     * f_args = [3, 2]
     * f(*f_args) # returns True
     * @param initials Set of names (and data types) that will act as inputs for the returned
     *                 Python function.
     * @return
     */
    def toPythonFunction(initials: HashSet[(String , VType)] = new util.HashSet[(String, VType)]()): String = {
        if (clauses.isEmpty)
            return "lambda: True"
        // note: initials is populated as part of the conversion to Python function def. As such,
        // inputNames should only be determined after the 'body'.
        // Maybe this should be an earlier preprocessing step somewhere?
        val body = convertClausesToString(initials, _.toPythonClause, _.mkString(" and "))
        val inputNames = initials.iterator().asScala.map(_._1)
        s"""lambda ${inputNames.mkString(", ")}: $body"""
    }
    
    /**
     * Combines this constraint's clauses using the provided initials, strConverter (e.g.
     * toZ3Query or toPythonFunction), and clauseJoiner (e.g., joining with " and ").
     *
     * This can be used as an alternative to @andClauses, as it is also more general (though not
     * recursive, if implementation is a concern).
     */
    private def convertClausesToString(initials: HashSet[(String , VType)],
                                       strConverter: Clause =>
                                         (HashSet[(String, VType)] => String) = _.toZ3Query,
                                       clauseJoiner: Array[String] => String = _.mkString(" ")
                                      ): String = {
        clauseJoiner(clauses.map(strConverter(_)(initials)))
    }
    
    def andClauses(idx :Int , initials: HashSet[(String , VType)]): String ={
        if(idx == clauses.length -1){
            clauses(idx).toZ3Query(initials)
        }else{
            s""" and ${(clauses(idx).toZ3Query(initials))} ${andClauses(idx+1 , initials)} """
        }
    }

    override def equals(other: Any): Boolean = {
        if(other != null && other.isInstanceOf[Constraint]) {
            this.clauses.deep == other.asInstanceOf[Constraint].clauses.deep
        }
        else false
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
        this.clauses.copyToArray(newArray) //TODO TEST: might shallow copying the clauses
        new Constraint(newArray)
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

    def toZ3Query(initials: HashSet[(String , VType)]): String = {
        if (compOp == null || rightExpr == null)
            leftExpr.toString
        else
        {
            // prefix/polish notation
            //Z3 -- > Assertion (assert (> x 2))
            //  if(leftExpr.isInstanceOf[Terminal] && rightExpr.isInstanceOf[Terminal])
            return s"""(${compOp.toString}  ${leftExpr.toZ3Query(initials)} ${rightExpr.toZ3Query(initials)} )"""
        }
        ""
    }
    
    def toPythonClause(initials: HashSet[(String , VType)]): String = {
        if (compOp == null || rightExpr == null)
            leftExpr.toString
        else
        {
            // infix notation for python functions.
            // This currently assumes that ComparisonOps convert directly to python-evaluable
            // strings.
            return s"(${leftExpr.toPythonExpr(initials)} ${compOp.toPythonComparison} ${rightExpr.toPythonExpr(initials)})"
        }
        ""
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
