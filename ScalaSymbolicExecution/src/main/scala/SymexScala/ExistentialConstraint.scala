package SymexScala

import ComparisonOp._
import NumericUnderlyingType._

//TODO: change base Constraint class to a clause and a list of (rest of) Constraints -> so as to have Existential Constraint nested
//E x such that x isAMemberOF SYM_A, or !E x such that x isAMemberOF SYM_A ->
class ExistentialConstraint(nextIndex: Int, isNonExis: Boolean = false, c: Array[Clause] = new Array[Clause](0)) extends Constraint(c) {
    //TODO: assumes type int for the existentialVar
    val existentialVar: SymVar = new SymVar(Numeric(_Int), "c"+nextIndex)
    

    def addCluase(other: Expr, op: ComparisonOp) = {
        clauses = new Clause(other, op, existentialVar) +: clauses
    }

    override def toString: String = {
        if (clauses.length == 0)
            return ""

        var result = ""
        if(isNonExis) result += "!"
        result += "E c"+nextIndex+": "
        result += clauses(0).toString
        for (i <- 1 to clauses.length - 1) {
            result += " && " + clauses(i)
        }
        result
    }

    //TODO:
    // override def toZ3Query(initials: HashSet[(String , VType)]): String = {

    // }

    override def deepCopy: ExistentialConstraint = {
        val newArray = new Array[Clause](this.clauses.size)
        this.clauses.copyToArray(newArray) //TODO TEST: might shallow copying the clauses
        new ExistentialConstraint(nextIndex, isNonExis, newArray)
    }
}