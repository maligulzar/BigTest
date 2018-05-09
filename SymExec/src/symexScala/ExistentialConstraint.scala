package symexScala

import ComparisonOp._
import NumericUnderlyingType._

/* **NOTE**
 I am assuming that we HAVE ALREADY REPLACED A.Key or B.key (rhs of predicate) with the existential var in (rest: Constraint)
 */
class ExistentialConstraint(existentialVar: SymVar, rest: Array[Clause])
    extends Constraint(rest) {

  //similar to conjunctWith
  def addCluase(op: ComparisonOp, keySet: SymVar) = {
    clauses = new Clause(existentialVar, op, keySet) +: clauses
  }

  override def toString: String = {
    if (clauses.length == 0) return ""
    s"E ${existentialVar.getName}: ${clauses.mkString(" && ")}"
  }

  //TODO:
  // override def toZ3Query(initials: HashSet[(String , VType)]): String = {

  // }

  override def deepCopy: ExistentialConstraint = {
    val newArray = new Array[Clause](this.clauses.size)
    this.clauses
      .copyToArray(newArray) //TODO TEST: might shallow copying the clauses
    new ExistentialConstraint(existentialVar.deepCopy, newArray)
  }
}
