package symexScala

import scala.collection.mutable.ArrayBuffer
import java.util.HashSet
import scala.collection.mutable.HashMap

class PathEffect(pc: Constraint, udfEffect: ArrayBuffer[Tuple2[SymVar, Expr]]) {
  var pathConstraint: Constraint = pc

  //TODO: change it back to effects after handling Spark DAG
  var effects: ArrayBuffer[Tuple2[SymVar, Expr]] = udfEffect

  def this(c: Constraint) {
    this(c, new ArrayBuffer[Tuple2[SymVar, Expr]]()) //no effects on variables
  }

  override def toString: String = {
    var eString: String = ""
    for (ePair <- effects) {
      eString += ePair._1.getName + " = " + ePair._2.toString + ", "
    }
    if (effects.size > 0) eString = eString.substring(0, eString.length - 2)

    // if(pathConstraint.clauses.size > 1) {
    //     eString += " && x2 = x1"
    // }

    "path constraint: {" + pathConstraint.toString + "}\t effect: {" + eString + "} ---------"
  }

  def addEffect(_var: SymVar, updatedExpr: Expr): PathEffect = {
    effects += new Tuple2(_var, updatedExpr)
    this
  }

  def getEffectZ3Query(initial: Z3QueryState): String = {
    var eString: String = ""
    var rName: String = ""
    // val clauses: util.ArrayList[Clause] = new util.ArrayList[Clause]()
    val clauses: Array[Clause] = new Array[Clause](effects.size)
    var i = 0;
    for (e <- effects) {
      clauses(i) = new Clause(e._1, ComparisonOp.Equality, e._2)
      i = i + 1
    }
    val pathCond = new Constraint(clauses.toArray)
    return pathCond.toZ3Query(initial)
  }

  def generateSplitConstraints(state: Z3QueryState): String = {
    var s = ""
    for ((k, v) <- state.split) {
      val del = v.del
      val arr = v.str_arr
      val query = arr.reverse
        .map(s => if (s == null) "\" \"" else s)
        .reduce((a, b) => "(str.++ " + "(str.++ " + b + del + " )  " + a + ")")
      s = s + "\n" + s"""(assert (= ${k} ${query})) """
    }
    s
  }

//    def generateSplitConstraints(state: Z3QueryState ): String = {
//      var s = ""
//      //var buff = new ArrayBuffer[String]()
//      for( (k,v) <- state.split ){
//          val del = v.del
//          val arr = v.str_arr
//          val query  = arr.reverse.map(s=> if(s==null) "\" \"" else s).reduce((a,b) => "(str.++ " + "(str.++ " + b +del+" )  " + a +")")
//        //     arr.filter(s => s!=null).map( a => buff.append(a))
//      }
//
//
//      //    return buff.filter(s=>s!=null).reduce(_+"\n"+_)
//    }

  def toZ3Query(): String = {

    val list: HashSet[(String, VType)] = new HashSet[(String, VType)]();

    val split = new HashMap[String, SplitHandler]();
    val replace = new HashMap[String, String]();

    val state: Z3QueryState = Z3QueryState(list, split, replace)

    var pc = pathConstraint.toZ3Query(state) + "\n" + getEffectZ3Query(state)
    //fix the references

    // for((k,v) <- state.replacements){
    //  pc =  pc.replaceAll(v, k)
    // }

    var decls = s"""
          |(set-logic QF_ASNIA)
          |(set-option :produce-models true)
          |
          |
          |(define-fun isinteger ((x!1 String)) Bool
          |(or (str.in.re x!1 (  re.++ (str.to.re "-") (re.+ (re.range "0" "9")))) (str.in.re x!1 (re.+ (re.range "0" "9"))) )
          |)      
          |
          |(define-fun notinteger ((x!1 String)) Bool
          |(not (isinteger x!1))
          |)
          |
          |""".stripMargin
    val itr = state.init.iterator()
    while (itr.hasNext) {
      val i = itr.next()
      decls +=
        s"""(declare-fun ${i._1} () ${i._2.toZ3Query()})
                  |""".stripMargin
    }
    s"""$decls
           |${generateSplitConstraints(state)}
           |$pc
           |
           
     """.stripMargin //,generateSplitConstraints(state))
  }

  def processOutput(str: String) {
    val arr = str.split("\n")
    val var_map = HashMap[String, String]()
//      arr.map(s => s.split(":")).filter(s => s.length>0).map{
//        s =>
//          var_map(s(0)) = s(1)
//      ""}
  }

//    def generateFinalData(map: HashMap ): String = {
//      var s = ""
//      var buff = new ArrayBuffer[String]()
//      for( (k,v) <- state.split ){
//          val del = v.del
//          val arr = v.str_arr
//         // val query  = arr.reverse.map(s=> if(s==null) "\" \"" else s).reduce((a,b) => "(str.++ " + "(str.++ " + b +del+" )  " + a +")")
//             arr.filter(s => s!=null).map( a => buff.append(a))
//      }
//      return buff.filter(s=>s!=null).reduce(_+"\n"+_)
//    }
//
  override def equals(other: Any): Boolean = {
    if (other != null && other.isInstanceOf[PathEffect]) {
      val casted = other.asInstanceOf[PathEffect]
      casted.pathConstraint.equals(this.pathConstraint) && casted.effects
        .corresponds(this.effects)((a, b) => a._1.equals(b._1) && a._2.equals(b._2))
    } else false
  }

  /*
        conjuncts this(udf) PathEffect with already-existing rdd PathEffect
   */
  def conjunctPathEffect(rddPE: PathEffect, link: Tuple2[Array[SymVar], Array[SymVar]] = null): PathEffect = {
    val newEffects = new ArrayBuffer[Tuple2[SymVar, Expr]]()
    rddPE.effects.copyToBuffer(newEffects)

    //adds the link between previous symOutput to the incoming symInput
    if (link != null) {
      for (i <- 0 to link._2.length - 1) {
        var ar1 = link._1
        var ar2 = link._2
        newEffects += new Tuple2(ar1(i), ar2(i))
      }

    }
    newEffects.appendAll(this.effects)

    val newPathEffect =
      new PathEffect(rddPE.pathConstraint.deepCopy, newEffects)
    newPathEffect.pathConstraint.conjunctWith(this.pathConstraint)
    newPathEffect
  }

  def indexOutputArrayForFlatMap(output_name: String, indx: Int): PathEffect = {
    var j = 0
    val newEffects = new ArrayBuffer[Tuple2[SymVar, Expr]]()
    var ret: Tuple2[SymVar, Expr] = null
    for (e <- effects) {
      if (e._1.name.equals(output_name)) {
        e._2 match {
          case StringExpr(_, op, _) =>
            if (op.op == StringOp.Split) {
              val str_op = e._2.asInstanceOf[StringExpr]
              newEffects.append(
                  (e._1, new StringExpr(str_op.obj, new SymStringOp(op.actualType, StringOp.Splitn), Array(new ConcreteValue(Numeric(NumericUnderlyingType._Int), indx + "")) ++ str_op.opr)))
            } else {
              newEffects.append(e)
            }
          case _ =>
            println("Not a string expr")
            newEffects.append(e)
        }
      } else {
        newEffects.append(e)
      }
    }
    new PathEffect(pathConstraint, newEffects)

  }

  def addOneToN_Mapping(link: SymVar, arr: Array[Expr], pa2: PathEffect): PathEffect = {
    val newEffects = new ArrayBuffer[Tuple2[SymVar, Expr]]()
    if (link != null) {
      for (i <- 0 to arr.length - 1) {
        newEffects += new Tuple2(link.addSuffix("P" + (i + 1)), arr(i))
      }
    }

    for (e <- this.effects) {
      val newRHS: Expr = e._2.addSuffix("P1")
      val newLHS = e._1.addSuffix("P1")
      newEffects += new Tuple2(newLHS, newRHS)
    }
    for (e <- pa2.effects) {
      val newRHS: Expr = e._2.addSuffix("P2")
      val newLHS = e._1.addSuffix("P2")
      newEffects += new Tuple2(newLHS, newRHS)
    }
    val cons1 = this.pathConstraint.addSuffix("P1")
    val cons2 = pa2.pathConstraint.addSuffix("P2")
    new PathEffect(new Constraint(cons1.clauses ++ cons2.clauses), newEffects)
  }

  def deepCopy: PathEffect = {
    val effectsCopy = new ArrayBuffer[Tuple2[SymVar, Expr]]()
    if (this.effects.size != 0) {
      this.effects.copyToBuffer(effectsCopy)
    }
    new PathEffect(this.pathConstraint.deepCopy, effectsCopy)
  }

  //Shagha: Should return a new instance of PathEffect
  def replace(thisVar: SymVar, other: SymVar): PathEffect = {
    val effectsCopy = new ArrayBuffer[Tuple2[SymVar, Expr]]()
    for (e <- this.effects) {
      val newRHS: Expr = e._2.replace(thisVar, other)
      if (e._1.equals(thisVar)) {
        effectsCopy += new Tuple2(thisVar, newRHS)
      } else effectsCopy += new Tuple2(e._1, newRHS)
    }
    val replacedPath = this.pathConstraint.replace(thisVar, other)
    new PathEffect(replacedPath, effectsCopy)
  }

  def addSuffix(sfx: String): PathEffect = {
    val effectsCopy = new ArrayBuffer[Tuple2[SymVar, Expr]]()
    for (e <- this.effects) {
      val newRHS: Expr = e._2.addSuffix(sfx)
      val newLHS = e._1.addSuffix(sfx)
      effectsCopy += new Tuple2(newLHS, newRHS)
    }
    val replacedPath = this.pathConstraint.addSuffix(sfx)
    new PathEffect(replacedPath, effectsCopy)
  }
  /*
        returns a new instance of PathEffect
        by applying the given effect on to (this) instance's path condition and effects
        this instance should NOT be modified
   */
  /*
    def applyLastEffect(x: SymVar, lastEffect: Expr): PathEffect = {
        val newPathConstraint: Constraint = this.pathConstraint.applyEffect(x, lastEffect)
        val newEffect: Tuple2[SymVar, ArrayBuffer[Expr]] =
            if(this.effect != null) {
                val newEffectArray = this.effect._2.map(_.applyEffect(x, lastEffect))
                (this.effect._1, newEffectArray)
            } else null
        new PathEffect(newPathConstraint, newEffect)
    }
   */

  def checkValidity(ss: SymbolicState): Boolean = {
    var result = this.pathConstraint.checkValidity(ss)
    effects.foreach(effect => result &= effect._2.checkValidity(ss))

    result
  }

}

case class TerminatingPath(c: Constraint, u: ArrayBuffer[Tuple2[SymVar, Expr]]) extends PathEffect(c, u) {
  def this(c: Constraint) {
    this(c, new ArrayBuffer[Tuple2[SymVar, Expr]]()) //no effects on variables
  }
  /*
        conjuncts this(udf) PathEffect with already-existing rdd PathEffect
   */
  override def conjunctPathEffect(rddPE: PathEffect, link: Tuple2[Array[SymVar], Array[SymVar]] = null): TerminatingPath = {
    val newEffects = new ArrayBuffer[Tuple2[SymVar, Expr]]()
    rddPE.effects.copyToBuffer(newEffects)
    if (link != null) {
      for (i <- 0 to link._2.length - 1) {
        var ar1 = link._1
        var ar2 = link._2
        newEffects += new Tuple2(ar1(i), ar2(i))
      }

    }
    newEffects.appendAll(this.effects)

    val newPathEffect =
      new TerminatingPath(this.pathConstraint.deepCopy, newEffects)
    newPathEffect.pathConstraint.conjunctWith(rddPE.pathConstraint)
    newPathEffect
  }

  override def checkValidity(ss: SymbolicState): Boolean = {
    this.pathConstraint.checkValidity(ss)
  }

}

case class Z3QueryState(init: HashSet[(String, VType)], split: HashMap[String, SplitHandler], replacements: HashMap[String, String]) {

  def addtoInit(a: (String, VType)) {
    val itr = init.iterator()
    while (itr.hasNext) {
      val de = itr.next()
      if (a._1.equals(de._1)) {
        return
      }
    }
    init.add(a);

  }
}
case class SplitHandler(str_arr: Array[String], del: String)
/***
  *
  * (define-fun isinteger ((x!1 String)) Bool
(or (str.in.re x!1 (  re.++ (str.to.re "-") (re.+ (re.range "0" "9")))) (str.in.re x!1 (re.+ (re.range "0" "9"))) )
)
  *
  *
  * /
  */
