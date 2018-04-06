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
        for(ePair <- effects) {
            eString += ePair._1.getName+" = "+ePair._2.toString+", "
        }
        if(effects.size > 0) eString = eString.substring(0, eString.length-2)

        // if(pathConstraint.clauses.size > 1) {
        //     eString += " && x2 = x1"
        // }

        "path constraint: {"+pathConstraint.toString+"}\t effect: {"+eString+"} ---------"
    }

    def addEffect(_var: SymVar, updatedExpr: Expr) = {
        effects += new Tuple2(_var, updatedExpr)
    }


    def getEffectZ3Query(initial: Z3QueryState): String = {
        var eString: String = ""
        var rName: String = ""
        // val clauses: util.ArrayList[Clause] = new util.ArrayList[Clause]()
        val clauses: Array[Clause] = new Array[Clause](effects.size)
            var i =0 ;
            for (e <- effects) {
                clauses(i) = new Clause(e._1,
                    ComparisonOp.Equality,
                    e._2)
                i =  i + 1
            }
            val pathCond = new Constraint(clauses.toArray)
            return pathCond.toZ3Query(initial)
    }

    
    def generateSplitConstraints(state: Z3QueryState): String = {
      var s = ""
      for( (k,v) <- state.split ){
          val del = v.del
          val arr = v.str_arr
          val query  = arr.reverse.map(s=> if(s==null) "\"\"" else s).reduce((a,b) => "(str.++ " + "(str.++ " + b +del+" )  " + a +")")
         s = s  +"\n"+ s"""(assert (= ${k} ${query})) """
      }
      s
    }

    def toZ3Query(): String = {

        val list: HashSet[(String, VType)] = new HashSet[(String, VType)]();
        
        val split = new HashMap[String, SplitHandler]();
        val state : Z3QueryState = Z3QueryState(list, split)
        
        val pc = pathConstraint.toZ3Query(state) + "\n" + getEffectZ3Query(state)
        
        
        var decls = s"""
          |(define-fun isinteger ((x!1 String)) Bool
          |  (str.in.re x!1 (re.+ (re.range "0" "9")) )
          |)
          |
          |(define-fun notinteger ((x!1 String)) Bool
          |  (not (str.in.re x!1 (re.+ (re.range "0" "9")) ))
          |)
          |
          |""".stripMargin
        val itr = state.init.iterator()
        while(itr.hasNext){
            val i = itr.next()
            decls +=
              s"""(declare-fun ${i._1} () ${i._2.toZ3Query()})
                  |""".stripMargin
        }
        s"""$decls
           |${generateSplitConstraints(state)}
           |$pc
           |(check-sat)
           |(get-model)
     """.stripMargin
    }


    override def equals(other: Any): Boolean = {
        if(other != null && other.isInstanceOf[PathEffect]) {
            val casted = other.asInstanceOf[PathEffect]
            casted.pathConstraint.equals(this.pathConstraint) && casted.effects.corresponds(this.effects)((a, b) => a._1.equals(b._1) && a._2.equals(b._2))
        }
        else false
    }

    /*
        conjuncts this(udf) PathEffect with already-existing rdd PathEffect
    */
    def conjunctPathEffect(rddPE: PathEffect, link: Tuple2[SymVar, SymVar] = null): PathEffect = {
        val newEffects = new ArrayBuffer[Tuple2[SymVar, Expr]]() 
        rddPE.effects.copyToBuffer(newEffects)
        //adds the link between previous symOutput to the incoming symInput
        if(link != null) newEffects += link
        newEffects.appendAll(this.effects)

        val newPathEffect = new PathEffect(rddPE.pathConstraint.deepCopy, newEffects)
        newPathEffect.pathConstraint.conjunctWith(this.pathConstraint)
        newPathEffect
    }

    
    def deepCopy: PathEffect = {
        val effectsCopy = new ArrayBuffer[Tuple2[SymVar, Expr]]() 
            if(this.effects.size != 0) {
                this.effects.copyToBuffer(effectsCopy)
            }
        new PathEffect(this.pathConstraint.deepCopy, effectsCopy)
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
    override def conjunctPathEffect(rddPE: PathEffect, link: Tuple2[SymVar, SymVar] = null): TerminatingPath = {
        val newEffects = new ArrayBuffer[Tuple2[SymVar, Expr]]() 
        rddPE.effects.copyToBuffer(newEffects)
        if(link != null) newEffects += link
        newEffects.appendAll(this.effects)

        val newPathEffect = new TerminatingPath(this.pathConstraint.deepCopy, newEffects)
        newPathEffect.pathConstraint.conjunctWith(rddPE.pathConstraint)
        newPathEffect
    }

    override def checkValidity(ss: SymbolicState): Boolean = {
        this.pathConstraint.checkValidity(ss)
    }

} 

case class Z3QueryState(init: HashSet[(String, VType)] , split:HashMap[String, SplitHandler])
case class SplitHandler(str_arr:  Array[String] , del:String)



