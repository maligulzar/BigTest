package SymexScala

import scala.collection.mutable.ArrayBuffer

class NotFoundPathCondition(message: String, cause: Throwable = null) 
    extends RuntimeException("Not found Pa in C(A) for record "+message, cause) {}


/* 
    paths = different paths each being satisfied by an equivalent class of tuples in dataset V
*/
class SymbolicResult(ss: SymbolicState, nonT: Array[PathAndEffect], t: ArrayBuffer[TerminatingPath] = null) {
    val state: SymbolicState = ss
    val paths: Array[PathAndEffect] = nonT
    val terminating: ArrayBuffer[TerminatingPath] = t

    override def toString: String = {
        var result = "Set of Constraints for this dataset V:\nNon-terminating:\n"
        paths.foreach(result += _.toString+"\n")

        if(terminating != null) {
            result += "terminating:\n"
            terminating.foreach(result += _.toString+"\n")
        }

        result
    }

    def this(ss: SymbolicState) {
        this(ss, new Array[PathAndEffect](1)) //terminating path is null now -> "false" maybe?
        paths(0) = new PathAndEffect(new Constraint()) //true
    }

    def numOfPaths: Int = {paths.size}

    def numOfTerminating: Int = {terminating.size}

    def map(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        //returns Cartesian product of already existing paths *  set of paths from given udf
        val product = new Array[PathAndEffect](paths.size * udfSymbolicResult.numOfPaths)
        var i = 0  
        for(pa <- paths) {
            for(udfPath <- udfSymbolicResult.paths) {
                product(i) = udfPath.conjunctPathEffect(pa)
                i += 1
            }
        }
        new SymbolicResult(this.state, product, this.terminating)
    }

    def filter(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        val product = new ArrayBuffer[PathAndEffect]()
        val terminatingPaths = new ArrayBuffer[TerminatingPath]()
        if(this.terminating != null) {
            terminatingPaths ++= this.terminating
        }

        for(udfPath: PathAndEffect <- udfSymbolicResult.paths) {
            //we need to check the effect to see whether it is a terminating or a non-terminating one
            if(udfPath.effect._2.last.toString == "0") { //terminating
                val udfTerminating = new TerminatingPath(udfPath.pathConstraint, null)
                for(pa <- this.paths) {
                    // print(pa.toString+" && "+udfTerminating.toString+" = ")
                    val conjuncted = udfTerminating.conjunctPathEffect(pa)
                    terminatingPaths += conjuncted
                }

            } else {
                val removedEffect = new PathAndEffect(udfPath.pathConstraint.deepCopy, null)
                for(pa <- this.paths) {
                    product += removedEffect.conjunctPathEffect(pa)
                }
            }
        }

        new SymbolicResult(this.state, product.toArray, terminatingPaths)
    }

    override def equals(other: Any): Boolean = {
        if(other != null && other.isInstanceOf[SymbolicResult]) {
            val castedOther = other.asInstanceOf[SymbolicResult]
            castedOther.numOfPaths == this.numOfPaths
        } else false
    } 
}

class PathAndEffect(pc: Constraint, udfEffect: Tuple2[SymVar, ArrayBuffer[Expr]]) {
    var pathConstraint: Constraint = pc
    var effect: Tuple2[SymVar, ArrayBuffer[Expr]] = udfEffect

    def this(c: Constraint) {
        this(c, null) //no effects on variables
    }

    override def toString: String = {
        var eString: String = ""
        var rName: String = ""
        if(effect == null) {
            eString = ""
            rName = "x"
        }
        else {
            for(e <- effect._2) {
                eString += effect._1.getName+" = "+e+", "
            }
            if(effect._2.size > 0) eString = eString.substring(0, eString.length-2)

            rName = effect._1.getName
        }
        "path constraint: {"+pathConstraint.toString+"}\t effect: {"+eString+"} ---------"
        //+" | for all "+rName+" member of V, pathConstraint("+rName+")} ---------"
    }

    /*
        reflect last previous effect on the incoming path constraint variables
        and update effect array
    */
    def conjunctPathEffect(prev: PathAndEffect): PathAndEffect = {
        val newPathEffect: PathAndEffect = 
            if(prev.effect != null) {
                this.applyLastEffect(prev.effect._1, prev.effect._2.last)
            }
            else {
                this.deepCopy
            }
        newPathEffect.pathConstraint.conjunctWith(prev.pathConstraint)

        //updates the effects buffer
        if(prev.effect != null && newPathEffect.effect != null) {
            val prepended = prev.effect._2 ++ newPathEffect.effect._2
            newPathEffect.effect = (newPathEffect.effect._1, prepended)
        }
        else if(prev.effect != null && newPathEffect.effect == null) {
            //deep-copy of prev.effect
            val newBuffer = new ArrayBuffer[Expr]
            prev.effect._2.copyToBuffer(newBuffer)
            newPathEffect.effect = (prev.effect._1, newBuffer)
        } 
        //else if prev.effect == null -> newPathEffect.effect would be the same as the result of applyLastEffect on this.effect     
        newPathEffect
    }

    def deepCopy: PathAndEffect = {
        val effectCopy: Tuple2[SymVar, ArrayBuffer[Expr]] = 
            if(this.effect != null) {
                val newBuffer = new ArrayBuffer[Expr]
                this.effect._2.copyToBuffer(newBuffer)
                (this.effect._1, newBuffer)
            } else null

        new PathAndEffect(this.pathConstraint.deepCopy, effectCopy)
    }

    /*
        returns a new instance of PathAndEffect 
        by applying the given effect on to (this) instance's path condition and effects
        this instance should be modified
    */
    def applyLastEffect(x: SymVar, lastEffect: Expr): PathAndEffect = {
        val newPathConstraint: Constraint = this.pathConstraint.applyEffect(x, lastEffect)
        val newEffect: Tuple2[SymVar, ArrayBuffer[Expr]] = 
            if(this.effect != null) {
                val newEffectArray = this.effect._2.map(_.applyEffect(x, lastEffect))
                (this.effect._1, newEffectArray)
            } else null
        new PathAndEffect(newPathConstraint, newEffect)
    }

    def checkValidity(ss: SymbolicState): Boolean = {
        var result = this.pathConstraint.checkValidity(ss)
        if(effect != null) {
            effect._2.foreach(effect => result &= effect.checkValidity(ss))
        }
        result
    }

}

case class TerminatingPath(c: Constraint, u: Tuple2[SymVar, ArrayBuffer[Expr]]) extends PathAndEffect(c, u) {
    
    // override def toString: String = {
    //     "path constraint: {"+pathConstraint.toString+"} ----------------"
    // }

    /*
        reflect last previous effect on the incoming path constraint variables
    */
    override def conjunctPathEffect(prev: PathAndEffect): TerminatingPath = {
        val newPathEffect: PathAndEffect = 
            if(prev.effect != null) {
                this.applyLastEffect(prev.effect._1, prev.effect._2.last)
            }
            else {
                this.deepCopy
            }
        newPathEffect.pathConstraint.conjunctWith(prev.pathConstraint)

        if(prev.effect != null) {
            //deep-copy of prev.effect
            val newBuffer = new ArrayBuffer[Expr]
            prev.effect._2.copyToBuffer(newBuffer)
            newPathEffect.effect = (prev.effect._1, newBuffer)
        }
        new TerminatingPath(newPathEffect.pathConstraint, newPathEffect.effect)
    }

    //TODO:
    // override def applyEffect(x: SymVar, effect: Expr) = {
    //     this.pathConstraint.applyEffect(x, effect)
    // }

    override def checkValidity(ss: SymbolicState): Boolean = {
        this.pathConstraint.checkValidity(ss)
    }

} 

