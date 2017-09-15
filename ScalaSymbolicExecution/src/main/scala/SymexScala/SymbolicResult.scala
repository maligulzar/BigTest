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
        //terminating path is null now -> "false"
        this(ss, new Array[PathAndEffect](1))
        paths(0) = new PathAndEffect(Constraint.parseConstraint("true"))
    }

    def numOfPaths: Int = {paths.size}

    def numOfTerminating: Int = {terminating.size}

    def map(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        //returns Cartesian product of already existing paths *  set of paths from given udf
        val product = new Array[PathAndEffect](paths.size * udfSymbolicResult.numOfPaths)
        var i = 0  
        for(pa <- paths) {
            for(udfPath <- udfSymbolicResult.paths) {
                product(i) = udfPath.conjunctedTo(pa)
                i += 1
            }
        }
        new SymbolicResult(this.state, product, this.terminating)
    }

    def filter(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        // println(udfSymbolicResult)
        // println("------------------------------")
        val product = new ArrayBuffer[PathAndEffect]()
        val terminatingPaths = new ArrayBuffer[TerminatingPath]()
        if(this.terminating != null) {
            terminatingPaths ++= this.terminating
        }

        for(udfPath: PathAndEffect <- udfSymbolicResult.paths) {
            //we need to check the effect to see whether it is a terminating or a non-terminating one
            if(udfPath.effect._2.toString == "0") { //terminating
                val udfTerminating = new TerminatingPath(udfPath.pathConstraint)
                for(pa <- this.paths) {
                    // print(pa.toString+" && "+udfTerminating.toString+" = ")
                    val conjuncted = udfTerminating.conjunctedTo(pa)
                    // println("conjuncted "+conjuncted)
                    terminatingPaths += conjuncted
                }

            } else {
                for(pa <- this.paths) {
                    product += udfPath.conjunctedTo(pa)
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

class PathAndEffect(pc: Constraint, udfEffect: Tuple2[SymVar, Expr]) {
    var pathConstraint: Constraint = pc
    var effect: Tuple2[SymVar, Expr] = udfEffect

    def this(c: Constraint) {
        this(c, null) //no effects on variables
    }

    override def toString: String = {
        var e: String = ""
        var rName: String = ""
        if(effect == null) {
            e = "x"
            rName = "x"
        }
        else {
            e = /*effect._1.getName+" -> "+*/effect._2.toString
            rName = effect._1.getName
        }
        "path constraint: {"+pathConstraint.toString+"} effect: {"+e+" | for all "+rName+" member of V, pathConstraint("+rName+")} ---------"
    }

    def conjunctedTo(old: PathAndEffect): PathAndEffect = {
        //reflect previous effect into coming path constraint variables
        val toBeAdded: PathAndEffect = 
            if(old.effect != null) {
                this.applyEffect(old.effect._1, old.effect._2)
            } else this

        val newPathConstraint = toBeAdded.pathConstraint.conjunctWith(old.pathConstraint)
        new PathAndEffect(newPathConstraint, this.effect)
    }

    def applyEffect(x: SymVar, lastEffect: Expr): PathAndEffect = {
        val newPathConstraint: Constraint = this.pathConstraint.applyEffect(x, lastEffect)
        val newEffect: Tuple2[SymVar, Expr] = 
            if(this.effect != null) {
                (this.effect._1, this.effect._2.applyEffect(x, lastEffect))
            } else null
        new PathAndEffect(newPathConstraint, newEffect)
    }

    def checkValidity(ss: SymbolicState): Boolean = {
        var result = this.pathConstraint.checkValidity(ss)
        if(effect != null) result &= effect._2.checkValidity(ss)
        result
    }

}

case class TerminatingPath(c: Constraint) extends PathAndEffect(c) {
    
    override def toString: String = {
        "path constraint: {"+pathConstraint.toString+"} ----------------"
    }

    override def conjunctedTo(old: PathAndEffect): TerminatingPath = {
        //reflect previous effect into coming path constraint variables
        val toBeAdded: PathAndEffect = 
            if(old.effect != null) {
                this.applyEffect(old.effect._1, old.effect._2)
            } else this

        val newPathConstraint = toBeAdded.pathConstraint.conjunctWith(old.pathConstraint)
        new TerminatingPath(newPathConstraint)
    }

    //TODO:
    // override def applyEffect(x: SymVar, effect: Expr) = {
    //     this.pathConstraint.applyEffect(x, effect)
    // }

    override def checkValidity(ss: SymbolicState): Boolean = {
        this.pathConstraint.checkValidity(ss)
    }

} 

