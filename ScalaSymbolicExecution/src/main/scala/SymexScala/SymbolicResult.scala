package SymexScala

class NotFoundPathCondition(message: String, cause: Throwable = null) 
    extends RuntimeException("Not found Pa in C(A) for record "+message, cause) {}

class TriState(s: String) {

    var state: String = {
        if(s.toLowerCase == "terminating") "Terminating"
        else if (s.toLowerCase == "true") "True"
        else "False"
    }

    def toBoolean: Boolean = {state == "True"} //or else that is Terminating or False

    override def toString: String = {state}
}

class SymbolicResult(ps: Array[PathAndEffect]) {
    //different paths each being satisfied by an equivalent class of tuples in dataset V
    val paths: Array[PathAndEffect] = ps
    var terminating: Array[TerminatingPath] = null

    override def toString: String = {
        var result = "Set of Constraints for this dataset V:"+"\n"
        paths.foreach(result += _.toString+"\n")
        result
    }

    def this() {
        this(new Array[PathAndEffect](1))
        paths(0) = new PathAndEffect(Constraint.parseConstraint("true"))
    }

    def this(nonT: Array[PathAndEffect], t: Array[TerminatingPath]) {
        this(nonT)
        this.terminating = t
    }

    def numOfPaths: Int = {paths.size}

    def numOfTerminating: Int = {terminating.size}

    def map(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        //val state: SymbolicState = new SymbolicState(this)
        //returns Cartesian product of already existing paths *  set of paths from given udf
        val product = new Array[PathAndEffect](paths.size * udfSymbolicResult.numOfPaths)
        var i = 0  
        for(pa <- paths) {
            for(udfPath <- udfSymbolicResult.paths) {
                product(i) = pa.conjunctWith(udfPath)
                i += 1
            }
        }
        new SymbolicResult(product)
    }

    //TODO: later I have to generalize this API more so as to instead of taking a PathAndEffect,
    //it would take a function(f) of Any to Boolean and creates a path consisting of f(x) == true as its constraint and identity as its effect
    // as well as another terminating path with f(x) != true as its constraint
    def filter(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        val product = new Array[PathAndEffect](paths.size * udfSymbolicResult.numOfPaths)
        var i = 0
        for(pa <- paths) {
            for(udfPath <- udfSymbolicResult.paths) {
                //val extraConj = Constraint.parseConstraint("f(x) == true")
                product(i) = pa.conjunctWith(udfPath)
                i += 1
            }
        }

        new SymbolicResult(product)
    }

    override def equals(other: Any): Boolean = {
        if(other != null && other.isInstanceOf[SymbolicResult]) {
            val castedOther = other.asInstanceOf[SymbolicResult]
            castedOther.numOfPaths == this.numOfPaths
        } else false
    } 
}

class PathAndEffect(c: Constraint, udfEffect: Tuple2[SymVar, Expr]) {
    var pc: Constraint = c
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
        "pc: {"+pc.toString+"}\n "+"effect: {"+e+" | for all "+rName+" member of V, pc("+rName+")} ---------\n"
    }

    def conjunctWith(other: PathAndEffect): PathAndEffect = {
        //reflect previous effect into coming path constraint variables
        if(effect != null) other.replace(effect._1, effect._2)
        other
    }

    def replace(x: SymVar, updated: Expr) = {
        this.pc.replace(x, updated)
        if(effect != null) effect = (effect._1, effect._2.replace(x, updated))
    }

    def checkValidity(ss: SymbolicState): Boolean = {
        var result = this.pc.checkValidity(ss)
        if(effect != null) result &= effect._2.checkValidity(ss)
        result
    }

}

case class TerminatingPath(c: Constraint) extends PathAndEffect(c) {
    
    override def toString: String = {
        "pc = "+pc.toString+"\n"+"{terminating | for all v member of V, pc(v)}\n"+"--------------------"
    }

    override def replace(x: SymVar, updated: Expr) = {
        this.pc.replace(x, updated)
    }

    override def checkValidity(ss: SymbolicState): Boolean = {
        this.pc.checkValidity(ss)
    }

} 

