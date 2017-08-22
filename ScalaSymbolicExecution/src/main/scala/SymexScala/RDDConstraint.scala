package SymexScala

import org.apache.spark.rdd._

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

class SetOfConstraints(ps: Array[PathConstraint]) { // C(V)
    //different paths each being satisfied by an equivalent class of tuples in dataset V
    val paths: Array[PathConstraint] = ps 

    override def toString: String = {
        var result = "Set of Constraints for this dataset V:"+"\n"
        paths.foreach(result += _.toString+"\n")
        result
    }

    def this() {
        this(new Array[PathConstraint](1))
        
        // val identity = new Function1[Int, Int] {
        //     def apply(x: Int): Int = x
        // }
        paths(0) = new PathConstraint(Conjunction.parseConjunction("true"), new Array[Tuple2[SymVar, Expr]](0))
    }

    def map(pathsOfUDF: Array[PathConstraint]): SetOfConstraints = {
        val state: SymbolicState = new SymbolicState(this)
        //returns Cartesian product of already existing paths *  set of paths from given udf
        val product = new Array[PathConstraint](paths.size * pathsOfUDF.size)
        var i = 0  
        for(pa <- paths) {
            for(udfC <- pathsOfUDF) {
                product(i) = pa.conjunctWith(udfC)
                i += 1
            }
        }
        new SetOfConstraints(product)
    }

    //TODO: later I have to generalize this API more so as to instead of taking a PathConstraint,
    //it would take a function(f) of Any to Boolean and creates a path consisting of f(x) == true as its constraint and identity as its effect
    // as well as another terminating path with f(x) != true as its constraint
    def filter(udfPath: PathConstraint): SetOfConstraints = {
        val product = new Array[PathConstraint](paths.size * 2)
        var i = 0
        for(pa <- paths) {
            //val extraConj = Conjunction.parseConjunction("f(x) == true")
            product(i) = pa.conjunctWith(udfPath)

            // val extraNegConj = Conjunction.parseConjunction("f(x) == false")
            // product(i+1) = new PathConstraint(pa.pc.conjunctWith(extraNegConj))
            i += 2
        }
        new SetOfConstraints(product)
    }
}

class PathConstraint(c: Conjunction, udfEffect: Array[Tuple2[SymVar, Expr]]) {
    var pc: Conjunction = c
    var effect: Array[Tuple2[SymVar, Expr]] = udfEffect

    override def toString: String = {
        //TODO: reflect effect for different variables not only return variables
        // "f = "+effect.toString+"\n"+
        "pc = "+pc.toString+"\n"+"{f(v) | for all v member of V, pc(v)}\n"+"--------------------"
    }

    def conjunctWith(other: PathConstraint): PathConstraint = {
        for(e <- effect) { //reflect each previous effect into coming path constraint variables
            other.replace(e._1, e._2)
        }
        other
    }

    def replace(x: SymVar, updated: Expr) = {
        this.pc.replace(x, updated)
        effect = effect.map(e => (e._1, e._2.replace(x, updated)))
    }

    def checkValidity(ss: SymbolicState): Boolean = {
        var result = this.pc.checkValidity(ss)
        for(e <- effect) result &= e._2.checkValidity(ss)
        result
    }

}


// case class FilterPathConstraint(C: Array[PathConstraint], udfConstraint: Constraint) extends PathConstraint {
//     override def toString: String = {
//         "for all records (ta) in A, such that Pa is a member of C(A) where Pa(ta) && " + udfConstraint.toString+"""
//          V
//          for all records(ta) in A, such that Pa is a member of C(A) where Pa(ta) && ~(""" + udfConstraint.toString + ") && Terminating"
//     }

//     def apply(record: Int): TriState = {
//         for(pa <- C) {
//             if(pa.apply(record).toBoolean) {
//                 if(udfConstraint.apply(record)) return new TriState("true")
//                 else return new TriState("terminating")
//             }
//         }
//         throw new NotFoundPathCondition(record.toString)
//     }
// }
