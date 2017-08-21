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

class SetOfConstraints(V: RDD[Int], ps: Array[PathConstraint]) { // C(V)
    val dataset: RDD[Int] = V

    //different paths each being satisfied by an equivalent class of tuples in dataset V
    val paths: Array[PathConstraint] = ps 

    override def toString: String = {
        var result = "Set of Constraints for this dataset V:"+"\n"
        paths.foreach(result += _.toString+"\n")
        result
    }

    def this(V: RDD[Int]) {
        this(V, new Array[PathConstraint](1))
        //TODO: define identity as singleton
        val identity = new Function1[Int, Int] {
            def apply(x: Int): Int = x
        }
        paths(0) = new PathConstraint(V, Conjunction.parseConjunction("true"), identity)
    }

    def map(f: Function1[Int, Int], pathsOfUDF: Array[Conjunction]): SetOfConstraints = {
        //returns Cartesian product of already existing paths *  set of paths from given udf
        val product = new Array[PathConstraint](paths.size * pathsOfUDF.size)
        var i = 0  
        for(pa <- paths) {
            for(udfC <- pathsOfUDF) {
                //TODO: decide to restrict dataset to only parts of the data which satisfies the constraint either here
                // or later in the PathConstraint constructor
                //TODO*: take care of dataset argument according to below comment
                product(i) = new PathConstraint(dataset, pa.pc.conjunctWith(udfC), f)
                i += 1
            }
        }
        //*TODO: this affected dataset should be consistent with the dataset passed to each of product PathConstraint members!!
        // val affected = dataset.map(x => f(x))
        new SetOfConstraints(dataset, product)
    }

    //TODO: define filter, reduce API which will returns a new SetOfConstraints object as a result of operation

    def filter(f: Function1[Int, Boolean]): SetOfConstraints = {
        val product = new Array[PathConstraint](paths.size * 2)
        var i = 0  
        for(pa <- paths) {
            val extraConj = Conjunction.parseConjunction("f(x) == true")
            product(i) = new PathConstraint(dataset, pa.pc.conjunctWith(extraConj), f)

            val extraNegConj = Conjunction.parseConjunction("f(x) == false")
            product(i+1) = new PathConstraint(dataset, pa.pc.conjunctWith(extraNegConj), f)
            i += 2
        }
        new SetOfConstraints(dataset, product)
    }
}

class PathConstraint(V: RDD[Int], c: Conjunction, f: Function1[Int, _]) {
    val dataset: RDD[Int] = V
    val pc: Conjunction = c
    val effect: Function1[Int, _] = f

    override def toString: String = {
        // "f = "+effect.toString+"\n"+
        "pc = "+pc.toString+"\n"+"{f(v) | for all v member of V, pc(v)}\n"+"--------------------"
    }

    //Assuming that isSatisfied is called before getEffect on the record 
    // def apply(record: Int): _ = {
    //     effect.apply(record)
    // }

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
