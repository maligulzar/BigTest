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

abstract class PathConstraint {
    def toString: String
    def apply(record: Int): TriState
}

case class MapPathConstraint(C: Array[PathConstraint], udfConstraint: Constraint) extends PathConstraint {
    override def toString: String = {
        "for all records(ta) in A, such that Pa is a member of C(A) where Pa(ta) && " + udfConstraint.toString
    }

    def apply(record: Int): TriState = {
        for(pa <- C) {
            //Pa(ta) ^ f(ta)
            if(pa.apply(record).toBoolean) return new TriState(udfConstraint.apply(record).toString)
        }
        //no pA found for particular record
        throw new NotFoundPathCondition(record.toString)
    }
    
}


case class FilterPathConstraint(C: Array[PathConstraint], udfConstraint: Constraint) extends PathConstraint {
    override def toString: String = {
        "for all records (ta) in A, such that Pa is a member of C(A) where Pa(ta) && " + udfConstraint.toString+"""
         V
         for all records(ta) in A, such that Pa is a member of C(A) where Pa(ta) && ~(""" + udfConstraint.toString + ") && Terminating"
    }

    def apply(record: Int): TriState = {
        for(pa <- C) {
            if(pa.apply(record).toBoolean) {
                if(udfConstraint.apply(record)) return new TriState("true")
                else return new TriState("terminating")
            }
        }
        throw new NotFoundPathCondition(record.toString)
    }
}

case class ReducePathConstraint(C: Array[PathConstraint], udfConstraint: Constraint) extends PathConstraint {
    override def toString: String = {
        //TODO: for every two records maybe? Is it Cartesian product of f(ta) and Pa(ta)?
        "for all records (ta) in A, such that Pa is a member of C(A) where Pa(ta) && " + udfConstraint.toString
    }

    def apply(record: Int): TriState = {
        //for now: is it is the same as map, but should be revised later
        for(pa <- C) {
            if(pa.apply(record).toBoolean) return new TriState(udfConstraint.apply(record).toString)
        }
        throw new NotFoundPathCondition(record.toString)
    }
}

case class JoinPathConstraint(C: Array[PathConstraint], A: RDD[Int], B: RDD[Int]) extends PathConstraint {
    override def toString: String = {
        "for all records (ta) in A, such that Pa, Pb are members of C(A) where Pa(ta) && Pb(tb), there exists an S such that ta.K = S and tb.K = S"
    }

    //how to generalize apply API? whether pass an RDD or single Int?
    //should not record be a tuple2 of Int, Int?
    //what about the other dataset containing any of this dataset key values
    def apply(record: Int): TriState = {
        var keys = B.filter(_ == record).collect
        if(keys.collect.size != 0) return new TriState("true")
        else return new TriState("Terminating")
    } 
}
