package symexScala

import org.scalatest._
import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }
import org.apache.spark.rdd._
import scala.collection.mutable.ArrayBuffer

import udfExtractor.Runner
import udfExtractor.JPFDAGNode

import NumericUnderlyingType._
import NonNumericUnderlyingType._
import ComparisonOp._
import ArithmeticOp._

class JoinTest extends FlatSpec with BeforeAndAfterAll with Matchers {

/*
    "simple join" should "return path constraint for a simple join" in {
        val symState = new SymbolicState()

        val filter1 = SymbolicEngine.executeDFOperator(symState, "filter", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/filter1.jpf")
        val _A = new SymTuple(Tuple(Numeric(_Int), Numeric(_Int)), "A") //filter1.symInput
        val initA = new SymbolicResult(symState, filter1.paths, filter1.terminating, _A._1, _A)
        // initA.symOutput = _A //RDD A which is of type (Int, Int)
        println(initA)

        val filter2 = SymbolicEngine.executeDFOperator(symState, "filter", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/filter2.jpf")
        val _B = new SymTuple(Tuple(Numeric(_Int), Numeric(_Int)), "B")
        val initB = new SymbolicResult(symState, filter2.paths, filter2.terminating, _B._1, _B)
        // initB.symOutput = _B //RDD B which is also of type (Int, Int)
        println(initB)

        val result = initA.join(initB)
        println(result)
        result.solveWithZ3

    }
*/
    "join on keys" should "return path constraint for a simple join on keys" in {
        val symState = new SymbolicState()

        val filter1 = SymbolicEngine.executeDFOperator(symState, "filter", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/filter1.jpf")
        val symOutputA = Array[SymVar](new SymVar(Numeric(_Int), "A_1"), new SymVar(Numeric(_Int), "A_2"))
        filter1.paths(0).addEffect(new SymVar(Numeric(_Int), "x0"), symOutputA(0))
        val initA = new SymbolicResult(symState, filter1.paths, filter1.terminating, symOutputA, symOutputA)
        println("--------------------------------")
        println(initA)
        println("--------------------------------")

        val filter2 = SymbolicEngine.executeDFOperator(symState, "filter", "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/filter2.jpf")
        val symOutputB = Array[SymVar](new SymVar(Numeric(_Int), "B_1"), new SymVar(Numeric(_Int), "B_2"))
        filter2.paths(0).addEffect(new SymVar(Numeric(_Int), "x2"), symOutputB(0))
        val initB = new SymbolicResult(symState, filter2.paths, filter2.terminating, symOutputB, symOutputB)
        println("--------------------------------")
        println(initB)
        println("--------------------------------")

        val result = initA.join(initB)
        // val result = JoinSymbolicResult(symState, initA, initB)
        println(result)
        // result.solveWithZ3

    }


}