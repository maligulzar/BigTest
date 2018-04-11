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


    def createFilterSymbolicResult(ss: SymbolicState, threshold: Int): SymbolicResult = {
        val inputVar1 = ss.getFreshSymVar("int")
        val symInput = Array[SymVar](inputVar1, ss.getFreshSymVar("int")) //e.g. (x0, x1)
        val filterReturnVar = ss.getFreshSymVar("int") //e.g. x2

        val fclause = new Clause(inputVar1, ComparisonOp.GreaterThan, new ConcreteValue(Numeric(_Int), threshold.toString))
        val filterIn = new Clause(inputVar1, ComparisonOp.Equality, new SymVar(Numeric(_Int), "x_filter"+threshold.toString))
        val pathCluases = Array[Clause](fclause, filterIn) //e.g. x0 > 5
        val filterEffect = new ArrayBuffer[Tuple2[SymVar, Expr]]()
        filterEffect += new Tuple2(filterReturnVar, new ConcreteValue(Numeric(_Int), "1")) // e.g. x2 = 1
        //***//
        val paths = Array[PathEffect](new PathEffect(new Constraint(pathCluases), filterEffect))

        val tfclause = new Clause(inputVar1, ComparisonOp.LessThanOrEq, new ConcreteValue(Numeric(_Int), threshold.toString))
        val termPathCluases = Array[Clause](tfclause, filterIn) //e.g. x0 <= 5
        val terminatingEffect = new ArrayBuffer[Tuple2[SymVar, Expr]]()
        terminatingEffect += new Tuple2(filterReturnVar,  new ConcreteValue(Numeric(_Int), "0")) // e.g. x2 = 0
        //***//
        val terminating = new ArrayBuffer[TerminatingPath]()
        terminating += new TerminatingPath(new Constraint(termPathCluases), terminatingEffect)

        new SymbolicResult(ss, paths, terminating, symInput, symInput)

    }

    "join on keys" should "return path constraint for a simple join on keys" in {
        val ss = new SymbolicState()

        val filter1 = createFilterSymbolicResult(ss, 5)
        println("--------------------------------")
        println(filter1.toString)
        println("--------------------------------")

        val filter2 = createFilterSymbolicResult(ss, 15)
        println("--------------------------------")
        println(filter2)
        println("--------------------------------")

        val result = filter1.join(filter2)
        // val result = JoinSymbolicResult(symState, initA, initB)
        println(result)
        // result.solveWithZ3

    }


}