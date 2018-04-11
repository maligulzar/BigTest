package symexScala

import org.scalatest._
import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }
import org.apache.spark.rdd._
import scala.collection.mutable.ArrayBuffer

import NumericUnderlyingType._
import NonNumericUnderlyingType._
import ComparisonOp._
import ArithmeticOp._

class SymbolicRDDTest extends FlatSpec with BeforeAndAfterAll with Matchers {

    "symbolicRDDAggregate" should "return aggregated function on a 4-elements collection" in {
        //[x0, x1, x2]
        val elems = new Array[SymVar](4)
        elems(0) = new SymVar(Numeric(_Int), "x0")
        elems(1) = new SymVar(Numeric(_Int), "x1")
        elems(2) = new SymVar(Numeric(_Int), "x2")
        elems(3) = new SymVar(Numeric(_Int), "x3")

        val rdd = new SymbolicRDD("rdd", elems)

        val x = new SymVar(Numeric(_Int), "x")
        val y = new SymVar(Numeric(_Int), "y")
        val f = new NonTerminal(x, new SymOp(Numeric(_Int), Addition), y)
        println("f: "+f)

        val result = rdd.aggregateOnRDD(f)
        println(result)
        assert(result.toString().equals("x0 + x1 + x2 + x3"))
    }

    "symbolicRDDAggregate on Half Pipeline" should "return aggregated function given a udf generated by udf_extractor" in {
        //reduce1
        val jpfFile = "/Users/amytis/Projects/jpf/jpf-symbc/src/examples/spf/reduce1.jpf"

        val symState = new SymbolicState()
        var currentPaths: SymbolicResult = new SymbolicResult(symState)
        val udfResult = SymbolicEngine.callSPF(jpfFile, symState)

        // println("-------------------------------")
        // println(udfResult)

        val elems = new Array[SymVar](4)
        elems(0) = new SymVar(Numeric(_Int), "x0")
        elems(1) = new SymVar(Numeric(_Int), "x1")
        elems(2) = new SymVar(Numeric(_Int), "x2")
        elems(3) = new SymVar(Numeric(_Int), "x3")

        val rdd = new SymbolicRDD("rdd", elems)

        val f = udfResult.paths(0).effects(0)._2 //x+y
        println("f: "+f)

        assert(f.isInstanceOf[NonTerminal])
        val result = rdd.aggregateOnRDD(f.asInstanceOf[NonTerminal])
        println(result)
        assert(result.toString().equals("x0 + x1 + x2 + x3"))
        // assert(result.isInstanceOf[NonTerminal])

    }


}