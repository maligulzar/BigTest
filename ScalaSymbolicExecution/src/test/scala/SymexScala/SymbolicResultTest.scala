package SymexScala

import org.scalatest._
import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }
import org.apache.spark.rdd._

import udfExtractor.Runner
import udfExtractor.JPFDAGNode
import java.util.ArrayList
import scala.collection.mutable.ArrayBuffer

import NumericUnderlyingType._
import NonNumericUnderlyingType._
import ComparisonOp._
import ArithmeticOp._

class SymbolicResultTest extends FlatSpec with BeforeAndAfterAll with Matchers {

    private var pe: PathAndEffect = null
    
    override def beforeAll() {
        val x0 = new SymVar(Numeric(_Int), "x0")
        val c :Array[Clause] = Array(new Clause(x0,
                                                GreaterThan,
                                                ConcreteValue(Numeric(_Int),"100")))

        val pathCond = new Constraint(c)

        val effect1: Expr = new NonTerminal(x0,
                                            new SymOp(Numeric(_Int), Addition),
                                            ConcreteValue(Numeric(_Int),"1"))

        val x1 = new SymVar(Numeric(_Int), "x1")

        val effect = new ArrayBuffer[Tuple2[SymVar, Expr]]()
        effect += new Tuple2(x1, effect1)

        this.pe = new PathAndEffect(pathCond, effect)
    }

    //not possible to call spf from different test suites, probably spf has some mutil-threading issue ->
/*
    "testSymbolicResult2Maps" should "return path constraint for a simple map" in {
        Runner.main(Array("Test6"))
        val dagOpList = Main.convertList(Runner.getDataFlowDAG)

        val symState = new SymbolicState()
        var init: SymbolicResult = new SymbolicResult(symState)
        //dagOpList(0)._1 is a map
        val map1UDF = SymbolicEngine.callSPF(dagOpList(0)._2, symState)
        //dagOpList(1)._1 is a map
        val map2UDF = SymbolicEngine.callSPF(dagOpList(1)._2, symState)

        //println(map1UDF)
        //println(map2UDF)

        val afterMap1 = init.map(map1UDF)
        println(afterMap1)
        assert(afterMap1.isInstanceOf[SymbolicResult])
        assert(afterMap1.numOfPaths == 2)

        //path constraint: {x0 > 100}    effect: {x1 = x0 + 1} ---------
        assert(afterMap1.paths(1).equals(this.pe))

        assert(afterMap1.numOfTerminating == 0)
        assert(afterMap1.symInput.equals(map1UDF.symInput))
        assert(afterMap1.symOutput.equals(map1UDF.symOutput))

        val afterMap2 = afterMap1.map(map2UDF)
        println(afterMap2)
        assert(afterMap2.isInstanceOf[SymbolicResult])

    }
*/
}