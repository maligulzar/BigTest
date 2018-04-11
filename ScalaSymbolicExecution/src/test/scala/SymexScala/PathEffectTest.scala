package symexScala

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

class PathEffectTest extends FlatSpec with BeforeAndAfterAll with Matchers {

    "test toString for empty effect" should "return {}" in {
        val ut = new PathEffect(new Constraint())
        assert(ut.toString.equals("path constraint: {}\t effect: {} ---------"))
    }

    "test conjuncting PathEffect" should "return conjuncting two path and effects" in {
        //path: x0 > 100 -> effect : x1 = x0 + 1
        val x0 = new SymVar(Numeric(_Int), "x0")
        val c0 :Array[Clause] = Array(new Clause(x0,
                                                GreaterThan,
                                                ConcreteValue(Numeric(_Int),"100")))

        val pathCond0 = new Constraint(c0)

        val eff0: Expr = new NonTerminal(x0,
                                            new SymOp(Numeric(_Int), Addition),
                                            ConcreteValue(Numeric(_Int),"1"))

        val returnVar1 = new SymVar(Numeric(_Int), "x1")
        val effects1 = new ArrayBuffer[Tuple2[SymVar, Expr]]()
        effects1 += new Tuple2(returnVar1, eff0)
        val pe01 = new PathEffect(pathCond0, effects1)


        //path: x2 < 200 -> effect : x3 = -200
        val x2 = new SymVar(Numeric(_Int), "x2")
        val c2 :Array[Clause] = Array(new Clause(x2,
                                                LessThan,
                                                ConcreteValue(Numeric(_Int),"200")))

        val pathCond2 = new Constraint(c2)

        val eff2: Expr = ConcreteValue(Numeric(_Int),"-200")

        val returnVar3 = new SymVar(Numeric(_Int), "x3")
        val effects3 = new ArrayBuffer[Tuple2[SymVar, Expr]]()
        effects3 += new Tuple2(returnVar3, eff2)
        val pe23 = new PathEffect(pathCond2, effects3)

        val link = new Tuple2(Array(x2), Array(returnVar1))

        val result = pe01.conjunctPathEffect(pe23, link)

        assert(result.isInstanceOf[PathEffect])

        assert(result.effects.size == 3)
        assert(result.pathConstraint.clauses.size == 2)

        assert(result.effects(0).equals(effects3(0)))
        assert(result.effects(1).equals(link))
        assert(result.effects(2).equals(effects1(0)))

        assert(result.pathConstraint.clauses(0).equals(c2(0)))
        assert(result.pathConstraint.clauses(1).equals(c0(0)))
        //println(result)

    }

}