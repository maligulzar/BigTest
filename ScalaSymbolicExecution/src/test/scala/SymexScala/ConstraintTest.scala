package SymexScala

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

class ConstraintTest extends FlatSpec with BeforeAndAfterAll with Matchers {

    "test one-clause constraint" should "return path constraint for a simple map" in {
        //path: x0 > 100 -> effect : x1 = x0 + 1
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

        val pe = new PathEffect(pathCond, effect)

    }

    "test a solvable path and effect" should "return result of map and filter" in {
        //path constraint: {x2 > 0 && x0 > 100}    effect: {x1 = x0 + 1 && x2 = x1}
        val x0 = new SymVar(Numeric(_Int), "x0")
        val x2 = new SymVar(Numeric(_Int), "x2")
        val c :Array[Clause] = Array(new Clause(x0,
                                                GreaterThan,
                                                ConcreteValue(Numeric(_Int),"100")),
                                    new Clause(x2,
                                                GreaterThan,
                                                ConcreteValue(Numeric(_Int),"0")))

        val pathCond = new Constraint(c)

        val effect1: Expr = new NonTerminal(x0,
                                            new SymOp(Numeric(_Int), Addition),
                                            ConcreteValue(Numeric(_Int),"1"))
        
        val x1 = new SymVar(Numeric(_Int), "x1")

        val effect = new ArrayBuffer[Tuple2[SymVar, Expr]]()
        effect += new Tuple2(x1, effect1)
        effect += new Tuple2(x2, x1)

        val pe = new PathEffect(pathCond, effect)
    }


}