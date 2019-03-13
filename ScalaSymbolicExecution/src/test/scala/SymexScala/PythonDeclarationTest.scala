package SymexScala

import SymexScala.ArithmeticOp._
import SymexScala.ComparisonOp._
import SymexScala.NonNumericUnderlyingType._Boolean
import SymexScala.NumericUnderlyingType._Int
import org.scalatest.{BeforeAndAfterAll, FlatSpec, Matchers}

class PythonDeclarationTest extends FlatSpec with BeforeAndAfterAll with Matchers {
  " test empty constraint" should "return true...?" in {
    var genStr = new Constraint().toPythonFunction()
    assert(genStr === "lambda: True")
  }
  
  " test each data type" should "return expected python expression" in {
    // this is just a brief test.
    val sampleNumericStr = "42" // assumption: SymexScala correctly handles type->value checks
    // and we only need to worry about string conversion.
    NumericUnderlyingType.values.foreach(t => {
      val genStr = Numeric(t).toConcretePythonExpr(sampleNumericStr)
      assert(genStr == sampleNumericStr)
    })
    NonNumericUnderlyingType.values.foreach {
      case _Boolean =>
        val boolVType = NonNumeric(_Boolean)
        // check that the Scala boolean variables map to the Python ones.
        assert(boolVType.toConcretePythonExpr(true.toString) === "True")
        assert(boolVType.toConcretePythonExpr(false.toString) === "False")
      case _Unit => // no test to run here, no defined behavior yet.
      case _ => fail("Unhandled/unexpected non-numeric type!")
    }
  }
  
  // In practice, should probably have more granular examples too. oops. e.g., Expr and Clause-level
  
  
  "test one-clause simple constraint" should "return appropriate python def" in {
    // x0 > 100, taken from ConstraintTest
    val x0 = new SymVar(Numeric(_Int), "x0")
    val c: Array[Clause] = Array(new Clause(x0,
                                            GreaterThan,
                                            ConcreteValue(Numeric(_Int), "100")))
  
    val constraint = new Constraint(c)
  
    assert(constraint.toPythonFunction() === "lambda x0: (x0 > 100)")
  }
  
  "Test constraint with nested clause and multiple args" should "return appropriate python def" in {
    val x0 = SymVar(Numeric(_Int), "x0")
    val x1 = SymVar(Numeric(_Int), "x1")
    val x2 = SymVar(Numeric(_Int), "x2")
    // rough tree illustration:
    //         +
    //     x0           *
    //            -         42
    //         x1   x2
    val subtrNode = NonTerminal(x1, SymOp(Numeric(_Int), Subtraction), x2)
    val multNode = NonTerminal(subtrNode,
                                   SymOp(Numeric(_Int), Multiplication),
                                   ConcreteValue(Numeric(_Int), "42"))
    val addNode = NonTerminal(x0, SymOp(Numeric(_Int), Addition), multNode)
    
    val clause = new Clause(addNode, LessThanOrEq, multNode)
    val constraint = new Constraint(Array(clause))
    // unfortunate implementation note: the argument declaration order depends on underlying data
    // structure and algorithmic details, which are reflected in this hardcoded string.
    // TODO if we change to multiline python func defs, we could individually declare clauses and
    //  evaluate them more generally.
    
    assert(constraint.toPythonFunction() === "lambda x2, x1, x0: ((x0 + ((x1 - x2) * 42)) <= ((x1 - x2) * 42))")
    // you can demo this using arguments of [0, 0, 0] and [0, 0, 1] as an example.
  }
  
  "test multiple clauses" should "return conjunction of constraints" in {
    // clauses are: x0 > 100, b0 == True, True != False
    // b0 == True could technically be shortened to "b0" - I would recommend that as a
    // postprocessing step or additional case in the Clause implementation. This representation
    // is, however, more explicit as Python allows for boolean evaluation of non-boolean values
    // as well (eg "hello" is truthy).
    val x0 = SymVar(Numeric(_Int), "x0")
    val numericValue = ConcreteValue(Numeric(_Int), "100")
    val clause1 = new Clause(x0,
                             GreaterThan,
                             numericValue)
    
    val b0 = SymVar(NonNumeric(_Boolean), "b0")
    val trueValue = ConcreteValue(NonNumeric(_Boolean), true.toString)
    val falseValue = ConcreteValue(NonNumeric(_Boolean), false.toString)
    val clause2 = new Clause(b0, Equality, trueValue)
    val clause3 = new Clause(trueValue, Inequality, falseValue)
    val clauses: Array[Clause] = Array(clause1, clause2, clause3)
    val constraint = new Constraint(clauses)
    // declared argument order depends on iteration.
    assert(constraint.toPythonFunction() === "lambda b0, x0: (x0 > 100) and (b0 == True) and (True != False)")
  }
}
