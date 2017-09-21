package SymexScala

import org.scalatest._
import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }
import org.apache.spark.rdd._

import udfExtractor.Runner
import udfExtractor.JPFDAGNode
import java.util.ArrayList

import NumericUnderlyingType._
import NonNumericUnderlyingType._

class SymbolicEngineTest extends FlatSpec with BeforeAndAfterAll with Matchers {

/*
    private var sc: SparkContext = _
    private var numbers: RDD[Int] = _
    
    override def beforeAll() {

        Logger.getLogger("org").setLevel(Level.OFF)
        Logger.getLogger("akka").setLevel(Level.OFF)

        val conf = new SparkConf()
            .setMaster("local[4]")
            .setAppName("Scala Symex Test")
        sc = new SparkContext(conf)
        val srcPath = "input"

        numbers = sc.textFile(srcPath)
                    .map(line => Integer.parseInt(line))
    }
    
    override def afterAll() {
        sc.stop()
    }
*/

    "test1" should "return path constraint for a simple map" in {
        Runner.main(Array("Test1"))
        val dagOpList = Main.convertList(Runner.getDataFlowDAG)
        val engineResult = SymbolicEngine.executeSymbolicDF(dagOpList)
        assert(engineResult.isInstanceOf[SymbolicResult])

        assert(engineResult.numOfPaths == 2)
        assert(engineResult.numOfTerminating == 0)

        assert(engineResult.paths(0).toString == "path constraint: {x <= 100}\t effect: {x = 0} ---------")
        assert(engineResult.paths(0).pathConstraint.toString == "x <= 100")
        assert(engineResult.paths(0).effect._1.equals(new SymVar(Numeric(_Int), "x")))
        assert(engineResult.paths(0).effect._2(0).equals(new ConcreteValue(Numeric(_Int), "0")))
        
        assert(engineResult.paths(1).toString == "path constraint: {x > 100}\t effect: {x = x} ---------")
        assert(engineResult.paths(1).pathConstraint.toString == "x > 100")
        val x = new SymVar(Numeric(_Int), "x")
        assert(engineResult.paths(1).effect._1.equals(x))
        assert(engineResult.paths(1).effect._2(0).equals(x))
    }


    "test2" should "return path constraint for a simple map and filter" in {
        Runner.main(Array("Test2"))
        val dagOpList = Main.convertList(Runner.getDataFlowDAG)
        val engineResult = SymbolicEngine.executeSymbolicDF(dagOpList)
        assert(engineResult.isInstanceOf[SymbolicResult])

        assert(engineResult.numOfPaths == 2)
        assert(engineResult.numOfTerminating == 2)

        assert(engineResult.paths(0).toString == "path constraint: {0 > 0 && x <= 100}\t effect: {x = 0} ---------")
        assert(engineResult.paths(0).pathConstraint.toString == "0 > 0 && x <= 100")
        assert(engineResult.paths(0).effect._1.equals(new SymVar(Numeric(_Int), "x")))
        assert(engineResult.paths(0).effect._2(0).equals(new ConcreteValue(Numeric(_Int), "0")))
        
        assert(engineResult.paths(1).toString == "path constraint: {x + 1 > 0 && x > 100}\t effect: {x = x + 1} ---------")
        assert(engineResult.paths(1).pathConstraint.toString == "x + 1 > 0 && x > 100")
        val x = new SymVar(Numeric(_Int), "x")
        assert(engineResult.paths(1).effect._1.equals(x))
        assert(engineResult.paths(1).effect._2(0).toString == "x + 1")

        assert(engineResult.terminating(0).toString == "path constraint: {0 <= 0 && x <= 100}\t effect: {x = 0} ---------")
        assert(engineResult.terminating(0).pathConstraint.toString == "0 <= 0 && x <= 100")
        assert(engineResult.terminating(0).effect._1.equals(new SymVar(Numeric(_Int), "x")))
        assert(engineResult.terminating(0).effect._2(0).equals(new ConcreteValue(Numeric(_Int), "0")))
        
        assert(engineResult.terminating(1).toString == "path constraint: {x + 1 <= 0 && x > 100}\t effect: {x = x + 1} ---------")
        assert(engineResult.terminating(1).pathConstraint.toString == "x + 1 <= 0 && x > 100")
        assert(engineResult.terminating(1).effect._1.equals(x))
        assert(engineResult.terminating(1).effect._2(0).toString == "x + 1")
    }

    "test3" should "return path constraint for a map,filter,map program" in {
        Runner.main(Array("Test3"))
        val dagOpList = Main.convertList(Runner.getDataFlowDAG)
        val engineResult = SymbolicEngine.executeSymbolicDF(dagOpList)
        assert(engineResult.isInstanceOf[SymbolicResult])

        assert(engineResult.numOfPaths == 4)
        assert(engineResult.numOfTerminating == 2)

        val x = new SymVar(Numeric(_Int), "x")

        assert(engineResult.paths(0).toString == "path constraint: {0 >= 200 && 0 > 0 && x <= 100}\t effect: {x = 0, x = 0} ---------")
        assert(engineResult.paths(0).pathConstraint.toString == "0 >= 200 && 0 > 0 && x <= 100")
        assert(engineResult.paths(0).effect._1.equals(x))
        assert(engineResult.paths(0).effect._2.size == 2)
        
        assert(engineResult.paths(1).toString == "path constraint: {0 < 200 && 0 > 0 && x <= 100}\t effect: {x = 0, x = -200} ---------")
        assert(engineResult.paths(1).pathConstraint.toString == "0 < 200 && 0 > 0 && x <= 100")
        assert(engineResult.paths(1).effect._1.equals(x))
        assert(engineResult.paths(1).effect._2.size == 2)

        assert(engineResult.paths(2).toString == "path constraint: {x + 1 >= 200 && x + 1 > 0 && x > 100}\t effect: {x = x + 1, x = x + 1} ---------")
        assert(engineResult.paths(2).pathConstraint.toString == "x + 1 >= 200 && x + 1 > 0 && x > 100")
        assert(engineResult.paths(2).effect._1.equals(x))
        assert(engineResult.paths(2).effect._2.size == 2)
        
        assert(engineResult.paths(3).toString == "path constraint: {x + 1 < 200 && x + 1 > 0 && x > 100}\t effect: {x = x + 1, x = -200} ---------")
        assert(engineResult.paths(3).pathConstraint.toString == "x + 1 < 200 && x + 1 > 0 && x > 100")
        assert(engineResult.paths(3).effect._1.equals(x))
        assert(engineResult.paths(3).effect._2.size == 2)


        assert(engineResult.terminating(0).toString == "path constraint: {0 <= 0 && x <= 100}\t effect: {x = 0} ---------")
        assert(engineResult.terminating(0).pathConstraint.toString == "0 <= 0 && x <= 100")
        assert(engineResult.terminating(0).effect._1.equals(new SymVar(Numeric(_Int), "x")))
        assert(engineResult.terminating(0).effect._2(0).equals(new ConcreteValue(Numeric(_Int), "0")))
        
        assert(engineResult.terminating(1).toString == "path constraint: {x + 1 <= 0 && x > 100}\t effect: {x = x + 1} ---------")
        assert(engineResult.terminating(1).pathConstraint.toString == "x + 1 <= 0 && x > 100")
        assert(engineResult.terminating(1).effect._1.equals(x))
        assert(engineResult.terminating(1).effect._2(0).toString == "x + 1")
    }

    "test4" should "return path constraint for a map,filter,map,filter program" in {
        Runner.main(Array("Test4"))
        val dagOpList = Main.convertList(Runner.getDataFlowDAG)
        val engineResult = SymbolicEngine.executeSymbolicDF(dagOpList)
        assert(engineResult.isInstanceOf[SymbolicResult])

        assert(engineResult.numOfPaths == 4)
        assert(engineResult.numOfTerminating == 6)
        val x = new SymVar(Numeric(_Int), "x")

        // assert(engineResult.paths(0).toString == "path constraint: {0 > 0 && 0 >= 200 && 0 > 10 && x <= 100}\t effect: {x = 0, x = 0} ---------")
        assert(engineResult.paths(0).pathConstraint.toString == "0 > 0 && 0 >= 200 && 0 > 10 && x <= 100")
        assert(engineResult.paths(0).effect._1.equals(x))
        assert(engineResult.paths(0).effect._2(0).equals(new ConcreteValue(Numeric(_Int), "0")))

        assert(engineResult.paths(1).pathConstraint.toString == "-200 > 0 && 0 < 200 && 0 > 10 && x <= 100")
        assert(engineResult.paths(1).effect._1.equals(x))
        assert(engineResult.paths(1).effect._2(0).equals(new ConcreteValue(Numeric(_Int), "0")))
        assert(engineResult.paths(1).effect._2(1).equals(new ConcreteValue(Numeric(_Int), "-200")))

        assert(engineResult.paths(2).pathConstraint.toString == "x > 0 && x >= 200 && x > 10 && x > 100")
        assert(engineResult.paths(2).effect._1.equals(x))
        assert(engineResult.paths(2).effect._2(0).equals(x))
        assert(engineResult.paths(2).effect._2(1).equals(x))

        assert(engineResult.paths(3).pathConstraint.toString == "-200 > 0 && x < 200 && x > 10 && x > 100")
        assert(engineResult.paths(3).effect._1.equals(x))
        assert(engineResult.paths(3).effect._2(0).equals(x))
        assert(engineResult.paths(3).effect._2(1).equals(new ConcreteValue(Numeric(_Int), "-200")))

        assert(engineResult.terminating(0).pathConstraint.toString == "0 <= 10 && x <= 100")
        assert(engineResult.terminating(0).effect._1.equals(x))
        assert(engineResult.terminating(0).effect._2(0).equals(new ConcreteValue(Numeric(_Int), "0")))
        
        assert(engineResult.terminating(1).pathConstraint.toString == "x <= 10 && x > 100")
        assert(engineResult.terminating(1).effect._1.equals(x))
        assert(engineResult.terminating(1).effect._2(0).equals(x))
        
        assert(engineResult.terminating(2).pathConstraint.toString == "0 <= 0 && 0 >= 200 && 0 > 10 && x <= 100")
        assert(engineResult.terminating(2).effect._1.equals(x))
        assert(engineResult.terminating(2).effect._2(0).equals(new ConcreteValue(Numeric(_Int), "0")))
        assert(engineResult.terminating(2).effect._2(1).equals(new ConcreteValue(Numeric(_Int), "0")))
        
        assert(engineResult.terminating(3).pathConstraint.toString == "-200 <= 0 && 0 < 200 && 0 > 10 && x <= 100")
        assert(engineResult.terminating(3).effect._1.equals(x))
        assert(engineResult.terminating(3).effect._2(0).equals(new ConcreteValue(Numeric(_Int), "0")))
        assert(engineResult.terminating(3).effect._2(1).equals(new ConcreteValue(Numeric(_Int), "-200")))
        
        assert(engineResult.terminating(4).pathConstraint.toString == "x <= 0 && x >= 200 && x > 10 && x > 100")
        assert(engineResult.terminating(4).effect._1.equals(x))
        assert(engineResult.terminating(4).effect._2(0).equals(x))
        assert(engineResult.terminating(4).effect._2(1).equals(x))
        
        assert(engineResult.terminating(5).pathConstraint.toString == "-200 <= 0 && x < 200 && x > 10 && x > 100")
        assert(engineResult.terminating(5).effect._1.equals(x))
        assert(engineResult.terminating(5).effect._2(0).equals(x))
        assert(engineResult.terminating(5).effect._2(1).equals(new ConcreteValue(Numeric(_Int), "-200")))

    }


    // "testMapFilter(Effect)" should "return path constraint correctly for proceeding non-terminating paths including the effect of previous udf" in {
    //     val sourceCode = """map((x: Int, y: Int) => 
    //                             if(x > 100) {
    //                                 x = x * 4;
    //                                 y = y - 20;
    //                             }
    //                             else {
    //                                 x = x * 2;
    //                                 y = y + 10;
    //                             }

    //                             if(y > 10 && x > 150){
    //                                 x = x + y;
    //                             }
    //                             else {
    //                                 x = x - y;
    //                             }
    //                         ).filter((x, y) => x%2 == 0)"""

    //     val result = SymbolicEngine.run(sourceCode)
    //     assert(result.isInstanceOf[SymbolicResult])

    //     val mapUdfPaths = new Array[Constraint](2)
    //     mapUdfPaths(0) = Constraint.parseConstraint("x > 100")
    //     mapUdfPaths(1) = Constraint.parseConstraint("x <= 100")
    //     val start = new SymbolicResult()
    //     val afterMapFilter = start.map(fMap1, mapUdfPaths).filter(fFilter)
    //     val afterSecondMap = afterMapFilter.map(fMap2, mapUdfPaths) //!

    //     result.paths.size should be (8) //at least
    //     assert(result.toString == afterMapFilter.toString)
    // }

}