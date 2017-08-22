package SymexScala

import org.scalatest._
import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }
import org.apache.spark.rdd._

class SymbolicEngineTest extends FlatSpec with BeforeAndAfterAll with Matchers {

    private var sc: SparkContext = _
    private var numbers: RDD[Int] = _
    // private val cut = new SymbolicEngine()
 
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

    //Toy#1
    "testAddIntegers" should "return path constraint for a simple map" in {
        val result = SymbolicEngine.run(numbers, "map(x: Int => if(x > 100) x else 0)")
        assert(result.isInstanceOf[SetOfConstraints])

        val fMap = new Function1[Int, Int] {
            def apply(x: Int): Int = { if(x > 100) x else 0 }
        }
        val udfPaths = new Array[Conjunction](2)
        udfPaths(0) = Conjunction.parseConjunction("x > 100")
        udfPaths(1) = Conjunction.parseConjunction("x <= 100")
        val start = new SetOfConstraints(numbers)
        val afterMap = start.map(fMap, udfPaths)

        SymbolicEngine.afterMap.paths.size should be (2)
        assert(SymbolicEngine.afterMap.toString == afterMap.toString)
        // println(result)
    }

    // it should "return path constraint for a simple map and reduce" in {
    //     val result = cut.run("map(line => Integer.parseInt(line)).reduce(_+_)")
    //     assert(result.isInstanceOf[ReducePathConstraint])
    //     assert(result == new ReducePathConstraint(new Array[PathConstraint](), new Constraint("true")))
    //     result.toString should be ("for all records in (ta) in A, such that Pa is a member of C(A) where Pa(ta) && true")
    //     // println(result)
    // }

    "testAddEvenIntegersGT100" should "return path constraint for a simple map and filter" in {
        val result = SymbolicEngine.run(numbers, "map(x: Int => if(x > 100) x else 0).filter(_%2 == 0)")
        assert(result.isInstanceOf[SetOfConstraints])

        val fMap = new Function1[Int, Int] {
            def apply(x: Int): Int = { if(x > 100) x else 0 }
        }
        val fFilter = new Function1[Int, Boolean] {
            def apply(x: Int): Boolean = {x%2 == 0}
        }

        val mapUdfPaths = new Array[Conjunction](2)
        mapUdfPaths(0) = Conjunction.parseConjunction("x > 100")
        mapUdfPaths(1) = Conjunction.parseConjunction("x <= 100")
        val start = new SetOfConstraints(numbers)
        val afterMapFilter = start.map(fMap, mapUdfPaths).filter(fFilter)

        result.paths.size should be (4)
        assert(result.toString == afterMapFilter.toString)
    }

    "testMapFilterMap(Terminating)" should "return path constraint for both terminating and non-terminating paths" in {
        val sourceCode = """map(x: Int => if(x > 100) x else 0)
                            .filter(_%2 == 0)
                            .map(y => if(y < 200) -200 else y)"""
        val result = SymbolicEngine.run(numbers, sourceCode)
        assert(result.isInstanceOf[SetOfConstraints])

        val fMap1 = new Function1[Int, Int] {
            def apply(x: Int): Int = { if(x > 100) x else 0 }
        }
        val fFilter = new Function1[Int, Boolean] {
            def apply(x: Int): Boolean = {x%2 == 0}
        }
        val fMap2 = new Function1[Int, Int] {
            def apply(x: Int): Int = { if(y < 200) -200 else y }
        }

        val mapUdfPaths = new Array[Conjunction](2)
        mapUdfPaths(0) = Conjunction.parseConjunction("x > 100")
        mapUdfPaths(1) = Conjunction.parseConjunction("x <= 100")
        val start = new SetOfConstraints(numbers)
        val afterMapFilter = start.map(fMap1, mapUdfPaths).filter(fFilter)
        val afterSecondMap = afterMapFilter.map(fMap2, mapUdfPaths) //!

        result.paths.size should be (8)
        assert(result.toString == afterMapFilter.toString)
    }

    "testMapFilter(Effect)" should "return path constraint correctly for proceeding non-terminating paths including the effect of previous udf" in {
        val sourceCode = """map((x: Int, y: Int) => 
                                if(x > 100) {
                                    x = x * 4;
                                    y = y - 20;
                                }
                                else {
                                    x = x * 2;
                                    y = y + 10;
                                }

                                if(y > 10 && x > 150){
                                    x = x + y;
                                }
                                else {
                                    x = x - y;
                                }
                            ).filter((x, y) => x%2 == 0)"""

        val result = SymbolicEngine.run(numbers, sourceCode)
        assert(result.isInstanceOf[SetOfConstraints])

        val mapUdfPaths = new Array[Conjunction](2)
        mapUdfPaths(0) = Conjunction.parseConjunction("x > 100")
        mapUdfPaths(1) = Conjunction.parseConjunction("x <= 100")
        val start = new SetOfConstraints(numbers)
        val afterMapFilter = start.map(fMap1, mapUdfPaths).filter(fFilter)
        val afterSecondMap = afterMapFilter.map(fMap2, mapUdfPaths) //!

        result.paths.size should be (8) //at least
        assert(result.toString == afterMapFilter.toString)
    }

    // "testAddEvenIntegers" should "return path constraint for a simple map" in {
    //     val result = cut.run("map(line => Integer.parseInt(line)).filter(_%2 == 0).reduce(_+_)")
    //     assert(result.isInstanceOf[ReducePathConstraint])
    //     val filterC = new Array[PathConstraint]()
    //     filterC += new FilterPathConstraint(new Array[PathConstraint](), new Constraint("x%2 == 0"))
    //     assert(result == new ReducePathConstraint(filterC, new Constraint("true")))
    //     // println(result)
    // }
}