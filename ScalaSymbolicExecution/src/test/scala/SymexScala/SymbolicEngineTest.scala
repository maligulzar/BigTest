package SymexScala

import org.scalatest._
import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }
import org.apache.spark.rdd._

import NumericUnderlyingType._
import NonNumericUnderlyingType._

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
        SymbolicEngine.defineVar("x", Numeric(_Int))
        val engineResult = SymbolicEngine.run("map(x: Int => if(x > 100) x else 0)", 1)
        assert(engineResult.isInstanceOf[SymbolicResult])


        val c1 = Constraint.parseConstraint("x > 100")
        val path1 = new PathAndEffect(c1)

        val c2 = Constraint.parseConstraint("x <= 100")
        val e2 = SymbolicEngine.parseEffect("x = 0;")
        val path2 = new PathAndEffect(c2, e2)

        val allUdfPaths = new Array[PathAndEffect](2)
        allUdfPaths(0) = path1
        allUdfPaths(1) = path2

        val udfSymbolicResult = new SymbolicResult(allUdfPaths)

        val mapResult = new SymbolicResult().map(udfSymbolicResult)

        assert(mapResult.isInstanceOf[SymbolicResult])
        mapResult.paths.size should be (2)

        // println(mapResult)
        // println("-------------")
        // println(udfSymbolicResult)
        assert(mapResult.equals(udfSymbolicResult)) //only because previous to map, our only path was true 
        assert(mapResult.equals(engineResult))
    }

    // it should "return path constraint for a simple map and reduce" in {
    //     val result = cut.run("map(line => Integer.parseInt(line)).reduce(_+_)")
    //     assert(result.isInstanceOf[ReducePathAndEffect])
    //     assert(result == new ReducePathAndEffect(new Array[PathAndEffect](), new Constraint("true")))
    //     result.toString should be ("for all records in (ta) in A, such that Pa is a member of C(A) where Pa(ta) && true")
    //     // println(result)
    // }

    "testAddEvenIntegersGT100" should "return path constraint for a simple map and filter" in {
        SymbolicEngine.defineVar("x", Numeric(_Int))
        var engineResult = SymbolicEngine.run("map(x: Int => if(x > 100) x else 0).filter(_%2 == 0)", 2)
        assert(engineResult.isInstanceOf[SymbolicResult])


        val c1 = Constraint.parseConstraint("x > 100")
        val path1 = new PathAndEffect(c1)

        val c2 = Constraint.parseConstraint("x <= 100")
        val e2 = SymbolicEngine.parseEffect("x = 0;")
        val path2 = new PathAndEffect(c2, e2)

        val allMapPaths = new Array[PathAndEffect](2)
        allMapPaths(0) = path1
        allMapPaths(1) = path2

        val c3 = Constraint.parseConstraint("x%2 == 0")
        val path3 = new PathAndEffect(c3)
        
        val nonTpaths = new Array[PathAndEffect](1)
        nonTpaths(0) = path3

        val c4 = Constraint.parseConstraint("x%2 != 0")
        val path4 = new TerminatingPath(c4)
        
        val terminPaths = new Array[TerminatingPath](1)
        terminPaths(0) = path4

        val mapSymbolicResult = new SymbolicResult(allMapPaths)
        val filterSymbolicResult = new SymbolicResult(nonTpaths, terminPaths)

        val mapResult = new SymbolicResult().map(mapSymbolicResult)
        val mapFilterResult = new SymbolicResult().map(mapSymbolicResult).filter(filterSymbolicResult)

        mapFilterResult.paths.size should be (2) //only 2 remaining terminating path

        val resultPaths = new Array[PathAndEffect](2)
        resultPaths(0) = path1.conjunctWith(path3)
        resultPaths(1) = path2.conjunctWith(path3)
        
        val terminatingResPaths = new Array[TerminatingPath](2)
        terminatingResPaths(0) = path1.conjunctWith(path4).asInstanceOf[TerminatingPath]
        terminatingResPaths(1) = path2.conjunctWith(path4).asInstanceOf[TerminatingPath]

        engineResult = new SymbolicResult(resultPaths, terminatingResPaths)
        assert(mapFilterResult.equals(engineResult))
    }

    "testMapFilterMap(Terminating)" should "return path constraint for both terminating and non-terminating paths" in {
        SymbolicEngine.defineVar("x", Numeric(_Int))
        val sourceCode = """map(x: Int => if(x > 100) x else 0)
                            .filter(_%2 == 0)
                            .map(x => if(x < 200) -200 else x)"""
        val engineResult = SymbolicEngine.run(sourceCode, 3)
        assert(engineResult.isInstanceOf[SymbolicResult])

        //first Map UDF
        val c1 = Constraint.parseConstraint("x > 100")
        val path1 = new PathAndEffect(c1)

        val c2 = Constraint.parseConstraint("x <= 100")
        val e2 = SymbolicEngine.parseEffect("x = 0;")
        val path2 = new PathAndEffect(c2, e2)

        val allMapPaths = new Array[PathAndEffect](2)
        allMapPaths(0) = path1
        allMapPaths(1) = path2

        val mapSymbolicResult = new SymbolicResult(allMapPaths)
        
        //filter UDF
        val c3 = Constraint.parseConstraint("x%2 == 0")
        val path3 = new PathAndEffect(c3)
        
        val nonTpaths = new Array[PathAndEffect](1)
        nonTpaths(0) = path3

        val c4 = Constraint.parseConstraint("x%2 != 0")
        val path4 = new TerminatingPath(c4)
        
        val terminPaths = new Array[TerminatingPath](1)
        terminPaths(0) = path4

        val filterSymbolicResult = new SymbolicResult(nonTpaths, terminPaths)

        //second Map UDF
        val c5 = Constraint.parseConstraint("x < 200")
        val e5 = SymbolicEngine.parseEffect("x = -200;")
        val path5 = new PathAndEffect(c5, e5)

        val c6 = Constraint.parseConstraint("x >= 200")
        val path6 = new PathAndEffect(c6)

        val allMap2Paths = new Array[PathAndEffect](2)
        allMap2Paths(0) = path5
        allMap2Paths(1) = path6

        val secondMapSymbolicResult = new SymbolicResult(allMap2Paths)

        val mapResult = new SymbolicResult().map(mapSymbolicResult)
        val mapFilterResult = new SymbolicResult().map(mapSymbolicResult).filter(filterSymbolicResult)

        val finalResult = mapFilterResult.map(secondMapSymbolicResult)

        finalResult.paths.size should be (4)
        // assert(mapFilterResult.equlas(engineResult))
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

    // "testAddEvenIntegers" should "return path constraint for a simple map" in {
    //     val result = cut.run("map(line => Integer.parseInt(line)).filter(_%2 == 0).reduce(_+_)")
    //     assert(result.isInstanceOf[ReducePathAndEffect])
    //     val filterC = new Array[PathAndEffect]()
    //     filterC += new FilterPathAndEffect(new Array[PathAndEffect](), new Constraint("x%2 == 0"))
    //     assert(result == new ReducePathAndEffect(filterC, new Constraint("true")))
    //     // println(result)
    // }
}