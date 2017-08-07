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
        val result = SymbolicEngine.run(numbers, "map(x => if(x > 100) x else 0)")
        assert(result.isInstanceOf[SetOfConstraints])

        val fMap = new Function1[Int, Int] {
            def apply(x: Int): Int = { if(x > 100) x else 0 }
        }
        val udfPaths = new Array[Conjunction](2)
        udfPaths(0) = Conjunction.parseConjunction("x > 100")
        udfPaths(1) = Conjunction.parseConjunction("x <= 100")
        val start = new SetOfConstraints(numbers)
        val afterMap = start.map(fMap, udfPaths)

        result.paths.size should be (2)
        assert(result.toString == afterMap.toString)
        // println(result)
    }

    // it should "return path constraint for a simple map and reduce" in {
    //     val result = cut.run("map(line => Integer.parseInt(line)).reduce(_+_)")
    //     assert(result.isInstanceOf[ReducePathConstraint])
    //     assert(result == new ReducePathConstraint(new Array[PathConstraint](), new Constraint("true")))
    //     result.toString should be ("for all records in (ta) in A, such that Pa is a member of C(A) where Pa(ta) && true")
    //     // println(result)
    // }

    // "testAddIntegersGT100" should "return path constraint for a simple map" in {
    //     val result = cut.run("map(line => Integer.parseInt(line)).map(x => if(x > 100) x else 0).reduce(_+_)")
    //     assert(result.isInstanceOf[ReducePathConstraint])
    //     val mapC = new Array[PathConstraint]()
    //     mapC += new MapPathConstraint(new Array[PathConstraint](), new Constraint("x > 100"))
    //     assert(result == new ReducePathConstraint(mapC, new Constraint("true")))
    //     // println(result)
    // }

    // "testAddEvenIntegers" should "return path constraint for a simple map" in {
    //     val result = cut.run("map(line => Integer.parseInt(line)).filter(_%2 == 0).reduce(_+_)")
    //     assert(result.isInstanceOf[ReducePathConstraint])
    //     val filterC = new Array[PathConstraint]()
    //     filterC += new FilterPathConstraint(new Array[PathConstraint](), new Constraint("x%2 == 0"))
    //     assert(result == new ReducePathConstraint(filterC, new Constraint("true")))
    //     // println(result)
    // }
}