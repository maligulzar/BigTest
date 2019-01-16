import airporttransit._
import commutetype._
import gradeanalysis._
import incomeaggregate._
import movieratings._
import org.apache.spark.{SparkConf, SparkContext}
import pigmixl2._
import wordcount.{WordCount, WordCountFaultWrongDelim, WordCountMutateOperatorAdd}

/**
  * Created by malig on 1/14/19.
  */
object TestSuiteRunner {

  val commute_data1 = Array(",, ,0,1",
    ",, ,16,1",
    ",, ,41,1",
    ",A, ,-0,1",
    ",A, ,-0,1")

  val commute_data2 = Array(",Palms",
    ",Palms",
    ",Palms" ,
  " , "," , ")

  val studentgrades_data1 = Array(":0\n:0",
    ":0\n:41",
    ":41\n:0"	,
    ":41\n:41")
  val incomeagg_data1 = Array("0",
    "$0",
    "800",
    "$800")
  val movie_data1 = Array(" : _5", ": _0")

  val airport_data1 = Array(" , ,90:0,-0:0, ",
    " , ,-0:0,-0:0, ",
    " , ,-0:9,-0:0, ",
    " , ,-0:0,00:0, ")

  val l2_data1 = Array(", , , , , , ",
    "A, , , , , , ",
    "A, , , , , , "
  )
  val l2_data2 =
    Array("", "", "")


  val wc_data1 = Array("\n",  "\n ,", " ,\n" , " ,\n ,")



  def prnt(str:String , program:String , output: String = "" ) = {
    println(s""">>$program>>,""" + str + s""",Test Data: $output  """ )
  }
  def main(args: Array[String]): Unit = {

    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("CommuteTime")
    val sc = new SparkContext(conf)
   // testCommuteType(sc)
   // testStudentGrades(sc)
    //testIncomeAggregate(sc)
    //testMovieRating(sc)
    //testAirportTransit(sc)
    //testL2(sc)
    testWordCount(sc)
  }

  def testCommuteType(sc: SparkContext): Unit ={
    // Testing Commute Type
    for(i <- 0 to commute_data1.length-1){
      val trips = sc.parallelize(Array(commute_data1(i)))
      val locations = sc.parallelize(Array(commute_data2(i)))
      var test_output = "---"
      try {
        test_output = CommuteType.execute(trips, locations).collect().mkString("\n")
        prnt("P, Passed,"+ i , "Commute Type" , test_output);
      }
      catch{
        case e:Exception =>
          prnt("P,Crashed," + i, "Commute Type" , test_output);
      }
      try {
        val f2output = CommuteTypeFaultWrongColumn.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f2output)) {
          prnt("F2,Passed," + i, "Commute Type" , f2output);
        } else {
          prnt("F2,Failed," + i, "Commute Type" , f2output);
        }
      } catch {
        case e: Exception =>
          prnt("F2,Crashed," + i, "Commute Type" );
      }

      try {
        val f3output = CommuteTypeFaultWrongDelim.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f3output)) {
          prnt("F3,Passed," + i, "Commute Type" , f3output);
        } else {
          prnt("F3,Failed," + i, "Commute Type" , f3output);

        }
      } catch {
        case e: Exception =>
          prnt("F3,Crashed," + i, "Commute Type");
      }

      try {
        val f4output = CommuteTypeFaultWrongPredicate.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f4output)) {
          prnt("F4,Passed," + i, "Commute Type" , f4output);
        } else {
          prnt("F4,Failed," + i, "Commute Type" , f4output);

        }
      } catch {
        case e: Exception =>
          prnt("F4,Crashed," + i, "Commute Type");
      }

      try {
        val f5output = CommuteTypeFaultWrongJoin.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f5output)) {
          prnt("F5,Passed," + i, "Commute Type" , f5output);
        } else {
          prnt("F5,Failed," + i, "Commute Type" , f5output);

        }
      } catch {
        case e: Exception =>
          prnt("F5,Crashed," + i, "Commute Type");
      }

      try {
        val f6output = CommuteTypeFaultSwapKV.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f6output)) {
          prnt("F6,Passed," + i, "Commute Type" , f6output);
        } else {
          prnt("F6,Failed," + i, "Commute Type" , f6output);

        }
      } catch {
        case e: Exception =>
          prnt("F6,Crashed," + i, "Commute Type");
      }

      try {
        val f7output = CommuteTypeMutationOperatorDiv.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f7output)) {
          prnt("F7,Passed," + i, "Commute Type" , f7output);
        } else {
          prnt("F7,Failed," + i, "Commute Type" , f7output);

        }
      } catch {
        case e: Exception =>
          prnt("F7,Crashed," + i, "Commute Type");
      }
    }
  }
  def testStudentGrades(sc: SparkContext): Unit = {
    // Testing Student Grades Type
    for (i <- 0 to studentgrades_data1.length - 1) {
      val input = sc.parallelize(Array(studentgrades_data1(i)))
      var test_output = "---"
      try {
        test_output = StudentGrades.execute(input).collect().mkString("\n")
        prnt("P, Passed," + i, "Student Grades", test_output);
      }
      catch {
        case e: Exception =>
          prnt("P,Crashed," + i, "Student Grades", test_output);
      }
      try {
        val f2output = StudentGradesFaultWrongColumn.execute(input).collect().mkString("\n")
        if (test_output.equals(f2output)) {
          prnt("F2,Passed," + i, "Student Grades", f2output);
        } else {
          prnt("F2,Failed," + i, "Student Grades", f2output);
        }
      } catch {
        case e: Exception =>
          prnt("F2,Crashed," + i, "Student Grades");
      }

      try {
        val f3output = StudentGradesFaultWrongDelim.execute(input).collect().mkString("\n")
        if (test_output.equals(f3output)) {
          prnt("F3,Passed," + i, "Student Grades", f3output);
        } else {
          prnt("F3,Failed," + i, "Student Grades", f3output);

        }
      } catch {
        case e: Exception =>
          prnt("F3,Crashed," + i, "Student Grades");
      }

      try {
        val f4output = StudentGradesFaultWrongPredicate.execute(input).collect().mkString("\n")
        if (test_output.equals(f4output)) {
          prnt("F4,Passed," + i, "Student Grades", f4output);
        } else {
          prnt("F4,Failed," + i, "Student Grades", f4output);

        }
      } catch {
        case e: Exception =>
          prnt("F4,Crashed," + i, "Student Grades");
      }

      try {
        val f7output = StudentGradesMutationOperatorGT.execute(input).collect().mkString("\n")
        if (test_output.equals(f7output)) {
          prnt("F7,Passed," + i, "Student Grades", f7output);
        } else {
          prnt("F7,Failed," + i, "Student Grades", f7output);

        }
      } catch {
        case e: Exception =>
          prnt("F7,Crashed," + i, "Student Grades");
      }
    }
  }
  def testIncomeAggregate(sc: SparkContext): Unit = {
    // Testing Student Grades Type
    for (i <- 0 to incomeagg_data1.length - 1) {
      val input = sc.parallelize(Array(incomeagg_data1(i)))
      var test_output = "---"
      try {
        test_output = IncomeAggregate.execute(input)
        prnt("P, Passed," + i, "Income Aggregate", test_output);
      }
      catch {
        case e: Exception =>
          e.printStackTrace()
          prnt("P,Crashed," + i, "Income Aggregate", test_output);
      }
      try {
        val f2output = IncomeAggregateFaultWrongOffsets.execute(input)
        if (test_output.equals(f2output)) {
          prnt("F1,Passed," + i, "Income Aggregate", f2output);
        } else {
          prnt("F1,Failed," + i, "Income Aggregate", f2output);
        }
      } catch {
        case e: Exception =>
          prnt("F1,Crashed," + i, "Income Aggregate");
      }

      try {
        val f4output = IncomeAggregateFaultWrongPredicate.execute(input)
        if (test_output.equals(f4output)) {
          prnt("F4,Passed," + i, "Income Aggregate", f4output);
        } else {
          prnt("F4,Failed," + i, "Income Aggregate", f4output);

        }
      } catch {
        case e: Exception =>
          prnt("F4,Crashed," + i, "Income Aggregate");
      }

      try {
        val f7output = IncomeAggregateMutateOperatorLT.execute(input)
        if (test_output.equals(f7output)) {
          prnt("F7,Passed," + i, "Income Aggregate", f7output);
        } else {
          prnt("F7,Failed," + i, "Income Aggregate", f7output);

        }
      } catch {
        case e: Exception =>
          prnt("F7,Crashed," + i, "Income Aggregate");
      }
    }
  }
  def testMovieRating(sc: SparkContext): Unit ={
    // Testing Commute Type
    for(i <- 0 to movie_data1.length-1){
      val input = sc.parallelize(Array(movie_data1(i)))
      var test_output = "---"
      try {
        test_output = MovieRatingsCount.execute(input).collect().mkString("\n")
        prnt("P, Passed,"+ i , "Movie Rating" , test_output);
      }
      catch{
        case e:Exception =>
          prnt("P,Crashed," + i, "Movie Rating" , test_output);
      }

      try {
        val f1output = MovieRatingCountFaultWrongOffsets.execute(input).collect().mkString("\n")
        if (test_output.equals(f1output)) {
          prnt("F1,Passed," + i, "Movie Rating" , f1output);
        } else {
          prnt("F1,Failed," + i, "Movie Rating" , f1output);

        }
      } catch {
        case e: Exception =>
          prnt("F1,Crashed," + i, "Movie Rating");
      }


      try {
        val f2output = MovieRatingCountFaultWrongColumn.execute(input).collect().mkString("\n")
        if (test_output.equals(f2output)) {
          prnt("F2,Passed," + i, "Movie Rating" , f2output);
        } else {
          prnt("F2,Failed," + i, "Movie Rating" , f2output);
        }
      } catch {
        case e: Exception =>
          prnt("F2,Crashed," + i, "Movie Rating" );
      }

      try {
        val f3output = MovieRatingCountFaultWrongDelim.execute(input).collect().mkString("\n")
        if (test_output.equals(f3output)) {
          prnt("F3,Passed," + i, "Movie Rating" , f3output);
        } else {
          prnt("F3,Failed," + i, "Movie Rating" , f3output);

        }
      } catch {
        case e: Exception =>
          prnt("F3,Crashed," + i, "Movie Rating");
      }

      try {
        val f4output = MovieRatingCountFaultWrongPredicate.execute(input).collect().mkString("\n")
        if (test_output.equals(f4output)) {
          prnt("F4,Passed," + i, "Movie Rating" , f4output);
        } else {
          prnt("F4,Failed," + i, "Movie Rating" , f4output);

        }
      } catch {
        case e: Exception =>
          prnt("F4,Crashed," + i, "Movie Rating");
      }


      try {
        val f6output = MovieRatingCountFaultSwapKV.execute(input).collect().mkString("\n")
        if (test_output.equals(f6output)) {
          prnt("F6,Passed," + i, "Movie Rating" , f6output);
        } else {
          prnt("F6,Failed," + i, "Movie Rating" , f6output);

        }
      } catch {
        case e: Exception =>
          prnt("F6,Crashed," + i, "Movie Rating");
      }

      try {
        val f7output = MovieRatingCountMutationOperatorGt.execute(input).collect().mkString("\n")
        if (test_output.equals(f7output)) {
          prnt("F7,Passed," + i, "Movie Rating" , f7output);
        } else {
          prnt("F7,Failed," + i, "Movie Rating" , f7output);

        }
      } catch {
        case e: Exception =>
          prnt("F7,Crashed," + i, "Movie Rating");
      }
    }
  }
  def testAirportTransit(sc: SparkContext): Unit ={
    for(i <- 0 to airport_data1.length-1){
      val input = sc.parallelize(Array(airport_data1(i)))
      var test_output = "---"
      try {
        test_output = AirportTransit.execute(input).collect().mkString("\n")
        prnt("P, Passed,"+ i , "Airport Transit" , test_output);
      }
      catch{
        case e:Exception =>
          prnt("P,Crashed," + i, "Airport Transit" , test_output);
      }

      try {
        val f1output = AirportTransitFaultOffsets.execute(input).collect().mkString("\n")
        if (test_output.equals(f1output)) {
          prnt("F1,Passed," + i, "Airport Transit" , f1output);
        } else {
          prnt("F1,Failed," + i, "Airport Transit" , f1output);

        }
      } catch {
        case e: Exception =>
          prnt("F1,Crashed," + i, "Airport Transit");
      }


      try {
        val f2output = AirportTransitFaultWrongColumn.execute(input).collect().mkString("\n")
        if (test_output.equals(f2output)) {
          prnt("F2,Passed," + i, "Airport Transit" , f2output);
        } else {
          prnt("F2,Failed," + i, "Airport Transit" , f2output);
        }
      } catch {
        case e: Exception =>
          prnt("F2,Crashed," + i, "Airport Transit" );
      }

      try {
        val f3output = AirportTransitFaultWrongDelim.execute(input).collect().mkString("\n")
        if (test_output.equals(f3output)) {
          prnt("F3,Passed," + i, "Airport Transit" , f3output);
        } else {
          prnt("F3,Failed," + i, "Airport Transit" , f3output);

        }
      } catch {
        case e: Exception =>
          prnt("F3,Crashed," + i, "Airport Transit");
      }

      try {
        val f4output = AirportTransitFaultWrongPredicate.execute(input).collect().mkString("\n")
        if (test_output.equals(f4output)) {
          prnt("F4,Passed," + i, "Airport Transit" , f4output);
        } else {
          prnt("F4,Failed," + i, "Airport Transit" , f4output);

        }
      } catch {
        case e: Exception =>
          prnt("F4,Crashed," + i, "Airport Transit");
      }


      try {
        val f6output = AirportTransitFaultSwapKV.execute(input).collect().mkString("\n")
        if (test_output.equals(f6output)) {
          prnt("F6,Passed," + i, "Airport Transit" , f6output);
        } else {
          prnt("F6,Failed," + i, "Airport Transit" , f6output);

        }
      } catch {
        case e: Exception =>
          prnt("F6,Crashed," + i, "Airport Transit");
      }

      try {
        val f7output = AirportTransitMutationOperatorGT.execute(input).collect().mkString("\n")
        if (test_output.equals(f7output)) {
          prnt("F7,Passed," + i, "Airport Transit" , f7output);
        } else {
          prnt("F7,Failed," + i, "Airport Transit" , f7output);

        }
      } catch {
        case e: Exception =>
          prnt("F7,Crashed," + i, "Airport Transit");
      }
    }
  }
  def testL2(sc: SparkContext): Unit ={
    // Testing Commute Type
    for(i <- 0 to l2_data1.length-1){
      val trips = sc.parallelize(Array(l2_data1(i)))
      val locations = sc.parallelize(Array(l2_data2(i)))
      var test_output = "---"
      try {
        test_output = L2.execute(trips, locations).collect().mkString("\n")
        prnt("P, Passed,"+ i , "L2" , test_output);
      }
      catch{
        case e:Exception =>
          prnt("P,Crashed," + i, "L2" , test_output);
      }
      try {
        val f2output = L2FaultWrongColumn.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f2output)) {
          prnt("F2,Passed," + i, "L2" , f2output);
        } else {
          prnt("F2,Failed," + i, "L2" , f2output);
        }
      } catch {
        case e: Exception =>
          prnt("F2,Crashed," + i, "L2" );
      }

      try {
        val f3output = L2FaultWrongDelim.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f3output)) {
          prnt("F3,Passed," + i, "L2" , f3output);
        } else {
          prnt("F3,Failed," + i, "L2" , f3output);

        }
      } catch {
        case e: Exception =>
          prnt("F3,Crashed," + i, "L2");
      }

      try {
        val f5output = L2FaultWrongJoin.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f5output)) {
          prnt("F5,Passed," + i, "L2" , f5output);
        } else {
          prnt("F5,Failed," + i, "L2" , f5output);

        }
      } catch {
        case e: Exception =>
          prnt("F5,Crashed," + i, "L2");
      }

      try {
        val f6output = L2FaultSwapKV.execute(trips, locations).collect().mkString("\n")
        if (test_output.equals(f6output)) {
          prnt("F6,Passed," + i, "L2" , f6output);
        } else {
          prnt("F6,Failed," + i, "L2" , f6output);

        }
      } catch {
        case e: Exception =>
          prnt("F6,Crashed," + i, "L2");
      }
    }
  }
  def testWordCount(sc: SparkContext): Unit ={
    // Testing Commute Type
    for(i <- 0 to wc_data1.length-1){
      val input = sc.parallelize(Array(wc_data1(i)))
      var test_output = "---"
      try {
        test_output = WordCount.execute(input).collect().mkString("\n")
        prnt("P, Passed,"+ i , "WordCount" , test_output);
      }
      catch{
        case e:Exception =>
          prnt("P,Crashed," + i, "WordCount" , test_output);
      }


      try {
        val f3output = WordCountFaultWrongDelim.execute(input).collect().mkString("\n")
        if (test_output.equals(f3output)) {
          prnt("F3,Passed," + i, "WordCount" , f3output);
        } else {
          prnt("F3,Failed," + i, "WordCount" , f3output);

        }
      } catch {
        case e: Exception =>
          prnt("F3,Crashed," + i, "WordCount");
      }


      try {
        val f6output = WordCountMutateOperatorAdd.execute(input).collect().mkString("\n")
        if (test_output.equals(f6output)) {
          prnt("F7,Passed," + i, "WordCount" , f6output);
        } else {
          prnt("F7,Failed," + i, "WordCount" , f6output);

        }
      } catch {
        case e: Exception =>
          prnt("F7,Crashed," + i, "WordCount");
      }
    }
  }

}
