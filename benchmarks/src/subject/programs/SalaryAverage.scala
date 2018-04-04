package subject.programs
import org.apache.spark.{SparkConf, SparkContext}

/**
  * Created by malig on 3/27/18.
  */
object SalaryAverage {
  def main(args: Array[String]): Unit = {
    val conf = new SparkConf()
    conf.setMaster("local[*]")
    conf.setAppName("Weather")
    val sc = new SparkContext(conf)
    val lines = sc.textFile(
      "/Users/malig/workspace/up_jpf/benchmarks/src/datasets/salary.csv")
    val out = lines
      .map { s =>
        if (s.substring(0, 1).equals("$")) {
          var i = s.substring(1, s.length - 1)
          i = i.replace(",", "")
           Integer.parseInt(i)
        } else {
           Integer.parseInt(s.replace(",", ""))
        }
      }
      .filter(s => s < 30000)
      .reduce(_ + _)
    println(out)
  }
}

/***


  (define-fun integer ((x!1 String) (x!2 String) (x!3 String)) Bool
   (str.in.re x!1 (re.++ (str.to.re x!2) (re.* (re.++ (str.to.re x!3) (str.to.re x!2) ))))
)

(declare-fun s () String)
(assert ( integer s) )
(check-sat)
(get-model)



  */

