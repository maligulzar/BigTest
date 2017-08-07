
/**
  * Created by malig on 6/4/16.
  */
object  Tool {


  def main (args: Array[String] ) {

    WordCount.main(Array[String]())
///Users/malig/workspace/git/Test-Minimization-in-Big-Data/udf_extractor/src/main/scala/WordCount.scala
    val conf = new Configuration("conf.txt").loadMapping().enableSparkMutation()
    val inputdir = "src/main/scala/WordCount.scala"
    val pathtosrc = "work/input/"   // usually /src/main
    val outputdir = "work/output/SparkWordCount.txt"
    val ex = new Extractor()
//    ex.run(conf,inputdir,pathtosrc, outputdir)
    ex.runOneFile(conf, inputdir, outputdir)

  }

}