
/**
  * Created by malig on 6/4/16.
  */
object  Tool {


  def main (args: Array[String] ) {
    val conf = new Configuration("conf.txt").loadMapping().enableSparkMutation()
    val inputdir = "work/input/SparkWordCount.scala"
    val pathtosrc = "work/input/"   // usually /src/main
    val outputdir = "work/output/SparkWordCount.scala"
    val ex = new Extractor()
//    ex.run(conf,inputdir,pathtosrc, outputdir)
    ex.runOneFile(conf, inputdir, outputdir)
  }
}