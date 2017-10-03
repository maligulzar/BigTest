/**
 * Created by shrinidhihudli on 2/8/15.
 *
 *-- This script covers group all.
 * register $PIGMIX_JAR
 * A = load '$HDFS_ROOT/page_views' using org.apache.pig.test.pigmix.udf.PigPerformanceLoader()
 *    as (user, action, timespent, query_term, ip_addr, timestamp,
 *        estimated_revenue, page_info, page_links);
 * B = foreach A generate user, (int)timespent as timespent, (double)estimated_revenue as estimated_revenue;
 * C = group B all;
 * D = foreach C generate SUM(B.timespent), AVG(B.estimated_revenue);
 * store D into '$PIGMIX_OUTPUT/L8out';
 *
 */

import java.io._

import org.apache.spark.{SparkConf, SparkContext}
import org.apache.spark.lineage.LineageContext


object L8 {
  def main(args: Array[String]) {

    val properties = SparkMixUtils.loadPropertiesFile()
    val dataSize = args(0)
    val lineage: Boolean = args(1).toBoolean

    val pigMixPath = properties.getProperty("pigMix") + "pigmix_" + dataSize + "/"
    val outputRoot = properties.getProperty("output") + "pigmix_" + dataSize + "_" + (System.currentTimeMillis() / 100000 % 1000000) + "/"

    new File(outputRoot).mkdir()

    val conf = new SparkConf().setAppName("SparkMix").setMaster("spark://SCAI01.CS.UCLA.EDU:7077")
    val sc = new SparkContext(conf)
    val lc = new LineageContext(sc)

    val pageViewsPath = pigMixPath + "page_views/"

    lc.setCaptureLineage(lineage)
    val pageViews = lc.textFile(pageViewsPath)


    val A = pageViews.map(x => (SparkMixUtils.safeSplit(x, "\u0001", 0), 
      SparkMixUtils.safeSplit(x, "\u0001", 1), SparkMixUtils.safeSplit(x, "\u0001", 2), 
      SparkMixUtils.safeSplit(x, "\u0001", 3), SparkMixUtils.safeSplit(x, "\u0001", 4), 
      SparkMixUtils.safeSplit(x, "\u0001", 5), SparkMixUtils.safeSplit(x, "\u0001", 6),
      SparkMixUtils.createMap(SparkMixUtils.safeSplit(x, "\u0001", 7)),
      SparkMixUtils.createBag(SparkMixUtils.safeSplit(x, "\u0001", 8))))

    val B = A.map(x => (x._1, SparkMixUtils.safeInt(x._3), SparkMixUtils.safeDouble(x._7)))

    val C = B

    val D = C.reduce((x, y) => ("", x._2 + y._2, x._3 + y._3))

    val E = (D._2, D._3 / C.filter(x => x._3 != 0).count())

    //if (lc != null)
    lc.setCaptureLineage(false)

    //val pw = new PrintWriter(new File(outputPath))
    //pw.write(E.toString())
    //pw.close()

    sc.stop()

  }
}
