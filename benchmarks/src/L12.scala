/**
 * Created by shrinidhihudli on 2/9/15.
 *
 * -- This script covers multi-store queries.
 * register $PIGMIX_JAR
 * A = load '$HDFS_ROOT/page_views' using org.apache.pig.test.pigmix.udf.PigPerformanceLoader()
 *    as (user, action, timespent, query_term, ip_addr, timestamp,
 *        estimated_revenue, page_info, page_links);
 * B = foreach A generate user, action, (int)timespent as timespent, query_term,
 *     (double)estimated_revenue as estimated_revenue;
 * split B into C if user is not null, alpha if user is null;
 * split C into D if query_term is not null, aleph if query_term is null;
 * E = group D by user parallel $PARALLEL;
 * F = foreach E generate group, MAX(D.estimated_revenue);
 * store F into '$PIGMIX_OUTPUT/highest_value_page_per_user';
 * beta = group alpha by query_term parallel $PARALLEL;
 * gamma = foreach beta generate group, SUM(alpha.timespent);
 * store gamma into '$PIGMIX_OUTPUT/total_timespent_per_term';
 * beth = group aleph by action parallel $PARALLEL;
 * gimel = foreach beth generate group, COUNT(aleph);
 * store gimel into '$PIGMIX_OUTPUT/queries_per_action';
 *
 */

import org.apache.spark.SparkContext
import org.apache.spark.SparkContext._
import org.apache.spark.SparkConf
import java.util.Properties
import java.io.{File, FileInputStream}

import org.apache.spark.lineage.LineageContext._
import org.apache.spark.lineage.LineageContext

object L12 {
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
    val pageViews = lc.textFile(pageViewsPath)

    lc.setCaptureLineage(lineage)

    val start = System.currentTimeMillis()

    val A = pageViews.map(x => (SparkMixUtils.safeSplit(x, "\u0001", 0), 
      SparkMixUtils.safeSplit(x, "\u0001", 1), SparkMixUtils.safeSplit(x, "\u0001", 2), 
      SparkMixUtils.safeSplit(x, "\u0001", 3), SparkMixUtils.safeSplit(x, "\u0001", 4), 
      SparkMixUtils.safeSplit(x, "\u0001", 5), SparkMixUtils.safeSplit(x, "\u0001", 6),
      SparkMixUtils.createMap(SparkMixUtils.safeSplit(x, "\u0001", 7)),
      SparkMixUtils.createBag(SparkMixUtils.safeSplit(x, "\u0001", 8))))

    val B = A.map(x => (x._1, x._2, SparkMixUtils.safeInt(x._3), x._4, SparkMixUtils.safeDouble(x._7)))

    val C = B.filter(_._1 != "")

    val alpha = B.subtract(C)

    val D = C.filter(_._4 != "")

    val aleph = C.subtract(D)

    val E = D.groupBy(_._1)

    val F = E.map(x => (x._1, x._2.reduce((a, b) => ("", "", 0, "", Math.max(a._5, b._5))))).map(x => (x._1,x._2._5))

    val beta = alpha.groupBy(_._4)

    val gamma = beta.map(x => (x._1, x._2.reduce((a, b) => ("", "", a._3 + b._3, "", 0)))).map(x => (x._1,x._2._3))

    val beth = aleph.groupBy(_._2)

    val gimel = beth.map(x => (x._1, x._2.size))

    val end = System.currentTimeMillis()

    F.collect
    gamma.collect
    gimel.collect

    lc.setCaptureLineage(false)

    //F.saveAsTextFile(outputPath + "/highest_value_page_per_user")
    //gamma.saveAsTextFile(outputPath + "/total_timespent_per_term")
    //gimel.saveAsTextFile(outputPath + "/queries_per_action")

    println(end - start)

    sc.stop()

  }
}
