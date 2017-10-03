/**
 * Created by shrinidhihudli on 2/9/15.
 *
 * -- This script covers distinct and union.
 * register $PIGMIX_JAR
 * A = load '$HDFS_ROOT/page_views' using org.apache.pig.test.pigmix.udf.PigPerformanceLoader()
 *     as (user, action, timespent, query_term, ip_addr, timestamp,
 *         estimated_revenue, page_info, page_links);
 * B = foreach A generate user;
 * C = distinct B parallel $PARALLEL;
 * alpha = load '$HDFS_ROOT/widerow' using PigStorage('\u0001');
 * beta = foreach alpha generate $0 as name;
 * gamma = distinct beta parallel $PARALLEL;
 * D = union C, gamma;
 * E = distinct D parallel $PARALLEL;
 * store E into '$PIGMIX_OUTPUT/L11out';
 *
 */

import org.apache.spark.{SparkConf, SparkContext}


object L11 {
  def main(args: Array[String]) {
    val conf = new SparkConf()
    var lineage = false
    var saveToHdfs = false
    var path = "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/pigmix_"
    if(args.size < 1) {
      path = "../../datasets/pigMix/"  + "pigmix_10M/"
      conf.setMaster("local[2]")
      lineage = true
    } else {
      path += args(0) + "G"
      conf.setMaster("spark://SCAI01.CS.UCLA.EDU:7077")
      saveToHdfs = true
    }
    conf.setAppName("SparkMix-L11" + lineage + "-" + path)

    val sc = new SparkContext(conf)

    val pageViewsPath = path + "page_views/"
    val widerowPath = path + "widerow/"

    val alpha = sc.textFile(widerowPath)

    val pageViews = sc.textFile(pageViewsPath)

    val A = pageViews.map(x => (SparkMixUtils.safeSplit(x, "\u0001", 0), 
      SparkMixUtils.safeSplit(x, "\u0001", 1), SparkMixUtils.safeSplit(x, "\u0001", 2), 
      SparkMixUtils.safeSplit(x, "\u0001", 3), SparkMixUtils.safeSplit(x, "\u0001", 4), 
      SparkMixUtils.safeSplit(x, "\u0001", 5), SparkMixUtils.safeSplit(x, "\u0001", 6),
      SparkMixUtils.createMap(SparkMixUtils.safeSplit(x, "\u0001", 7)),
      SparkMixUtils.createBag(SparkMixUtils.safeSplit(x, "\u0001", 8))))

    val B = A.map(_._1)

    val C = B.distinct()

    val beta = alpha.map(x => x.split("\u0001")(0))

    val gamma = beta.distinct()

    val D = C.union(gamma)

    val E = D.distinct()

    if(saveToHdfs) {
      E.saveAsTextFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/output-L11-" + args(0) + "G")
    } else {
      E.collect.foreach(println)
    }

    sc.stop()
  }
}
