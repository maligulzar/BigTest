/**
 * Created by shrinidhihudli on 2/4/15.
 *
 * -- This script tests reading from a map, flattening a bag of maps, and use of bincond.
 *    register $PIGMIX_JAR (register /home/clash/pig-0.14.0/test/perf/pigmix/pigmix.jar)
 *    A = load '$HDFS_ROOT/page_views' using org.apache.pig.test.pigmix.udf.PigPerformanceLoader()
 *        as (user, action, timespent, query_term, ip_addr, timestamp, estimated_revenue, page_info, page_links);
 *    B = foreach A generate user, (int)action as action, (map[])page_info as page_info,
 *        flatten((bag{tuple(map[])})page_links) as page_links;
 *    C = foreach B generate user,
 *        (action == 1 ? page_info#'a' : page_links#'b') as header;
 *    D = group C by user parallel $PARALLEL;
 *    E = foreach D generate group, COUNT(C) as cnt;
 *    store E into '$PIGMIX_OUTPUT/L1out';
 */


import org.apache.spark.{SparkConf, SparkContext}


object L1 {
  def main(args: Array[String]) {
    val conf = new SparkConf()
    var saveToHdfs = false
    var path = "hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/pigmix_"
    if(args.size < 1) {
      path = "../../datasets/pigMix/"  + "pigmix_10M/"
      conf.setMaster("local[2]")
    } else {
      path += args(0) + "G"
      conf.setMaster("spark://SCAI01.CS.UCLA.EDU:7077")
      saveToHdfs = true
    }
    conf.setAppName("SparkMix-L1-" + path)

    val sc = new SparkContext(conf)

    val pageViewsPath = path + "page_views/"

    val pageViews = sc.textFile(pageViewsPath)

    val A = pageViews.map(x => (SparkMixUtils.safeSplit(x, "\u0001", 0),
      SparkMixUtils.safeSplit(x, "\u0001", 1), SparkMixUtils.safeSplit(x, "\u0001", 2),
      SparkMixUtils.safeSplit(x, "\u0001", 3), SparkMixUtils.safeSplit(x, "\u0001", 4), 
      SparkMixUtils.safeSplit(x, "\u0001", 5), SparkMixUtils.safeSplit(x, "\u0001", 6),
      SparkMixUtils.createMap(SparkMixUtils.safeSplit(x, "\u0001", 7)),
      SparkMixUtils.createBag(SparkMixUtils.safeSplit(x, "\u0001", 8))))

    val B = A.map(x => (x._1, x._2, x._8, x._9)).flatMap(r => for (v <- r._4) yield (r._1, r._2, r._3, v))

    val C = B.map(x => if (x._2 == "1") (x._1, x._3.get("a").toString) else (x._1, x._4.get("b").toString))

    val D = C.groupBy(_._1)

    val E = D.map(x => (x._1, x._2.size))

    if(saveToHdfs) {
      E.saveAsTextFile("hdfs://scai01.cs.ucla.edu:9000/clash/datasets/pigmix-spark/output-L1-" + args(0) + "G")
    } else {
      E.collect.foreach(println)
    }

    sc.stop()
  }

}
