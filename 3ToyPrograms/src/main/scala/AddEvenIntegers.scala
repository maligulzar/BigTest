import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }

object AddEvenIntegers {

    def main(args: Array[String]): Unit = {

        Logger.getLogger("org").setLevel(Level.OFF)
        Logger.getLogger("akka").setLevel(Level.OFF)

        val conf = new SparkConf()
        conf.setAppName("Scala Toy Example 3: Add Even Integers")
        conf.setMaster("local[4]")
        val sc = new SparkContext(conf)
        val srcPath = args(0)
        val sum = sc.textFile(srcPath)
                    .map(line => Integer.parseInt(line))
                    .filter(_%2 == 0)
                    .reduce(_+_)
        println("Sum: "+sum)

    }
}

    //PC.f1:  x' = Integer.parseInt(x)
    //PC.f2: X = {x' = x for every x s.t. x%2 == 0}
    //PC.f3: {x' = F(V)} <---- acc = V(0) ^ for(i <- 1 to N-1): acc = f(acc, V(i)) ^ acc = F(V)

