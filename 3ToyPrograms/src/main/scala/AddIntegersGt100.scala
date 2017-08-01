import org.apache.spark.{ SparkContext, SparkConf }
import org.apache.log4j.{ Logger, Level }

object AddIntegersGt100 {

    def main(args: Array[String]): Unit = {

        Logger.getLogger("org").setLevel(Level.OFF)
        Logger.getLogger("akka").setLevel(Level.OFF)

        val conf = new SparkConf()
        conf.setAppName("Scala Toy Example 2: Add Integers if greater than 100")
        conf.setMaster("local[4]")
        val sc = new SparkContext(conf)
        val srcPath = args(0)
        val sum = sc.textFile(srcPath)
                    .map(line => Integer.parseInt(line))
                    .map(x => if(x > 100) x else 0)
                    .reduce(_+_)
        println("Sum: "+sum)

    }
}


    //PC.f1:  x' = Integer.parseInt(x)
    //PC.f2: X = {x' = x for every x s.t. x > 100} v Y = {x' = 0 for every x s.t. !(x > 100)}
    //PC.f3: {x' = F(V) for V = X.Y} <---- acc = V(0) ^ for(i <- 1 to N-1): acc = f(acc, V(i)) ^ acc = F(V)
