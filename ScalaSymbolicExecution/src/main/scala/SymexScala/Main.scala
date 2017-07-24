package SymexScala

// import SymexScala.PathConstraint._

object Main {
    
    def main(args: Array[String]): Unit = {
        val x = new Constraint("x < 1 && y == 2 && z>y".replaceAll("\\s", ""))
        println(x)
    }
}