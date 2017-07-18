class ToyScalaP {

    def main(args: Array[String]) {
        println("Start of Test");
        var a: Int = 120
        var b: Int = 140
        testMe(a, b);
    }

    def testMe (a: Int, b: Int): Unit = {
        if (a > 100) {
            if (b > 120) {
                println("a+b = " + a + b)
            }
            else {
                println("b was <= 120")
            }
        }
        else {
            println("a was <= 100")
        }
    }
}