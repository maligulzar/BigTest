package symexScala

import java.io.{ BufferedWriter, File, FileWriter }
import java.util
import java.util.HashSet

import scala.collection.mutable.ArrayBuffer
import NumericUnderlyingType._
import ComparisonOp._
import ArithmeticOp._
import udfExtractor.SystemCommandExecutor

class NotFoundPathCondition(message: String, cause: Throwable = null)
    extends RuntimeException("Not found Pa in C(A) for record " + message, cause) {}

/*
    paths = different paths each being satisfied by an equivalent class of tuples in dataset V
*/
class SymbolicResult(ss: SymbolicState,
                    nonT: Array[PathEffect],
                    t: ArrayBuffer[TerminatingPath] = null,
                    iVar: Array[SymVar] = Array(),
                    oVar: Array[SymVar] = Array()) {

    var Z3DIR: String = "/Users/amytis/Projects/z3-master"
    var SOLVER: String = "Z3"
    val state: SymbolicState = ss
    val paths: Array[PathEffect] = nonT
    val terminating: ArrayBuffer[TerminatingPath] = t
    var symInput: Array[SymVar] = iVar
    var symOutput: Array[SymVar] = oVar

    def this(ss: SymbolicState) {
        this(ss, new Array[PathEffect](1))
        paths(0) = new PathEffect(new Constraint()) //true
    }

    def setZ3Dir(path: String) {
        Z3DIR = path
    }
    def setSolver(path: String) {
        SOLVER = path
    }

    override def toString: String = {
        var result = "Set of Constraints for this dataset V:\nNon-terminating:\n"
        paths.foreach(result += _.toString + "\n")

        if (terminating != null) {
            result += "terminating:\n"
            terminating.foreach(result += _.toString + "\n")
        }

        result
    }

    def writeTempSMTFile(filename: String, z3: String): Unit = {
        try {
            val file: File = new File(filename)
            if (!file.exists) {
                file.createNewFile
            }
            val fw: FileWriter = new FileWriter(file)
            val bw = new BufferedWriter(fw)
            bw.write(z3);
            bw.close();
        } catch {
            case ex: Exception =>
                ex.printStackTrace();
        }
    }

    def runZ3Command(filename: String, Z3dir: String, args: Array[String] = Array()): String = {
        // build the system command we want to run
        var s = ""
        // if (SOLVER.equals("CVC4")) {
        //     s = "/Users/malig/Downloads/cvc4-1.5/builds/x86_64-apple-darwin16.7.0/production/bin/cvc4 --strings-exp --lang smt2 < " + filename

        // } else {
        //     s = "python " + Z3dir + "runZ3.py " + filename
        // }

        // for (a <- args) {
        //     s = s + "  " + a
        // }
        // println("run z3 for file " + s)
        // try {
        //     val commands: util.List[String] = new util.ArrayList[String]
        //     commands.add("/bin/sh")
        //     commands.add("-c")
        //     commands.add(s)
        //     val commandExecutor: SystemCommandExecutor = new SystemCommandExecutor(commands, Z3dir)
        //     val result: Int = commandExecutor.executeCommand();
        //     val stdout: java.lang.StringBuilder = commandExecutor.getStandardOutputFromCommand
        //     val stderr: java.lang.StringBuilder = commandExecutor.getStandardErrorFromCommand
        //     println("********** Satisfying Assigments **********************************************")
        //     println(stdout.toString)
        //     println("*******************************************************************************")

        //     println("\n" + stderr.toString)
        //     return stdout.toString()
        // } catch {
        //     case e: Exception => {
        //         e.printStackTrace
        //     }
        // }
        ""
    }

    def solveWithZ3(): String = {
        var result = ""
        println("Non-Terminating")
        for (path <- paths) {
            var str = path.toZ3Query();
            if (SOLVER.equals("CVC4")) {
                str = str + "\n(check-sat)\n(get-model)"
            }
            var filename = "/tmp/" + path.hashCode();
            result += str+"\n"
            writeTempSMTFile(filename, str);
            println("------------------------")
            println(path.toString)
            println("Z3Query:\n" + str)
            println("------------------------")
            runZ3Command(filename, Z3DIR);
        }
        println("Terminating")
        for (path <- terminating) {
            var str = path.toZ3Query();
            if (SOLVER.equals("CVC4")) {
                str = str + "\n(check-sat)\n(get-model)"
            }
            var filename = "/tmp/" + path.hashCode();
            result += str+"\n"
            writeTempSMTFile(filename, str);
            println("------------------------")
            println(path.toString)
            println("Z3Query:\n" + str)
            println("------------------------")
            runZ3Command(filename, Z3DIR);

        }
        result
    }

    def numOfPaths: Int = { paths.size }

    def numOfTerminating: Int = {
        if (terminating != null) terminating.size
        else 0
    }

    def map(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        //returns Cartesian product of already existing paths *  set of paths from given udf

        val product = new Array[PathEffect](paths.size * udfSymbolicResult.numOfPaths)
        val product_terminating = ArrayBuffer.fill((paths.size * udfSymbolicResult.numOfTerminating) + numOfTerminating)(new TerminatingPath(new Constraint()))
        var i = 0
        var j = 0;
        var terminatingPaths = new ArrayBuffer[TerminatingPath]()
        if (this.terminating != null) {
            for (tp <- this.terminating) {
                product_terminating(j) = tp
                j += 1
            }

        }

        for (pa <- this.paths) {
            for (udfPath <- udfSymbolicResult.paths) {
                //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                val link: Tuple2[Array[SymVar], Array[SymVar]] =
                    if (this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], this.symOutput.asInstanceOf[Array[SymVar]])
                    else null

                product(i) = udfPath.conjunctPathEffect(pa, link)
                i += 1
            }
        }

        for (pa <- this.paths) {
            for (udfPath <- udfSymbolicResult.terminating) {
                //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                val link: Tuple2[Array[SymVar], Array[SymVar]] =
                    if (this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], this.symOutput.asInstanceOf[Array[SymVar]])
                    else null

                product_terminating(j) = udfPath.conjunctPathEffect(pa, link)
                j += 1
            }
        }

        val input = if (this.symInput.length == 0) udfSymbolicResult.symInput else this.symInput
        new SymbolicResult(this.state, product, product_terminating, input, udfSymbolicResult.symOutput)
    }

    def reduce(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        //returns Cartesian product of already existing paths *  set of paths from given udf
        val product = new Array[PathEffect](paths.size * udfSymbolicResult.numOfPaths)
        var i = 0
        for (pa <- this.paths) {
            for (udfPath <- udfSymbolicResult.paths) {
                //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                val link: Tuple2[Array[SymVar], Array[SymVar]] =
                    if (this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], this.symOutput.asInstanceOf[Array[SymVar]])
                    else null

                product(i) = udfPath.conjunctPathEffect(pa, link)
                i += 1
            }
        }
        val input = if (this.symInput.length == 0) udfSymbolicResult.symInput else this.symInput
        new SymbolicResult(this.state, product, this.terminating, input, udfSymbolicResult.symOutput)
    }

    def reduceByKey(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        assert(this.symOutput.length >= 2, "ReduceByeKey is not Applicable, Effect of previous is not tuple")
        //returns Cartesian product of already existing paths *  set of paths from given udf

        val tempSymOutput = Array(this.symOutput(1))
        val product = new Array[PathEffect](paths.size * udfSymbolicResult.numOfPaths)
        var i = 0
        for (pa <- this.paths) {
            for (udfPath <- udfSymbolicResult.paths) {
                //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                val link: Tuple2[Array[SymVar], Array[SymVar]] =
                    if (this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], tempSymOutput)
                    else null

                product(i) = udfPath.conjunctPathEffect(pa, link)
                i += 1
            }
        }
        val input = if (this.symInput.length == 0) udfSymbolicResult.symInput else this.symInput
        val finalSymOutput = Array(this.symOutput(0)) ++ udfSymbolicResult.symOutput
        new SymbolicResult(this.state, product, this.terminating, input, finalSymOutput)
    }

    def filter(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        val product = new ArrayBuffer[PathEffect]()
        val terminatingPaths = new ArrayBuffer[TerminatingPath]()
        if (this.terminating != null) {
            terminatingPaths ++= this.terminating
        }

        for (udfPath: PathEffect <- udfSymbolicResult.paths) {
            //we need to check the effect to see whether it is a terminating or a non-terminating one
            // if it's terminating effect would be '0'
            if (udfPath.effects.last._2.toString == "0") { //terminating
                val udfTerminating = new TerminatingPath(udfPath.pathConstraint)
                for (pa <- this.paths) {
                    // print(pa.toString+" && "+udfTerminating.toString+" = ")
                    //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                    val link: Tuple2[Array[SymVar], Array[SymVar]] =
                        if (this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], this.symOutput.asInstanceOf[Array[SymVar]])
                        else null

                    val conjuncted = udfTerminating.conjunctPathEffect(pa, link)
                    terminatingPaths.append(conjuncted)
                }

            } else {
                val removedEffect = new PathEffect(udfPath.pathConstraint.deepCopy)
                for (pa <- this.paths) {
                    //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                    val link: Tuple2[Array[SymVar], Array[SymVar]] =
                        if (this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], this.symOutput.asInstanceOf[Array[SymVar]])
                        else null
                    product += removedEffect.conjunctPathEffect(pa, link)
                }
            }
        }

        val input = if (this.symInput.length == 0) udfSymbolicResult.symInput else this.symInput
        //udf symOutput is dis-regarded as it is either false or true
        //and since filter is side-effect free symInput is considered as output of whole
        new SymbolicResult(this.state, product.toArray, terminatingPaths, input, udfSymbolicResult.symInput)
    }

    def join(secondRDD: SymbolicResult): SymbolicResult = {
        JoinSymbolicResult.apply(this.state, this, secondRDD)
    }

    // override def equals(other: Any): Boolean = {
    //     if(other != null && other.isInstanceOf[SymbolicResult]) {
    //         val castedOther = other.asInstanceOf[SymbolicResult]
    //         castedOther.numOfPaths == this.numOfPaths
    //     } else false
    // }

}