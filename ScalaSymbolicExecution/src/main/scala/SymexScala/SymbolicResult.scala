package SymexScala

import java.io.{BufferedWriter, FileWriter, File}
import java.util
import java.util.HashSet
import scala.collection.mutable.ArrayBuffer

import udfExtractor.Logging.LogType
import udfExtractor.SystemCommandExecutor

import NumericUnderlyingType._
import ComparisonOp._
import ArithmeticOp._

class NotFoundPathCondition(message: String, cause: Throwable = null) 
    extends RuntimeException("Not found Pa in C(A) for record "+message, cause) {}


/* 
    paths = different paths each being satisfied by an equivalent class of tuples in dataset V
*/
class SymbolicResult(ss: SymbolicState, 
                    nonT: Array[PathEffect],
                    t: ArrayBuffer[TerminatingPath] = null,
                    iVar: Expr = null,
                    oVar: Expr = null,
                    j: Boolean = false) {
    var Z3DIR: String = "/Users/amytis/Projects/z3-master"   
    val state: SymbolicState = ss
    val paths: Array[PathEffect] = nonT
    val terminating: ArrayBuffer[TerminatingPath] = t
    var symInput: Expr = iVar
    var symOutput: Expr = oVar

    var joined: Boolean = j

    def this(ss: SymbolicState) {
        this(ss, new Array[PathEffect](1))
        paths(0) = new PathEffect(new Constraint()) //true
    }

    override def toString: String = {
        var result = "Set of Constraints for this dataset V:\nNon-terminating:\n"
        paths.foreach(result += _.toString+"\n")

        if(terminating != null) {
            result += "terminating:\n"
            terminating.foreach(result += _.toString+"\n")
        }

        result
    }

    def writeTempSMTFile(filename: String , z3: String): Unit = {
       try {
           val file: File = new File(filename)
           if (!file.exists) {
               file.createNewFile
           }
           val fw: FileWriter = new FileWriter(file)
           val bw = new BufferedWriter(fw)
           bw.write(z3);
           bw.close();
       } catch{
             case ex: Exception =>
                ex .printStackTrace();
        }
    }

    def runZ3Command(filename: String , Z3dir:String): Unit = {
        // build the system command we want to run
        println("run z3 for filename "+filename)
        val s: String = Z3dir+"/build/z3 -smt2 " + filename
        try {
            val commands: util.List[String] = new util.ArrayList[String]
            commands.add("/bin/sh")
            commands.add("-c")
            commands.add(s)
            val commandExecutor: SystemCommandExecutor = new SystemCommandExecutor(commands, Z3dir)
            val result: Int = commandExecutor.executeCommand();
            val stdout: java.lang.StringBuilder = commandExecutor.getStandardOutputFromCommand
            val stderr: java.lang.StringBuilder = commandExecutor.getStandardErrorFromCommand
            println("Model --> \n" + stdout.toString)
        }
        catch {
            case e: Exception => {
                e.printStackTrace
            }
        }
    }
    def solveWithZ3(): Unit = {
        var first = ""
        var second = ""
        if(joined == false) {
            for (path <- paths) {
                var str = path.toZ3Query();
                var filename = "/tmp/"+path.hashCode();
                writeTempSMTFile(filename , str);
                println(path.toString)
                println("Z3Query:\n"+str)
                println("------------------------")
                runZ3Command(filename , Z3DIR);
                println("------------------------")

            }
        } 
        /*else {
            val path = paths(0)
            println(path)

            val list: HashSet[(String, VType)] = new HashSet[(String, VType)]();
            val pc = path.pathConstraint.toZ3Query(list)
            var decls = ""
            val itr = list.iterator()
            while(itr.hasNext){
                val i = itr.next()
                if(i._1.indexOf(".") != -1) {
                    val setName = i._1.substring(0, i._1.indexOf("."))
                    decls += s"""(declare-fun ${setName} (Int) Bool)"""+"\n"
                    if(first == "")
                        first = setName
                    else if(second == "")
                        second = setName
                }
                // else {
                //     decls +=
                //     s""" (declare-fun ${i._1} () ${i._2.toZ3Query()} )
                //     |""".stripMargin
                // }
            }

            var result = ""
            result += "(declare-const c1 Int)\n"
            result += getPartial(pc, "c1")
            result += s"""(assert (and ($first c1) ($second c1) ) )"""+"\n\n"

            result += "(declare-const c2 Int)\n"
            result += getPartial(pc, "c2")
            result += s"""(assert (and ($first c2) (not ($second c2)) ) )"""+"\n\n"

            result += "(declare-const c3 Int)\n"
            result += getPartial(pc, "c3")
            result += s"""(assert (and (not ($first c3)) ($second c3) ) )"""+"\n\n"

            val str = s"""$decls
                        |$result
                        |(check-sat)
                        |(get-model)
                        """.stripMargin

            var filename = "/tmp/"+path.hashCode();
            writeTempSMTFile(filename , str);
            println(path.toString)
            println("Z3Query:\n"+str)
            println("------------------------")
            runZ3Command(filename , Z3DIR);
            println("------------------------")
        }*/

    }

    def numOfPaths: Int = {paths.size}

    def numOfTerminating: Int = {
        if(terminating != null) terminating.size
        else 0
    }

    def map(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        //returns Cartesian product of already existing paths *  set of paths from given udf
        val product = new Array[PathEffect](paths.size * udfSymbolicResult.numOfPaths)
        var i = 0  
        for(pa <- this.paths) {
            for(udfPath <- udfSymbolicResult.paths) {
                //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                val link: Tuple2[SymVar, SymVar] = 
                    if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[SymVar], this.symOutput.asInstanceOf[SymVar])
                    else null

                product(i) = udfPath.conjunctPathEffect(pa, link)
                i += 1
            }
        }
        val input = if(this.symInput == null) udfSymbolicResult.symInput.asInstanceOf[SymVar] else this.symInput.asInstanceOf[SymVar]
        new SymbolicResult(this.state, product, this.terminating, input, udfSymbolicResult.symOutput.asInstanceOf[SymVar])
    }

    def filter(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        val product = new ArrayBuffer[PathEffect]()
        val terminatingPaths = new ArrayBuffer[TerminatingPath]()
        if(this.terminating != null) {
            terminatingPaths ++= this.terminating
        }

        for(udfPath: PathEffect <- udfSymbolicResult.paths) {
            //we need to check the effect to see whether it is a terminating or a non-terminating one
            // if it's terminating effect would be '0'
            if(udfPath.effects.last._2.toString == "0") { //terminating
                val udfTerminating = new TerminatingPath(udfPath.pathConstraint)
                for(pa <- this.paths) {
                    // print(pa.toString+" && "+udfTerminating.toString+" = ")
                    //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                    val link: Tuple2[SymVar, SymVar] = 
                        if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[SymVar], this.symOutput.asInstanceOf[SymVar])
                        else null

                    val conjuncted = udfTerminating.conjunctPathEffect(pa, link)
                    terminatingPaths += conjuncted
                }

            } else {
                val removedEffect = new PathEffect(udfPath.pathConstraint.deepCopy)
                for(pa <- this.paths) {
                    //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                    val link: Tuple2[SymVar, SymVar] = 
                        if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[SymVar], this.symOutput.asInstanceOf[SymVar])
                        else null
                    product += removedEffect.conjunctPathEffect(pa, link)
                }
            }
        }

        val input = if(this.symInput == null) udfSymbolicResult.symInput.asInstanceOf[SymVar] else this.symInput.asInstanceOf[SymVar]
        //udf symOutput is dis-regarded as it is either false or true
        //and since filter is side-effect free symInput is considered as output of whole
        new SymbolicResult(this.state, product.toArray, terminatingPaths, input, input)
    }

    def join(secondRDD: SymbolicResult): SymbolicResult = {
        val product = new Array[PathEffect](paths.size * secondRDD.numOfPaths)

        val joinedPaths = new Array[PathEffect](paths.size * secondRDD.numOfPaths)

        val terminatingPaths = new ArrayBuffer[TerminatingPath]()
        if(this.terminating != null) {
            terminatingPaths ++= this.terminating
        }
        if(secondRDD.terminating != null) {
            terminatingPaths ++= secondRDD.terminating
        }

        var i = 0  
        for(pa <- this.paths) {
            for(secondPath <- secondRDD.paths) {
                //TODO: rdd -> (x0, x1) and second -> (x2, x3) => link -> ???
                val link: Tuple2[SymVar, SymVar] = null
                product(i) = secondPath.conjunctPathEffect(pa, link)
                i += 1
            }
        }
          
        for(i <- 0 until product.length) {
            val c1 :Array[Clause] = Array(new Clause(this.symOutput.asInstanceOf[SymTuple]._1,Equality,
                                                    secondRDD.symOutput.asInstanceOf[SymTuple]._1))
            val keysEq = new Constraint(c1)
            joinedPaths(i) = product(i).conjunctPathEffect(new PathEffect(keysEq), null)

            val c2 :Array[Clause] = Array(new Clause(this.symOutput.asInstanceOf[SymTuple]._1,Inequality,
                                                    secondRDD.symOutput.asInstanceOf[SymTuple]._1))
            
            // terminatingPaths += product(i).conjunctPathEffect(new TerminatingPath(new Constraint(c2)))
            terminatingPaths += new TerminatingPath(new Constraint(c2)).conjunctPathEffect(product(i))
        }


        val input = new SymTuple(Tuple(this.symInput.actualType, secondRDD.symInput.actualType), "x0-x1")
        val output = new SymTuple(Tuple(Numeric(_Int), Tuple(Numeric(_Int), Numeric(_Int))), "x0.x1")
        // val input = if(this.symInput == null) udfSymbolicResult.symInput else this.symInput
        return new SymbolicResult(this.state, joinedPaths, terminatingPaths, input, output, true)
    }

    // override def equals(other: Any): Boolean = {
    //     if(other != null && other.isInstanceOf[SymbolicResult]) {
    //         val castedOther = other.asInstanceOf[SymbolicResult]
    //         castedOther.numOfPaths == this.numOfPaths
    //     } else false
    // }

}