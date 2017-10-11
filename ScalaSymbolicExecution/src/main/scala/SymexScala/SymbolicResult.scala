package SymexScala

import java.io.{BufferedWriter, FileWriter, File}
import java.util

import udfExtractor.Logging.LogType
import udfExtractor.SystemCommandExecutor

import scala.collection.mutable.ArrayBuffer

class NotFoundPathCondition(message: String, cause: Throwable = null) 
    extends RuntimeException("Not found Pa in C(A) for record "+message, cause) {}


/* 
    paths = different paths each being satisfied by an equivalent class of tuples in dataset V
*/
class SymbolicResult(ss: SymbolicState, 
                    nonT: Array[PathEffect],
                    t: ArrayBuffer[TerminatingPath] = null,
                    iVar: SymVar = null,
                    oVar: SymVar = null) {
    var Z3DIR: String = ""    
    val state: SymbolicState = ss
    val paths: Array[PathEffect] = nonT
    val terminating: ArrayBuffer[TerminatingPath] = t
    val symInput: SymVar = iVar
    val symOutput: SymVar = oVar

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

    def writeTempSMTFile(filename: String , z3: String): Unit ={
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
    def runZ3Command(filename: String , Z3dir:String): Unit ={
        // build the system command we want to run
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
        for (path <- paths) {
            var str = path.toZ3Query();
            var filename = "/tmp/"+path.hashCode();
            writeTempSMTFile(filename , str);
            runZ3Command(filename , Z3DIR);
            println("------------------------")
            print(path.toString)
            println(str)
            println("------------------------")

        }
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
                    if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput, this.symOutput)
                    else null

                product(i) = udfPath.conjunctPathEffect(pa, link)
                i += 1
            }
        }
        val input = if(this.symInput == null) udfSymbolicResult.symInput else this.symInput
        new SymbolicResult(this.state, product, this.terminating, input, udfSymbolicResult.symOutput)
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
                        if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput, this.symOutput)
                        else null

                    val conjuncted = udfTerminating.conjunctPathEffect(pa, link)
                    terminatingPaths += conjuncted
                }

            } else {
                val removedEffect = new PathEffect(udfPath.pathConstraint.deepCopy)
                for(pa <- this.paths) {
                    //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                    val link: Tuple2[SymVar, SymVar] = 
                        if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput, this.symOutput)
                        else null
                    product += removedEffect.conjunctPathEffect(pa, link)
                }
            }
        }

        val input = if(this.symInput == null) udfSymbolicResult.symInput else this.symInput
        //udf symOutput is dis-regarded as it is either false or true
        //and since filter is side-effect free symInput is considered as output of whole
        new SymbolicResult(this.state, product.toArray, terminatingPaths, input, udfSymbolicResult.symInput)
    }

    // override def equals(other: Any): Boolean = {
    //     if(other != null && other.isInstanceOf[SymbolicResult]) {
    //         val castedOther = other.asInstanceOf[SymbolicResult]
    //         castedOther.numOfPaths == this.numOfPaths
    //     } else false
    // }

}