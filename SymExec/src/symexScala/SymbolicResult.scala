package symexScala

import java.io.{BufferedWriter, File, FileWriter}
import java.util
import java.util.HashSet

import scala.collection.mutable.ArrayBuffer
import NumericUnderlyingType._
import ComparisonOp._
import ArithmeticOp._ 
import udfExtractor.SystemCommandExecutor

class NotFoundPathCondition(message: String, cause: Throwable = null) 
    extends RuntimeException("Not found Pa in C(A) for record "+message, cause) {}


/* 
    paths = different paths each being satisfied by an equivalent class of tuples in dataset V
*/
class SymbolicResult(ss: SymbolicState, 
                    nonT: Array[PathEffect],
                    t: ArrayBuffer[TerminatingPath] = null,
                    iVar: Array[SymVar] = Array(),
                    oVar: Array[SymVar] = Array(),
                    j: Boolean = false) {
    var Z3DIR: String = "/Users/amytis/Projects/z3-master"   
    var SOLVER: String = "Z3"   
    val state: SymbolicState = ss
    val paths: Array[PathEffect] = nonT
    val terminating: ArrayBuffer[TerminatingPath] = t
    var symInput: Array[SymVar]  = iVar
    var symOutput: Array[SymVar] = oVar

    var joined: Boolean = j

    def this(ss: SymbolicState) {
        this(ss, new Array[PathEffect](1))
        paths(0) = new PathEffect(new Constraint()) //true
    }

    def setZ3Dir(path:String){
      Z3DIR =  path
    }
    def setSolver(path:String){
      SOLVER =  path
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

   def runZ3Command(filename: String , Z3dir:String , args: Array[String] = Array()): String = {
        // build the system command we want to run
          var s = ""
          if(SOLVER.equals("CVC4")){   
                  s = "/Users/malig/Downloads/cvc4-1.5/builds/x86_64-apple-darwin16.7.0/production/bin/cvc4 --strings-exp --lang smt2 < " + filename
            
          }else {
                s = "python "+Z3dir+"runZ3.py " + filename
          }
     
        for(a <- args){
          s = s +"  " + a 
        }
             println("run z3 for file "+ s)
        try {
            val commands: util.List[String] = new util.ArrayList[String]
            commands.add("/bin/sh")
            commands.add("-c")
            commands.add(s)
            val commandExecutor: SystemCommandExecutor = new SystemCommandExecutor(commands, Z3dir)
            val result: Int = commandExecutor.executeCommand();
            val stdout: java.lang.StringBuilder = commandExecutor.getStandardOutputFromCommand
            val stderr: java.lang.StringBuilder = commandExecutor.getStandardErrorFromCommand
            println("********** Satisfying Assigments **********************************************")
            println(stdout.toString)
            println("*******************************************************************************")
            
            println("\n" + stderr.toString)
            return stdout.toString()
        }
        catch {
            case e: Exception => {
                e.printStackTrace
            }
        }
        return "";
    }


    def solveWithZ3(): Unit = {
        var first = ""
        var second = ""
        if(joined == false) {
          println("Non - Terminating")  
          for (path <- paths) {
                var str = path.toZ3Query();
                if(SOLVER.equals("CVC4")){
                  str = str + "\n(check-sat)\n(get-model)"
                }
                var filename = "/tmp/"+path.hashCode();
                writeTempSMTFile(filename , str);   
                println(path.toString)
                println("Z3Query:\n"+str)
                println("------------------------")
                runZ3Command(filename , Z3DIR);
                println("------------------------")

            }
            println("Terminating")
            for (path <- terminating) {
                var str = path.toZ3Query();
                var filename = "/tmp/"+path.hashCode();
                if(SOLVER.equals("CVC4")){
                  str = str + "\n(check-sat)\n(get-model)"
                }
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
        val product_terminating = ArrayBuffer.fill((paths.size * udfSymbolicResult.numOfTerminating) + numOfTerminating)(new TerminatingPath(new Constraint()))
        var i = 0 
        var j = 0;
        var terminatingPaths = new ArrayBuffer[TerminatingPath]()
        if(this.terminating != null) {
            for(tp <- this.terminating){
              product_terminating(j) = tp
              j+=1
            }

        }
        
        for(pa <- this.paths) {
            for(udfPath <- udfSymbolicResult.paths) {
                //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                 val link: Tuple2[Array[SymVar], Array[SymVar]] = 
                    if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], this.symOutput.asInstanceOf[Array[SymVar]])
                    else null


                product(i) = udfPath.conjunctPathEffect(pa, link)
                i += 1
            }
        }
        
        
        for(pa <- this.paths) {
            for(udfPath <- udfSymbolicResult.terminating) {
                //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                val link: Tuple2[Array[SymVar], Array[SymVar]] = 
                    if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], this.symOutput.asInstanceOf[Array[SymVar]])
                    else null


                product_terminating(j) = udfPath.conjunctPathEffect(pa, link)
                j += 1
            }
        }
        
        
        val input = if(this.symInput.length == 0) udfSymbolicResult.symInput else this.symInput
        new SymbolicResult(this.state, product, product_terminating, input, udfSymbolicResult.symOutput)
    }

    
    
    def reduce(udfSymbolicResult: SymbolicResult): SymbolicResult = {
        //returns Cartesian product of already existing paths *  set of paths from given udf
        val product = new Array[PathEffect](paths.size * udfSymbolicResult.numOfPaths)
        
          var arr_name = ss.getFreshName
        var arr_type =this.symOutput(0).actualType
        var type_name  = arr_type match {
            case NonNumeric(t) =>            
              CollectionNonNumeric(t)
            case Numeric(t) =>  
              CollectionNumeric(t)
            case _ => throw new UnsupportedOperationException("Not Supported Type " + arr_type.toString() )
          }
        val symarray = new SymArray(type_name, arr_name)  
        val arr_op_non = new SymArrayOp(type_name, ArrayOp.withName("select")) ///*** TODO: Only supporting Arrays of Integers
        val arr_0 = new ArrayExpr(symarray ,arr_op_non, Array(new ConcreteValue(Numeric(_Int) , "0")))
        val arr_1 = new ArrayExpr(symarray ,arr_op_non, Array(new ConcreteValue(Numeric(_Int) , "1")))
 
        var i = 0  
        for(pa <- this.paths) {
            for(udfPath <- udfSymbolicResult.paths) {
                //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                val link: Tuple2[Array[SymVar], Array[SymVar]] = 
                    if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], Array(symarray))
                    else null

                product(i) = udfPath.conjunctPathEffect(pa, link)
                product(i) = product(i).addOneToN_Mapping(this.symOutput(0), Array(arr_0, arr_1))
                i += 1
            }
        }
        val input = if(this.symInput.length == 0) udfSymbolicResult.symInput else this.symInput
        new SymbolicResult(this.state, product, this.terminating, input, udfSymbolicResult.symOutput)
    }
        
        def reduceByKey(udfSymbolicResult: SymbolicResult): SymbolicResult = {
          assert(this.symOutput.length>=2 , "ReduceByeKey is not Applicable, Effect of previous is not tuple")
        //returns Cartesian product of already existing paths *  set of paths from given udf
          
        val tempSymOutput = Array(this.symOutput(1))
       
        var arr_name = ss.getFreshName
        var arr_type =this.symOutput(1).actualType
        var type_name  = arr_type match {
            case NonNumeric(t) =>            
              CollectionNonNumeric(t)
            case Numeric(t) =>  
              CollectionNumeric(t)
            case _ => throw new UnsupportedOperationException("Not Supported Type " + arr_type.toString() )
          }
        val symarray = new SymArray(type_name, arr_name)  
        val arr_op_non = new SymArrayOp(type_name, ArrayOp.withName("select")) ///*** TODO: Only supporting Arrays of Integers
        val arr_0 = new ArrayExpr(symarray ,arr_op_non, Array(new ConcreteValue(Numeric(_Int) , "0")))
        val arr_1 = new ArrayExpr(symarray ,arr_op_non, Array(new ConcreteValue(Numeric(_Int) , "1")))
 
          
        val product = new Array[PathEffect](paths.size * udfSymbolicResult.numOfPaths)
        var i = 0  
        for(pa <- this.paths) {
            for(udfPath <- udfSymbolicResult.paths) {
                //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                val link: Tuple2[Array[SymVar], Array[SymVar]] = 
                    if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], Array(symarray))
                    else null

                product(i) = udfPath.conjunctPathEffect(pa, link)
                product(i) = product(i).addOneToN_Mapping(this.symOutput(1), Array(arr_0, arr_1))
                i += 1
            }
        }
        val input = if(this.symInput.length == 0) udfSymbolicResult.symInput else this.symInput
        val finalSymOutput = Array(this.symOutput(0)) ++ udfSymbolicResult.symOutput
        new SymbolicResult(this.state, product, this.terminating, input, finalSymOutput)
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
                    val link: Tuple2[Array[SymVar], Array[SymVar]] = 
                    if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], this.symOutput.asInstanceOf[Array[SymVar]])
                    else null

                    val conjuncted = udfTerminating.conjunctPathEffect(pa, link)
                    terminatingPaths.append(conjuncted)
                }

            } else {
                val removedEffect = new PathEffect(udfPath.pathConstraint.deepCopy)
                for(pa <- this.paths) {
                    //udf -> (x2, x3) / rdd -> (x0, x1) => link -> (x2 = x1)
                    val link: Tuple2[Array[SymVar], Array[SymVar]] = 
                        if(this.symOutput != null) new Tuple2(udfSymbolicResult.symInput.asInstanceOf[Array[SymVar]], this.symOutput.asInstanceOf[Array[SymVar]])
                        else null
                    product += removedEffect.conjunctPathEffect(pa, link)
                }
            }
        }

        val input = if(this.symInput.length == 0) udfSymbolicResult.symInput else this.symInput
        //udf symOutput is dis-regarded as it is either false or true
        //and since filter is side-effect free symInput is considered as output of whole
        new SymbolicResult(this.state, product.toArray, terminatingPaths, input, udfSymbolicResult.symInput)
    }

    def join(secondRDD: SymbolicResult): SymbolicResult = {
      JoinSymbolicResult.apply(this.state, this, secondRDD)
      
    }
    
    
    
    // We need to spawn new branch to link the input of this operation to the output
    // E.g Input  : V -->  Output : [V1 ,V2] Such that V1 ==V, and V2 ==V 
      def groupByKey(): SymbolicResult = {
          assert(this.symOutput.length>=2 , "GroupByKey is not Applicable, Effect of previous is not tuple")
        val product = new Array[PathEffect](paths.size)
        var i = 0  
        var arr_name = ss.getFreshName
        var arr_type =this.symOutput(1).actualType
        var type_name  = arr_type match {
            case NonNumeric(t) =>            
              CollectionNonNumeric(t)
            case Numeric(t) =>  
              CollectionNumeric(t)
            case _ => throw new UnsupportedOperationException("Not Supported Type " + arr_type.toString() )
          }
        val symarray = new SymArray(type_name, arr_name)
        for(pa <- this.paths) {
                //(x0, x1) -> (x2, [x3,x4] )  => link -> (x0 = x2) && (x1 = x3 , x4 = x1)
                
                val arr_op_non = new SymArrayOp(type_name, ArrayOp.withName("select")) ///*** TODO: Only supporting Arrays of Integers
                val arr_0 = new ArrayExpr(symarray ,arr_op_non, Array(new ConcreteValue(Numeric(_Int) , "0")))
                val arr_1 = new ArrayExpr(symarray ,arr_op_non, Array(new ConcreteValue(Numeric(_Int) , "1")))
 
                //TODO: *****THIS IS WHERE WE NEED TO SPAWN A NEW LINK TO CONSTRUCT 1-N MAPPING BETWEEN INPUT AND OUTPUT
                product(i) = pa.addOneToN_Mapping(this.symOutput(1), Array(arr_0, arr_1))
                //*******
                i += 1
        }
        val input = this.symOutput
        val finalSymOutput = Array(this.symOutput(0)) ++ Array(symarray)
        new SymbolicResult(this.state, product, this.terminating, input, finalSymOutput)
    }

    // override def equals(other: Any): Boolean = {
    //     if(other != null && other.isInstanceOf[SymbolicResult]) {
    //         val castedOther = other.asInstanceOf[SymbolicResult]
    //         castedOther.numOfPaths == this.numOfPaths
    //     } else false
    // }

}