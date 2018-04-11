package symexScala

//import sys.process.
import gov.nasa.jpf.Config
import gov.nasa.jpf.JPF
import gov.nasa.jpf.symbc.SymbolicListener

class parseEffectException(message: String, cause: Throwable = null) extends RuntimeException("Effect: "+message, cause) {}

object SymbolicEngine {

    def callSPF(jpfFile: String, symState: SymbolicState): SymbolicResult = {
        println("Running first file: "+jpfFile)
        //>>>>>
        val lastPart = jpfFile.split("/")(jpfFile.count(_ == '/'))
        val fileName = lastPart.substring(0, lastPart.length-4)
        //<<<<<
       val injectedListener = new PathEffectListenerImp()
       val config: Config = JPF.createConfig(Array(jpfFile));
       config.setProperty("symbolic.dp", "no_solver")
       config.getArgs.foreach(println)

       val jpf: JPF = new JPF(config)
       val symbc: SymbolicListener = new SymbolicListener(config, jpf, injectedListener)
       jpf.addListener(symbc)
       jpf.run()

       val udfResult = injectedListener.convertAll(symState, fileName)
       udfResult
    }

    /*
        used for unit testing data flow symbolic execution with "true" as initial path constraint
    */
    def executeDFOperator(symState: SymbolicState, dfName: String, jpfFile: String): SymbolicResult = {
        // val symState = new SymbolicState()
        val init = new SymbolicResult(symState) //non-T: true, T: null
        val udfResult = callSPF(jpfFile, symState)

        dfName match {
            case "map" => init.map(udfResult)
            case "filter" => init.filter(udfResult)
            case _ => throw new NotSupportedRightNow("This data flow operation is yet not supported!")
        }
    }

    /*
        used for join unit testing
    */
    def executeJoinOperator(first: SymbolicResult, second: SymbolicResult): SymbolicResult = {
        val symState = new SymbolicState()
        //val init1 = new SymbolicResult(symState) //non-T: true, T: null
        //val init2 = new SymbolicResult(symState) //non-T: true, T: null

        val result = first.join(second)
        println(result)
        result
    }

    def executeSymbolicDF(opJpfList: Array[Tuple2[String, String]]): SymbolicResult = {
        val symState = new SymbolicState()
        var currentPaths: SymbolicResult = new SymbolicResult(symState)
        //val res = callSPF(opJpfList(0)._2, symState)
        //println(res)

        for((dfName, jpfFile) <- opJpfList) {
            val udfResult = callSPF(jpfFile, symState)
            //println(udfResult)
            //println("--------------")

            currentPaths = dfName match {
                case "map" => currentPaths.map(udfResult)
                case "filter" => currentPaths.filter(udfResult)
                // case "join" =>
                case _ => throw new NotSupportedRightNow("This data flow operation is yet not supported!")
            }

            println("after "+dfName)
            println(currentPaths)
        }
        currentPaths.Z3DIR = "/Users/malig/workspace/git/Test-Minimization-in-Big-Data/z3-master"
        currentPaths.solveWithZ3
        currentPaths
    }

}