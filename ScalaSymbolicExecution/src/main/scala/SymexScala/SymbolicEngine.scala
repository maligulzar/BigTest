package SymexScala

//import sys.process._
import gov.nasa.jpf.JPF
import gov.nasa.jpf.Config
import gov.nasa.jpf.symbc.SymbolicListener

class parseEffectException(message: String, cause: Throwable = null) extends RuntimeException("Effect: "+message, cause) {}

object SymbolicEngine {
    
    def callSPF(jpfFile: String, symState: SymbolicState): SymbolicResult = {
        val injectedListener = new PathEffectListenerImp()
        val config: Config = JPF.createConfig(Array(jpfFile))
        val jpf: JPF = new JPF(config)
        val symbc: SymbolicListener = new SymbolicListener(config, jpf, injectedListener)
        // symbc.registerPathEffectListener(injectedListener)
        jpf.addListener(symbc)
        jpf.run()

        val udfResult = injectedListener.convertAll(symState)
        udfResult
    }

    /*
        used for unit testing data flow symbolic execution with "true" as initial path constraint
    */
    def executeDFOperator(dfName: String, jpfFile: String): SymbolicResult = {
        val symState = new SymbolicState()
        val init = new SymbolicResult(symState) //non-T: true, T: null
        val udfResult = callSPF(jpfFile, symState)
        
        dfName match {
            case "map" => init.map(udfResult)
            case "filter" => init.filter(udfResult)
            case _ => throw new NotSupportedRightNow("This data flow operation is yet not supported!")
        }
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
        
        currentPaths
    }

}