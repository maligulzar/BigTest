package SymexScala

//import sys.process._
import gov.nasa.jpf.JPF
import gov.nasa.jpf.Config
import gov.nasa.jpf.symbc.SymbolicListener

class parseEffectException(message: String, cause: Throwable = null) extends RuntimeException("Effect: "+message, cause) {}

object SymbolicEngine {

    val currentState: SymbolicState = new SymbolicState()
    
    def callSPF(jpfFile: String): SymbolicResult = {
        val injectedListener = new PathEffectListenerImp()
        val config: Config = JPF.createConfig(Array(jpfFile))
        val jpf: JPF = new JPF(config)
        val symbc: SymbolicListener = new SymbolicListener(config, jpf, injectedListener)
        // symbc.registerPathEffectListener(injectedListener)
        jpf.addListener(symbc)
        jpf.run()

        val udfResult = injectedListener.convertAll("x")
        udfResult
    }

    /*
        used for unit testing data flow symbolic execution with "true" as initial path constraint
    */
    def executeDFOperator(dfName: String, jpfFile: String): SymbolicResult = {
        val init = new SymbolicResult(new SymbolicState()) //non-T: true, T: null
        val udfResult = callSPF(jpfFile)
        
        dfName match {
            case "map" => init.map(udfResult)
            case "filter" => init.filter(udfResult)
            case _ => throw new NotSupportedRightNow("This data flow operation is yet not supported!")
        }
    }

    def executeSymbolicDF(opJpfList: Array[Tuple2[String, String]]): SymbolicResult = {
        var currentPaths: SymbolicResult = new SymbolicResult(new SymbolicState())

        for((dfName, jpfFile) <- opJpfList) {
            val udfResult = callSPF(jpfFile)
            //println(udfResult)
            //println("--------------")

            currentPaths = dfName match {
                case "map" => currentPaths.map(udfResult)
                case "filter" => currentPaths.filter(udfResult)
                case _ => throw new NotSupportedRightNow("This data flow operation is yet not supported!")
            }

            println("after "+dfName)
            println(currentPaths)
        }

        currentPaths
    }

    def parseEffect(effectStr: String): Tuple2[SymVar, Expr] = {
        if(effectStr == null || effectStr == "")
            return null

        val part = effectStr.replaceAll("\\s", "")
        // if(parts.size == 0)
        //     throw new parseEffectException(effectStr)

        var parsed: Tuple2[SymVar, Expr] = null
        //could do it with scala map from array(parts) to an array(parsedArr)
        
        val assignIndex = part.indexOf("=")
        val leftHand = currentState.getSymVar(part.substring(0, assignIndex))
        // println("l: "+leftHand)
        val expr = Constraint.parseExpr(part.substring(assignIndex + 1))
        // println("expr: "+expr)

        if(leftHand != null /*&& expr.checkValidity(currentState)*/) {
            parsed = (leftHand, expr)
        }
        else throw new parseEffectException(part)

        parsed
    }

    def defineVar(varName: String, varType: VType): String = {
        if(currentState.getSymVar(varName) == null) {
            currentState.updateVarInEnv(varName, varType, null)
            varName
        }
        else "" //has to redefine with another name also keep the oldName and return new Name!
    }
}