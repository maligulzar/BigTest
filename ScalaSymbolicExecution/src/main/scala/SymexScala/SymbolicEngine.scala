package SymexScala

import org.apache.spark.rdd._
import sys.process._

class parseEffectException(message: String, cause: Throwable = null) extends RuntimeException("Effect: "+message, cause) {}

object SymbolicEngine {

    var afterMap: SymbolicResult = null
    val currentState: SymbolicState = new SymbolicState()

    def run(source: String, testId: Int): SymbolicResult = {
        //1) parse source code to create AST
        //2) lift UDFs off the tree
        //3) run SPF on lifted udfs to get their path constraints
        // val result: String = "java -cp .:../../jpf/jpf-symbc/build/jpf-symbc-classes.jar -jar ../../jpf/jpf-core/build/RunJPF.jar spf/UDF.jpf".!!
        // //4) call SymbolicResult spark operation APIs according to the source code operations
        // //   to get the final set of path constraints for whole program

        val c1 = Constraint.parseConstraint("x > 100")
        val path1 = new PathAndEffect(c1)

        val c2 = Constraint.parseConstraint("x <= 100")
        val e2 = SymbolicEngine.parseEffect("x = 0;")
        val path2 = new PathAndEffect(c2, e2)

        val allMapPaths = new Array[PathAndEffect](2)
        allMapPaths(0) = path1
        allMapPaths(1) = path2

        val mapSymbolicResult = new SymbolicResult(allMapPaths)
        
        //filter UDF
        val c3 = Constraint.parseConstraint("x%2 == 0")
        val path3 = new PathAndEffect(c3)
        
        val nonTpaths = new Array[PathAndEffect](1)
        nonTpaths(0) = path3

        val c4 = Constraint.parseConstraint("x%2 != 0")
        val path4 = new TerminatingPath(c4)
        
        val terminPaths = new Array[TerminatingPath](1)
        terminPaths(0) = path4

        val filterSymbolicResult = new SymbolicResult(nonTpaths, terminPaths)

        //second Map UDF
        val c5 = Constraint.parseConstraint("x < 200")
        val e5 = SymbolicEngine.parseEffect("x = -200;")
        val path5 = new PathAndEffect(c5, e5)

        val c6 = Constraint.parseConstraint("x >= 200")
        val path6 = new PathAndEffect(c6)

        val allMap2Paths = new Array[PathAndEffect](2)
        allMap2Paths(0) = path5
        allMap2Paths(1) = path6

        if(testId == 1) {
            new SymbolicResult(allMapPaths)
        }
        else if(testId == 2) {
            val resultPaths = new Array[PathAndEffect](2)
            resultPaths(0) = path1.conjunctWith(path3)
            resultPaths(1) = path2.conjunctWith(path3)
            
            val terminatingResPaths = new Array[TerminatingPath](2)
            terminatingResPaths(0) = path1.conjunctWith(path4).asInstanceOf[TerminatingPath]
            terminatingResPaths(1) = path2.conjunctWith(path4).asInstanceOf[TerminatingPath]
            return new SymbolicResult(resultPaths, terminatingResPaths)
        }
        else {
            val resultPaths = new Array[PathAndEffect](2)
            resultPaths(0) = path1.conjunctWith(path3).conjunctWith(path5)
            resultPaths(1) = path2.conjunctWith(path3).conjunctWith(path5)
            
            val terminatingResPaths = new Array[TerminatingPath](2)
            terminatingResPaths(0) = path1.conjunctWith(path4).asInstanceOf[TerminatingPath]
            terminatingResPaths(1) = path2.conjunctWith(path4).asInstanceOf[TerminatingPath]
            return new SymbolicResult(resultPaths, terminatingResPaths)
        }
        

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