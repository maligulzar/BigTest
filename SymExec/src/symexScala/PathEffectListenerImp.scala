package symexScala

import java.util.Vector
import java.util.Iterator
import gov.nasa.jpf.symbc.PathEffectListener
import gov.nasa.jpf.util.Pair
import gov.nasa.jpf.symbc.numeric.Expression
import gov.nasa.jpf.symbc.numeric.PathCondition
import gov.nasa.jpf.symbc.numeric.IntegerExpression
import gov.nasa.jpf.symbc.arrays.SelectExpression
import gov.nasa.jpf.symbc.numeric.RealExpression
import gov.nasa.jpf.symbc.numeric.BinaryLinearIntegerExpression
import gov.nasa.jpf.symbc.numeric.IntegerConstant
import gov.nasa.jpf.symbc.numeric.SymbolicInteger
import gov.nasa.jpf.symbc.numeric.BinaryRealExpression
import gov.nasa.jpf.symbc.numeric.RealConstant
import gov.nasa.jpf.symbc.numeric.SymbolicReal

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.Map

import NumericUnderlyingType._
import NonNumericUnderlyingType._

class NotSupportedRightNow(message: String, cause: Throwable = null) 
    extends RuntimeException("This is not supported right now: "+message, cause) {}

class PathEffectListenerImp extends PathEffectListener  {

    var allPathEffects: Array[PathEffect] = null
    val argsMap: Map[String, SymVar] = Map[String, SymVar]()  //from old names to instantiations with new names

    def convertRealExpression(lr: RealExpression): Expr = {
        lr match {
            case r: BinaryRealExpression => {
                val left: Expr = convertExpressionToExpr(r.getLeft())     //RealExpression -> Expr
                val right: Expr = convertExpressionToExpr(r.getRight())   //RealExpression -> Expr
                
                var opStr = r.getOp().toString().replaceAll("\\s", "")
                if(opStr != "+" && opStr != "-" && opStr != "*" && opStr != "/") throw new NotSupportedRightNow(opStr)
                val op = new SymOp(Numeric(_Double), ArithmeticOp.withName(opStr))
                new NonTerminal(left, op, right)
            }
            case c: RealConstant => new ConcreteValue(Numeric(_Double), c.toString())
            case s: SymbolicReal => {
                val realVar = argsMap.getOrElse(s.getName(), null)
                if(realVar == null) 
                    new SymVar(Numeric(_Double), s.getName())
                else realVar
            }
            case _ => throw new NotSupportedRightNow(lr.getClass.getName)
        }
    }

    def convertIntegerExpression(li: IntegerExpression): Expr = {
        li match {
            case i: BinaryLinearIntegerExpression => {
                val left: Expr = convertExpressionToExpr(i.getLeft())     //IntegerExpression -> Expr
                val right: Expr = convertExpressionToExpr(i.getRight())   //IntegerExpression -> Expr
                
                var opStr = i.getOp().toString().replaceAll("\\s", "")
                if(opStr != "+" && opStr != "-" && opStr != "*" && opStr != "/") throw new NotSupportedRightNow(opStr)
                val op = new SymOp(Numeric(_Int), ArithmeticOp.withName(opStr))
                new NonTerminal(left, op, right)
            }
            case c: IntegerConstant => new ConcreteValue(Numeric(_Int), c.toString())
            case s: SymbolicInteger => {
                    val intVar = argsMap.getOrElse(s.getName(), null)
                    if(intVar == null) 
                        new SymVar(Numeric(_Int), fixArrayName(s.getName()))
                    else intVar
                }
            case _ => throw new NotSupportedRightNow(li.getClass.getName)
        }
    }
    
    
    def fixArrayName(str: String) : String = {
      if(str.startsWith("[") &&  str.endsWith("]")){
        val s = str.split("\\[")
        val name  = searchInputArrayName(s(1))
        val idx = s(2).replaceAll("\\]", "")
        return name+idx
      }
      return str;
    }

    def searchInputArrayName(name : String) : String = {
      val list:  Vector[Pair[String, String]] = super.getArgsInfo()
      for(  i <- 0  to list.size()){
        if(list.get(i)._2.endsWith("[]")){
          return list.get(i)._1
        }
      }
      return name
    }
    
    def addInArgsMap(str: String , arrname : String) = {
        var link =  argsMap(arrname)
        argsMap.put(str, link)
    }
    
    def convertSelectExpression(li: SelectExpression): Expr = {
     var ar =  li.arrayExpression
     var name  =  searchInputArrayName(ar.getName)
     var i = li.indexExpression
     addInArgsMap(name + convertIntegerExpression(i) , name)
     new SymVar(Numeric(_Int), name + convertIntegerExpression(i) )
     /**
      * The select array operation or array expression needs to be evaluated recursively. 
      * Right now I am assuming that the name of the array is used all the time
      * **/
    }
    
    def convertExpressionToExpr(e: Expression): Expr = {
        e match {
            case li: IntegerExpression => convertIntegerExpression(li)
            //we are not supporting non-linear integer expr for now!

            case lr: RealExpression => convertRealExpression(lr)

            case se: SelectExpression => convertSelectExpression(se)
            
            case _ => throw new NotSupportedRightNow(e.getClass.getName)
        }
    }

    def convertConstraintToClause(cons: gov.nasa.jpf.symbc.numeric.Constraint): Clause = {
        val left: Expr =  convertExpressionToExpr(cons.getLeft())
        val right: Expr = convertExpressionToExpr(cons.getRight())

        var compStr = cons.getComparator().toString().replaceAll("\\s", "")
        //if(compStr == "=") compStr = "=="
        val comp = ComparisonOp.withName(compStr) 

        new Clause (left, comp, right) 
    }

    def convertPathCondition(pc: PathCondition): Constraint = {
        val clauses: ArrayBuffer[Clause] = new ArrayBuffer[Clause]()
        var current = pc.header //: gov.nasa.jpf.symbc.numeric.Constraint
        while(current != null) {
            clauses += convertConstraintToClause(current)

            val next = current.and
            current = next
        }
        var clses  = List[Clause]()
        for((k,v) <- this.argsMap){
          clses = new Clause(new SymVar(Numeric(_Int),k),  
              ComparisonOp.withName("=") ,
              v) ::clses
        }
        new Constraint(clauses.toArray ++ clses)
    }

    /*
        assuming first input argument is our record (which also has the same type as return variable) 
    */
    def convertAll(symState: SymbolicState): SymbolicResult = {
        val pathVector: Vector[Pair[PathCondition, Expression]] = super.getListOfPairs()
        val argsInfo: Vector[Pair[String, String]] = super.getArgsInfo()

        println("------>"+pathVector.size+" "+argsInfo.size)

        val (inputVar: SymVar, outputVar: SymVar) = 
            if(argsInfo.size == 1) {
                val freshVar : SymVar = symState.getFreshSymVar(argsInfo.get(0)._2)
                argsMap += (argsInfo.get(0)._1 -> freshVar)
                (freshVar, symState.getFreshSymVar(argsInfo.get(0)._2))
            }
            else if(argsInfo.size == 2) {
                val freshTuple: SymTuple = symState.getFreshSymTuple(argsInfo.get(0)._2, argsInfo.get(1)._2)
                argsMap += (argsInfo.get(0)._1 -> freshTuple._1)
                argsMap += (argsInfo.get(1)._1 -> freshTuple._2)
                (freshTuple, symState.getFreshSymTuple(argsInfo.get(0)._2, argsInfo.get(1)._2))
            }
            else {
                for(i <- 0 until argsInfo.size) {
                    println(argsInfo.get(i)._1+" "+argsInfo.get(i)._2)
                }
                println("------------"+argsInfo.size+"-------------")
                throw new NotSupportedRightNow("more than 2 input arguments!")
            }

        allPathEffects = new Array[PathEffect](pathVector.size())
        for(i <- 0 until pathVector.size){
            val effectFromSPF: Expr = convertExpressionToExpr(pathVector.get(i)._2)
            val effectBuffer = new ArrayBuffer[Tuple2[SymVar, Expr]]()
            effectBuffer += new Tuple2(outputVar, effectFromSPF)

            allPathEffects(i) = new PathEffect(convertPathCondition(pathVector.get(i)._1), effectBuffer)
        }

        //println(inputVar)
        //println(outputVar)
        //there is no terminating path in the scope of udf
        new SymbolicResult(symState, allPathEffects, null, inputVar, outputVar)
    }

}