package symexScala

import scala.collection.mutable.ArrayBuffer
import java.util.HashSet
import ComparisonOp._

class UnexpectedInputType(message: String, cause: Throwable = null)
    extends RuntimeException(message, cause) {}

class JoinSymbolicResult(ss: SymbolicState,
    nonTerminatingPaths: Array[PathEffect],
    terminatingPaths: ArrayBuffer[TerminatingPath] = null,
    iVar: Array[SymVar],
    oVar: Array[SymVar])
    extends SymbolicResult(ss, nonTerminatingPaths, terminatingPaths, iVar, oVar) {

    // var joined: Boolean = j

    def getPartial(pc: String, constName: String): String = {
        val x0 = pc.indexOf("x0")
        val partial1 = pc.substring(x0 - 4, x0) + constName + pc.substring(x0 + 2, x0 + 6)

        val x2 = pc.indexOf("x2")
        val partial2 = pc.substring(x2 - 4, x2) + constName + pc.substring(x2 + 2, x2 + 7)
        s"""(assert (and ${partial1} ${partial2}))
        |""".stripMargin
    }

    override def solveWithZ3() = {
        //        var hashCode: Int = 0
        //        var first = ""
        //        var second = ""
        //        var pc = ""
        //        val list: HashSet[(String, VType)] = new HashSet[(String, VType)]();
        //
        //        for (path <- paths) {
        //            pc += (path.pathConstraint.toZ3Query(list)+"\n")
        //
        //            //we use the first seen hashCode to save the whole query!
        //            if(hashCode == 0)
        //                hashCode = path.hashCode
        //        }
        //        for(ters <- terminating) {
        //            pc += (ters.pathConstraint.toZ3Query(list)+"\n")
        //        }
        //
        //        var decls = ""
        //        val itr = list.iterator()
        //        while(itr.hasNext){
        //            val i = itr.next()
        //            if(i._1.indexOf(".") != -1) {
        //                val setName = i._1.substring(0, i._1.indexOf("."))
        //                decls += s"""(declare-fun ${setName} (Int) Bool)"""+"\n"
        //                if(first == "")
        //                    first = setName
        //                else if(second == "")
        //                    second = setName
        //            }
        //            else {
        //                decls +=
        //                s""" (declare-fun ${i._1} () ${i._2.toZ3Query()} )
        //                |""".stripMargin
        //            }
        //        }
        //
        //        var result = ""
        //        result += getPartial(pc, "c1")
        //        result += s"""(assert (and ($first c1) ($second c1) ) )"""+"\n\n"
        //
        //        result += "(declare-const c11 Int)\n"
        //        result += getPartial(pc, "c11")
        //        result += s"""(assert (and ($first c11) ($second c11) ) )"""+"\n\n"
        //
        //        result += "(declare-const c12 Int)\n"
        //        result += getPartial(pc, "c12")
        //        result += s"""(assert (and ($first c12) ($second c12) ) )"""+"\n\n"
        //
        //        result += getPartial(pc, "c2")
        //        result += s"""(assert (and ($first c2) (not ($second c2)) ) )"""+"\n\n"
        //
        //        result += "(declare-const c22 Int)\n"
        //        result += getPartial(pc, "c22")
        //        result += s"""(assert (and ($first c22) (not ($second c22)) ) )"""+"\n\n"
        //
        //        result += "(declare-const c23 Int)\n"
        //        result += getPartial(pc, "c23")
        //        result += s"""(assert (and ($first c23) (not ($second c23)) ) )"""+"\n\n"
        //
        //        result += getPartial(pc, "c3")
        //        result += s"""(assert (and (not ($first c3)) ($second c3) ) )"""+"\n\n"
        //
        //        result += "(declare-const c33 Int)\n"
        //        result += getPartial(pc, "c33")
        //        result += s"""(assert (and (not ($first c33)) ($second c33) ) )"""+"\n\n"
        //
        //        result += "(declare-const c34 Int)\n"
        //        result += getPartial(pc, "c34")
        //        result += s"""(assert (and (not ($first c34)) ($second c34) ) )"""+"\n\n"
        //
        //       // we are the programming languages and compiler and types group
        //
        //        val str = s"""$decls
        //                    |$result
        //                    |(check-sat)
        //                    |(get-model)
        //                    """.stripMargin
        //
        //        var filename = "/tmp/"+hashCode
        //        writeTempSMTFile(filename , str)
        //        println(str)
        //        println("------------------------")
        //        runZ3Command(filename , Z3DIR);
        //        println("------------------------")
    }
}

object JoinSymbolicResult {
    def apply(ss: SymbolicState, rddA: SymbolicResult, rddB: SymbolicResult): JoinSymbolicResult = {
        //Makes sure that A and B both have a more than one element as their symOutput
        require(rddA.symOutput.size > 1 && rddB.symOutput.size > 1)

        val keyA: SymVar = rddA.symOutput(0)
        val keyB: SymVar = rddB.symOutput(0)
        require(keyA.actualType.equals(keyB.actualType))

        //do join
        val product = new Array[PathEffect](rddA.numOfPaths * rddB.numOfPaths)
        val joinedPaths = new Array[PathEffect](rddA.numOfPaths * rddB.numOfPaths)
        val terminatingPaths = new ArrayBuffer[TerminatingPath]()

        if (rddA.terminating != null) {
            terminatingPaths ++= rddA.terminating
        }
        if (rddB.terminating != null) {
            terminatingPaths ++= rddB.terminating
        }

        var i = 0
        for (pA <- rddA.paths) {
            for (pB <- rddB.paths) {
                product(i) = pB.conjunctPathEffect(pA)
                i += 1
            }
        }

        for (i <- 0 until product.length) {
            println("This is the product already!!!")
            println(product(i))
            println("End of product --------------------")
            //***Assuming that the first element of symOutput array is the key***
            //product(i) is the rest of the cluases and we need to replace A.key and B.key with the existential var in this rest!

            //Case 1:
            val c1 = new SymVar(keyA.actualType, ss.getFreshName)
            val replacedC1: PathEffect = product(i).replace(keyA, c1).replace(keyB, c1)

            val existA_B = new ExistentialConstraint(c1, replacedC1.pathConstraint.clauses)
            existA_B.addCluase(ComparisonOp.isIn, keyA)
            existA_B.addCluase(ComparisonOp.isIn, keyB)

            joinedPaths(i) = new PathEffect(existA_B, replacedC1.effects)

            //Case 2: Terminating
            val c2 = new SymVar(keyA.actualType, ss.getFreshName)
            val replacedC2: PathEffect = product(i).replace(keyA, c2).replace(keyB, c2)

            val existA_NotB = new ExistentialConstraint(c2, replacedC2.pathConstraint.clauses)
            existA_NotB.addCluase(ComparisonOp.isIn, keyA)
            existA_NotB.addCluase(ComparisonOp.isNotIn, keyB)

            terminatingPaths += new TerminatingPath(existA_NotB, replacedC2.effects)

            //Case 3: Terminating
            val c3 = new SymVar(keyA.actualType, ss.getFreshName)
            val replacedC3: PathEffect = product(i).replace(keyA, c3).replace(keyB, c3)

            val existNotA_B = new ExistentialConstraint(c3, replacedC3.pathConstraint.clauses)
            existNotA_B.addCluase(ComparisonOp.isNotIn, keyA)
            existNotA_B.addCluase(ComparisonOp.isIn, keyB)

            terminatingPaths += new TerminatingPath(existNotA_B, replacedC3.effects)
        }

        // var result = ""
        // joinedPaths.foreach(result += _.toString+"\n")
        // println(result)

        val input = rddA.symOutput ++ rddB.symOutput
        val output = Array(rddA.symOutput(0)) ++ rddA.symOutput.drop(1) ++ rddB.symOutput.drop(1)

        return new JoinSymbolicResult(ss, joinedPaths, terminatingPaths, input, output)

    }
}