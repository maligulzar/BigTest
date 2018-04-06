package symexScala

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.HashMap
import java.util.HashSet
import ComparisonOp._

class UnexpectedInputType(message: String, cause: Throwable = null) 
    extends RuntimeException(message, cause) {}


class JoinSymbolicResult(ss: SymbolicState, 
                    nonTerminatingPaths: Array[PathEffect],
                    terminatingPaths: ArrayBuffer[TerminatingPath] = null,
                    iVar: Tuple2[SymTuple, SymTuple],
                    oVar: Tuple2[SymVar, Tuple2[SymVar, SymVar]]) 
                    extends SymbolicResult(ss, 
                                        nonTerminatingPaths) {

    override val terminating: ArrayBuffer[TerminatingPath] = terminatingPaths
    //TODO: override symInput and symOutput


    //first thing TODO: 
    //2) write toZ3Query for SymTuple and for existential quantifiers -> similar to examples.z3
    //3) add isMemberOF and isNotMemeberOf similar to comparison operator so that we can have c1 member of A.keys -> then generate assert((S1 c1)) for


    def getPartial(pc: String, constName: String): String = {
        val x0 = pc.indexOf("x0")
        val partial1 = pc.substring(x0-4, x0)+constName+pc.substring(x0+2, x0+6)

        val x2 = pc.indexOf("x2")
        val partial2 = pc.substring(x2-4, x2)+constName+pc.substring(x2+2, x2+7)
        s"""(assert (and ${partial1} ${partial2}))
        |""".stripMargin
    }

    override def solveWithZ3() = {
        var hashCode: Int = 0
        var first = ""
        var second = ""
        var pc = ""
         val list: HashSet[(String, VType)] = new HashSet[(String, VType)]();
        val split = new HashMap[String,SplitHandler]();
        val replace = new HashMap[String, String]();
        val state : Z3QueryState = Z3QueryState(list, split, replace)
        
        for (path <- paths) {
            pc += (path.pathConstraint.toZ3Query(state)+"\n")
            
            //we use the first seen hashCode to save the whole query!
            if(hashCode == 0)
                hashCode = path.hashCode
        }
        for(ters <- terminating) {
            pc += (ters.pathConstraint.toZ3Query(state)+"\n")
        }

        var decls = ""
        val itr = state.init.iterator()
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
            else {
                decls +=
                s""" (declare-fun ${i._1} () ${i._2.toZ3Query()} )
                |""".stripMargin
            }
        }

        var result = ""
        result += getPartial(pc, "c1")
        result += s"""(assert (and ($first c1) ($second c1) ) )"""+"\n\n"

        result += "(declare-const c11 Int)\n"
        result += getPartial(pc, "c11")
        result += s"""(assert (and ($first c11) ($second c11) ) )"""+"\n\n"

        result += "(declare-const c12 Int)\n"
        result += getPartial(pc, "c12")
        result += s"""(assert (and ($first c12) ($second c12) ) )"""+"\n\n"

        result += getPartial(pc, "c2")
        result += s"""(assert (and ($first c2) (not ($second c2)) ) )"""+"\n\n"

        result += "(declare-const c22 Int)\n"
        result += getPartial(pc, "c22")
        result += s"""(assert (and ($first c22) (not ($second c22)) ) )"""+"\n\n"

        result += "(declare-const c23 Int)\n"
        result += getPartial(pc, "c23")
        result += s"""(assert (and ($first c23) (not ($second c23)) ) )"""+"\n\n"

        result += getPartial(pc, "c3")
        result += s"""(assert (and (not ($first c3)) ($second c3) ) )"""+"\n\n"

        result += "(declare-const c33 Int)\n"
        result += getPartial(pc, "c33")
        result += s"""(assert (and (not ($first c33)) ($second c33) ) )"""+"\n\n"

        result += "(declare-const c34 Int)\n"
        result += getPartial(pc, "c34")
        result += s"""(assert (and (not ($first c34)) ($second c34) ) )"""+"\n\n"

       // we are the programming languages and compiler and types group

        val str = s"""$decls
                    |$result
                    |(check-sat)
                    |(get-model)
                    """.stripMargin

        var filename = "/tmp/"+hashCode
        writeTempSMTFile(filename , str)
        println(str)
        println("------------------------")
        runZ3Command(filename , Z3DIR);
        println("------------------------")

    }
}


object JoinSymbolicResult {
    def apply(ss: SymbolicState, _A: SymbolicResult, _B: SymbolicResult): JoinSymbolicResult = {
        //Makes sure that A and B both have a SymbolicTuple for their symOutput
        val _ATuple = _A.symOutput match {
            case o: SymTuple => o
            case _ => throw new UnexpectedInputType("First RDD for Join operation")
        }

        val _BTuple = _B.symOutput match {
            case o: SymTuple => o
            case _ => throw new UnexpectedInputType("Second RDD for Join operation")
        }

        //do join
        val product = new Array[PathEffect](_A.numOfPaths * _B.numOfPaths)
        val joinedPaths = new Array[PathEffect](_A.numOfPaths * _B.numOfPaths)
        val terminatingPaths = new ArrayBuffer[TerminatingPath]()

        if(_A.terminating != null) {
            terminatingPaths ++= _A.terminating
        }
        if(_B.terminating != null) {
            terminatingPaths ++= _B.terminating
        }

        var i = 0
        for(pA <- _A.paths) {
            for(pB <- _B.paths) {
                product(i) = pB.conjunctPathEffect(pA)
                i += 1
            }
        }

        for(i <- 0 until product.length) {
            val c1 = new ExistentialConstraint(nextIndex = 1)
            c1.addCluase(_ATuple._1, Equality)
            c1.addCluase(_BTuple._1, Equality)

            //val c1 :Array[Clause] = Array(new Clause(_ATuple._1, Equality, _BTuple._1))
            //val keysEq = new Constraint(c1)
            joinedPaths(i) = product(i).conjunctPathEffect(new PathEffect(c1))

            val c2 = new ExistentialConstraint(nextIndex = 2, isNonExis = true)
            c2.addCluase(_ATuple._1, Equality)
            c2.addCluase(_BTuple._1, Inequality)
            val t1 =  new TerminatingPath(c2)
            terminatingPaths += t1.conjunctPathEffect(product(i))

            val c3 = new ExistentialConstraint(nextIndex = 3, isNonExis = true)
            c3.addCluase(_ATuple._1, Inequality)
            c3.addCluase(_BTuple._1, Equality)
            terminatingPaths += new TerminatingPath(c3).conjunctPathEffect(product(i))
        }

        // var result = ""
        // joinedPaths.foreach(result += _.toString+"\n")
        // println(result)

        val input = new Tuple2(_ATuple, _BTuple)
        val output = new Tuple2(_ATuple._1, new Tuple2(_ATuple._2, _BTuple._2))
        // val input = new SymTuple(Tuple(this.symInput.actualType, secondRDD.symInput.actualType), "x0-x1")
        // val output = new SymTuple(Tuple(Numeric(_Int), Tuple(Numeric(_Int), Numeric(_Int))), "x0.x1")
        return new JoinSymbolicResult(ss, joinedPaths, terminatingPaths, input, output)

    }
}