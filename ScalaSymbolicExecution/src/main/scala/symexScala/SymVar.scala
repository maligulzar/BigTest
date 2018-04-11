package symexScala


class SymVar(atype: VType, name: String) extends Terminal {

    override var actualType = atype
      /**
     * Setting types of the newly introduced return variable in the effect
     * */
    def setType(_type:VType) {
      actualType = _type
    }
    def getName: String = {name}

    override def toString: String = { name /*+": "+actualType*/ }

    override def applyEffect(x: SymVar, effect: Expr): Expr = {
        if (this.equals(x)) effect
        else this //TODO TEST: may need to do a deep-copy instead of returning the same instance, in case of further effects
    }

    override def checkValidity(ss: SymbolicState): Boolean = {
        ss.isDefined(this)
    }

    override def toZ3Query(initials:Z3QueryState): String = {
        var temp_name = name.replaceAll("[^A-Za-z0-9]","")
        initials.addtoInit((temp_name , actualType))
        temp_name
    }

    override def deepCopy: SymVar = {
        new SymVar(actualType, name)
    }

    override def replace(thisVar: SymVar, other: SymVar): SymVar = {
        if(this.equals(thisVar)) other
        else this
    }

    override def equals(that: Any): Boolean = that match {
        case that: SymVar => this.actualType == that.actualType && this.name == that.getName
        case _ => false
    }
}


//case class SymTuple(ttype: Tuple, name: String) extends SymVar(ttype,name) {
//    //val actualType = ttype
//
//    val _1: SymVar = new SymVar(ttype._1Type, name+".key")
//    val _2: SymVar = new SymVar(ttype._2Type, name+".val")
//
//    def getFirst: SymVar = {_1}
//    def getSecond: SymVar = {_2}
//
//    override def toString: String = name+"=("+_1.getName+", "+_2.getName+")"
//
//    //TODO: update this for tuple
//    override def applyEffect(x: SymVar, effect: Expr): Expr = {
//        if (this.equals(x)) effect
//        else this
//    }
//
//    override def checkValidity(ss: SymbolicState): Boolean = {
//        ss.isDefined(_1)
//        ss.isDefined(_2)
//    }
//
//    override def toZ3Query(initials :Z3QueryState): String = {""}
//
//    override def deepCopy: SymTuple = {
//        new SymTuple(actualType.asInstanceOf[Tuple], name)
//    }
//
//
//}
