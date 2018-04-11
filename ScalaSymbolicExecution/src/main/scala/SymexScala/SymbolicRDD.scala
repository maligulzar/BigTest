package symexScala

class SymbolicRDD(/*ofType: VType, */name: String, es: Array[SymVar]) {
    //val actualType = RDD<ofType>
    val elements: Array[SymVar] = es

    def aggregateOnRDD(effect: NonTerminal): NonTerminal = {
        //SymVar, Expr -> Expr
        val l = 
            if(effect.left.isInstanceOf[SymVar]) effect.left.applyEffect(effect.left.asInstanceOf[SymVar], elements(0))  
            else null

        val r = 
            if(effect.right.isInstanceOf[SymVar]) effect.right.applyEffect(effect.right.asInstanceOf[SymVar], elements(1))  
            else null

        // val root = new NonTerminal(l, effect.middle, r)
        
        updateTree(effect, elements.head, elements.tail).asInstanceOf[NonTerminal]
    }

    def updateTree(effect:NonTerminal, root: Expr, rdd: Array[SymVar]): Expr = {
        if(rdd.size > 0) {
            val newRoot = new NonTerminal(root, effect.middle, rdd.head)
            updateTree(effect, newRoot, rdd.tail)    
        }
        else root
    }
}