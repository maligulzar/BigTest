package SymexScala

import SymexScala.

class SymbolicEngine {
    def run(source: String): PathConstraint = {
        //parse source code to create AST
        //lift UDFs off the tree
        //create constraints and symbolic output based on the AST
        //return final path constraints and corresponding symbolic outputs
        return new MapPathConstraint(new Array[PathConstraint](), new Constraint("true"))
    }
}