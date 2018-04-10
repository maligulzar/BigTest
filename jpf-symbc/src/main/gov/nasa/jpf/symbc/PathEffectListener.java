package gov.nasa.jpf.symbc;

import java.util.List;
import java.util.Vector;

import gov.nasa.jpf.util.Pair;

import gov.nasa.jpf.symbc.numeric.Expression;
import gov.nasa.jpf.symbc.numeric.PathCondition;

public class PathEffectListener {

    private Vector<Pair<PathCondition, List<Expression>>> listOfPairs;
    private Vector<Pair<String, String>> argsInfo;
    private boolean argsInfoAdded;

    public PathEffectListener() {
        listOfPairs = new Vector<Pair<PathCondition, List<Expression>>>();
        argsInfo = new Vector<Pair<String, String>>();
        argsInfoAdded = false;
    }

    public void addPCPair(PathCondition pc, List<Expression> result) {
        Pair<PathCondition, List<Expression>> pePair = new Pair<PathCondition, List<Expression>>(pc, result);
        listOfPairs.add(pePair);
    }

    public Vector<Pair<PathCondition, List<Expression>>> getListOfPairs() {
        return listOfPairs;
    }

    public void addArgsInfo(String varName, String varType) {
        argsInfo.add(new Pair<String, String>(varName, varType));
    }

    public Vector<Pair<String, String>> getArgsInfo() {
        return argsInfo;
    }

    public boolean isArgsInfoAdded() {
        return argsInfoAdded;
    }

    public void argsInfoIsAdded() {
        argsInfoAdded = true;
    }


}