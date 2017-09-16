package udfExtractor;

public class JPFDAGNode{
     String operator_name ;
     String jpf_file;

     public JPFDAGNode(String op, String file){
         operator_name  = op;
         jpf_file = file;
     }

     public String getOperatorName() {
        return operator_name;
     }

     public String getJPFFileName() {
        return jpf_file;
     }
 }