package udfExtractor;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Set;


public class UDFWriter {
    String filename = null;
    BufferedWriter bw = null;
    HashMap<String, String> functions = new HashMap<>();
    String argsToMain = null;
    public UDFWriter(String filen , String argsmain) {
        argsToMain = argsmain;
        try {

            filename = filen.replace("$" , "");
            String arr[] = filename.split("/");
            String file_name = arr[arr.length-1];
            File file = new File(filename);
            filename=file_name;
            if (!file.exists()) {
                file.createNewFile();
            }
            FileWriter fw = new FileWriter(file);
            bw = new BufferedWriter(fw);
           // bw.write(skeleton);
        } catch (Exception ex) {
            ex.printStackTrace();
        }
    }


    public void enrollFunction(String name, String code ){
        functions.put(name, code);
    }
    public void write(Set<String> used_func , String target_func , SparkProgramVisitor visitor) {
        String wrapper_func_body = "";
        String wrapper_name = "applyReduce";
        String method_call = target_func+"("+ argsToMain+");\n";
        if(filename.startsWith("reduce")){
            wrapper_func_body = "static int "+wrapper_name+"( int[] a) {\n" +
                    "   int s = a[0];\n" +
                    "   for(int i = 1 ; i < 3 ; i++){\n" + //// This is where we set the upper bound for the loop in reduce.
                    "       s = " + target_func +"( s , a[i] );\n"+
                    "   }\n" +
                    "   return s;\n" +
                    "}\n";
            visitor.setTargetJPF(wrapper_name);
            target_func = wrapper_name;
                method_call = "int[] arr = "+ argsToMain+";\n       "+target_func+"(arr);\n";
        }

        String skeleton =
                "public class " + filename.replace(".java" , "") + " { \n" +
                        "   public static void main(String[] args) { \n" +
                        "       "+ method_call +
                        "   }\n " ;

        String content = skeleton;
        content  = content + wrapper_func_body;

        for(String fun : used_func){
            if(functions.containsKey(fun))
            content += functions.get(fun);
        }

        try {
            bw.write(content);
        } catch (IOException ioe) {
            ioe.printStackTrace();
        } finally {

        }
    }

    public void close() {
        try {
            if (bw != null)
                bw.write("}");
                bw.close();
        } catch (Exception ex) {
            System.out.println("Error in closing the BufferedWriter" + ex);
        }
    }
}
