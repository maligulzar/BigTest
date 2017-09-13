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
    public void write(Set<String> used_func , String target_func) {
        String skeleton =
                "public class " + filename.replace(".java" , "") + " { \n" +
                        "   public static void main(String[] args) { \n" +
                        "       "+target_func+"("+ argsToMain+");\n" +
                        "   }\n " ;

        String content = skeleton;
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
