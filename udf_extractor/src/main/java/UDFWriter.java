import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;


public class UDFWriter {
    String filename = null;
    BufferedWriter bw = null;
    public UDFWriter(String filen , String argsToMain) {
        try {

            filename = filen.replace("$" , "");
            String arr[] = filename.split("/");
            String file_name = arr[arr.length-1];
            String skeleton =
                    "public class " + file_name.replace(".java" , "") + " { \n" +
                    "   public static void main(String[] args) { \n" +
                    "       apply("+ argsToMain+");\n" +
                    "   }\n " ;
            File file = new File(filename);
            filename=file_name;
            if (!file.exists()) {
                file.createNewFile();
            }
            FileWriter fw = new FileWriter(file);
            bw = new BufferedWriter(fw);
            bw.write(skeleton);
        } catch (Exception ex) {
            ex.printStackTrace();
        }
    }

    public void write(String mycontent) {
        try {
            bw.write(mycontent);
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
