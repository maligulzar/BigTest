package udfExtractor;

import java.io.*;
import java.util.ArrayList;
import java.util.HashMap;

import org.eclipse.jdt.core.dom.*;

public class UDFDecompilerAndExtractor extends Logging {

    String classfile = null;
    String classFile_jad = null;
    String outputJava = null;
    ArrayList<JPFDAGNode> jpf_dag = new ArrayList<>();


    public UDFDecompilerAndExtractor(String classf, String classf_jad, String output_java) {
        classfile = classf;
        classFile_jad = classf_jad;
        outputJava = output_java;
    }


    public void parse(String str , String jpfdir) {
        ASTParser parser = ASTParser.newParser(AST.JLS3);
        parser.setSource(str.toCharArray());
        parser.setKind(ASTParser.K_COMPILATION_UNIT);
        final CompilationUnit cu = (CompilationUnit) parser.createAST(null);
        AST ast = cu.getAST();
        cu.accept(new SparkProgramVisitor(this , jpfdir));
    }

    //read file content into a string
    public String readFileToString(String filePath) throws IOException {
        StringBuilder fileData = new StringBuilder(1000);
        BufferedReader reader = new BufferedReader(new FileReader(filePath));
        char[] buf = new char[10];
        int numRead = 0;
        while ((numRead = reader.read(buf)) != -1) {
            //  System.out.println(numRead);
            String readData = String.valueOf(buf, 0, numRead);
            fileData.append(readData);
            buf = new char[1024];
        }
        reader.close();
        return fileData.toString();
    }


    //loop directory to get file list
    public void ParseFilesInDir( String jpfdir) throws Exception {

        if (new File(classFile_jad).exists()) {
            loginfo(LogType.INFO, "Deleting file " + classFile_jad + " ...");
            new File(classFile_jad).delete();
        }
        String classFile_class = classfile + ".class";
        decompileProgram(classFile_class);
        parse(readFileToString(classFile_jad), jpfdir);
    }


    public void decompileProgram(String file) {
        String[] args = new String[]{Configuration.JAD_EXE, file};
        runCommand(args);
    }

    public void runCommand(String[] args) {
        try {
            String s = "";
            for (String a : args) {
                s = s + "  " + a;
            }
            loginfo(LogType.INFO, "Running Command : " + s);
            Runtime runt = Runtime.getRuntime();
            Process p = runt.exec(s);
            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(p.getInputStream()));
            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(p.getErrorStream()));
            // read the output from the command
            StringBuilder stdout = new StringBuilder("");
            while ((s = stdInput.readLine()) != null) {
                stdout.append(s);
            }
            loginfo(LogType.INFO, stdout.toString());
            StringBuilder stderr = new StringBuilder("");
            while ((s = stdError.readLine()) != null) {
                stderr.append(s);
            }
            loginfo(LogType.WARN, stderr.toString());
            stdError.close();
            stdInput.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
