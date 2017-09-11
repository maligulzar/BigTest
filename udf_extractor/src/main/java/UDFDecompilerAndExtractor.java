import java.io.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.jdt.core.dom.*;
import org.eclipse.jdt.internal.core.util.ExceptionAttribute;

public class UDFDecompilerAndExtractor {
    //use ASTParse to parse string
    String classfile = "/Users/malig/workspace/git/Test-Minimization-in-Big-Data/udf_extractor/target/scala-2.11/classes/WordCount$$anonfun$main$1";
    String classFile_jad = classfile.split("/")[classfile.split("/").length - 1] + ".jad";
    String mainArgs = "15";
    String outputJava = "/Users/malig/workspace/jpf/jpf-symbc/src/examples/spf/";
    HashMap<String, ArrayList<String>> call_graph = new HashMap<String, ArrayList<String>>();

    public UDFDecompilerAndExtractor(String classf, String classf_jad, String args, String output_java) {
        classfile = classf;
        classf_jad = classf_jad;
        mainArgs = args;
        outputJava = output_java;
    }


    public String parse(String str, String filename, String mainArgs) {
        ASTParser parser = ASTParser.newParser(AST.JLS3);
        parser.setSource(str.toCharArray());
        parser.setKind(ASTParser.K_COMPILATION_UNIT);
        final CompilationUnit cu = (CompilationUnit) parser.createAST(null);
        AST ast = cu.getAST();
        UDFWriter u_writer = new UDFWriter(filename + ".java", mainArgs);
        cu.accept(new ASTVisitor() {
            Set names = new HashSet();
            String current_fun = "";

            public boolean visit(MethodDeclaration node) {
                SimpleName name = node.getName();
                this.names.add(name.getIdentifier());
                if (name.toString().contains("apply")) {
                    current_fun = name.toString();
                    System.out.println("\n******* Printing Java UDF ********");
                    System.out.println(node.toString());
                    Modifier mod = ((Modifier) node.modifiers().get(0));
                    mod.setKeyword(Modifier.ModifierKeyword.STATIC_KEYWORD);
                    //  node.modifiers().add(1 , "Static");
                    u_writer.write(node.toString() + "\n  ");
                    System.out.println("**********************************");
                }
                return true;
            }

            public boolean visit(MethodInvocation inv) {
                if (call_graph.containsKey(current_fun)) {
                    call_graph.get(current_fun).add(inv.getName().toString());
                } else {
                    ArrayList<String> temp = new ArrayList<String>();
                    temp.add(inv.getName().toString());
                    call_graph.put(current_fun, temp);
                }
                System.out.println("INV : " + inv.getName().toString());
                return true;
            }
        });
        u_writer.close();
        return u_writer.filename.replace(".java", "");
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


    public String getJPFFunction(String s) {
        ArrayList<String> fun = call_graph.get(s);
        if (fun == null) {
            return s;
        }
        //Set<String> key = call_graph.keySet();
        while (!fun.isEmpty()) {
            String temp = fun.get(0);
            if (temp.contains("apply"))
                return getJPFFunction(temp);
            fun.remove(0);
        }
        return s;
    }

    //loop directory to get file list
    public void ParseFilesInDir(String jpfJar, String jpfModel) throws Exception {

        if (new File(classFile_jad).exists()) {
            new File(classFile_jad).delete();
        }
        String classFile_class = classfile + ".class";
        decompileProgram(classFile_class);
        String new_classname = parse(readFileToString(classFile_jad), outputJava + classFile_jad.replace(".jad", ""), mainArgs);
        //System.out.println(" --> " + getJPFFunction("apply"));
        createJPFile(new_classname, getJPFFunction("apply"), jpfModel);

    }

    public void createJPFile(String target, String fun_name, String jpfPath) throws Exception {
        String content = "target=" + target + "\n" +
                "\n" +
                "classpath=${jpf-symbc}/build/examples\n" +
                "#sourcepath=${jpf-symbc}/src/examples\n" +
                "\n" +
                "symbolic.method=" + target + "." + fun_name + "(sym)\n" +
                "\n" +
                "symbolic.debug=true\n" +
                "\n" +
                "listener = gov.nasa.jpf.symbc.SymbolicListener\n" +
                "#listener = gov.nasa.jpf.symbc.sequences.SymbolicSequenceListener #for test-case generation";

        FileWriter fw = null;
        try {
            File file = new File(jpfPath);
            if (!file.exists()) {
                file.createNewFile();
            }
            fw = new FileWriter(file);

        } catch (Exception e) {
            e.printStackTrace();
        }

        BufferedWriter bw = null;
        try {
            bw = new BufferedWriter(fw);
            bw.write(content);
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            bw.close();
        }
    }

//    public static void main(String[] args) throws Exception {
//        String jpfJar = "/Users/malig/workspace/jpf/jpf-core/build/RunJPF.jar";
//        String jpfModel = "/Users/malig/workspace/jpf/jpf-symbc/src/examples/spf/WC.jpf";
//        ParseFilesInDir(jpfJar, jpfModel);
//    }

    public void decompileProgram(String file) {
        String jad_exe = "/Users/malig/workspace/git/Test-Minimization-in-Big-Data/udf_extractor/jadmx158/jad";
        String[] args = new String[]{jad_exe, file};
        runCommand(args);
    }

    public void runCommand(String[] args) {
        try {
            String s = "";
            for (String a : args) {
                s = s + "  " + a;
            }
            Runtime runt = Runtime.getRuntime();
            Process p = runt.exec(s, new String[]{"PATH=$PATH", "JUNIT_HOME=/Users/malig/workspace/jpf/", "JPF=/Users/malig/workspace/jpf/jpf-core"});
            BufferedReader stdInput = new BufferedReader(new
                    InputStreamReader(p.getInputStream()));
            BufferedReader stdError = new BufferedReader(new
                    InputStreamReader(p.getErrorStream()));
            // read the output from the command
            System.out.println("Here is the standard output of the command:\n");
            while ((s = stdInput.readLine()) != null) {
                System.out.println(s);
            }
            // read any errors from the attempted command
            System.out.println("Here is the standard error of the command (if any):\n");
            while ((s = stdError.readLine()) != null) {
                System.out.println(s);
            }
            stdError.close();
            stdInput.close();
        } catch (IOException e) {
            System.out.println("exception happened - here's what I know: ");
            e.printStackTrace();
            System.exit(-1);
        }
    }


}