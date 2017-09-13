import java.io.*;
import java.util.*;

import org.eclipse.jdt.core.dom.*;

public class UDFDecompilerAndExtractor extends Logging {

    String classfile = null;
    String classFile_jad = null;
    String mainArgs = null;
    String outputJava = null;
    HashMap<String, ArrayList<String>> call_graph = new HashMap<String, ArrayList<String>>();

    public UDFDecompilerAndExtractor(String classf, String classf_jad, String args, String output_java) {
        classfile = classf;
        classFile_jad = classf_jad;
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
                current_fun = name.toString();
                
                // Check if the method declaration is for parameter overloading
                //Todo: Come up with a better fix // FIXME: 9/13/17
                if (node.getReturnType2() != null) {
                    if (node.getReturnType2().toString().equals("Object")){
                        boolean vol = false;
                        for(Modifier m : (List<Modifier>)node.modifiers() ){
                            if(m.isVolatile()){
                                vol = true;
                            }
                        }
                        if(vol) return true;
                    }
                }

                loginfo(LogType.DEBUG, node.toString());
                Modifier mod = ((Modifier) node.modifiers().get(0));
                mod.setKeyword(Modifier.ModifierKeyword.STATIC_KEYWORD);
                u_writer.enrollFunction(name.toString(), node.toString() + "\n  ");
                return true;
            }

            public boolean visit(MethodInvocation inv) {
                if (call_graph.containsKey(current_fun)) {
                    if (!current_fun.equals(inv.getName().toString()))
                        call_graph.get(current_fun).add(inv.getName().toString());
                } else {
                    ArrayList<String> temp = new ArrayList<String>();
                    temp.add(inv.getName().toString());
                    if (!current_fun.equals(inv.getName().toString()))
                        call_graph.put(current_fun, temp);
                }
                loginfo(LogType.DEBUG, "Function invoked  " + inv.getName().toString());
                return true;
            }
        });

        Set<String> functions_set = new HashSet<>();
        String jpffunction = getJPFFunction("apply");
        functions_set.add(jpffunction);
        getAllCallee(jpffunction, functions_set);
        u_writer.write(functions_set, jpffunction);
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

    public void getAllCallee(String s, Set<String> callees) {
        ArrayList<String> fun = call_graph.get(s);
        if (fun == null) {
            return;
        } else {
            callees.addAll(fun);
            for (String fun_name : fun) {
                if (!callees.contains(fun))
                    getAllCallee(fun_name, callees);
            }
        }
    }


    public String getJPFFunction(String s) {
        ArrayList<String> fun = call_graph.get(s);
        if (fun == null) {
            return s;
        }
        //Set<String> key = call_graph.keySet();
        for (String funname : fun) {
            if (funname.contains("apply"))
                return getJPFFunction(funname);
        }
        return s;
    }

    //loop directory to get file list
    public void ParseFilesInDir(String jpfJar, String jpfModel) throws Exception {

        if (new File(classFile_jad).exists()) {
            loginfo(LogType.INFO, "Deleting file " + classFile_jad + " ...");
            new File(classFile_jad).delete();
        }
        String classFile_class = classfile + ".class";
        decompileProgram(classFile_class);
        String new_classname = parse(readFileToString(classFile_jad), outputJava + classFile_jad.replace(".jad", ""), mainArgs);
        createJPFile(new_classname, getJPFFunction("apply"), jpfModel);
        Runner.runCommand(new String[]{"javac", "-g",
                        Configuration.JPF_HOME + "jpf-symbc/src/examples/spf/" + new_classname + ".java"},
                Configuration.JAVA_RUN_DIR);

    }

    public void createJPFile(String target, String fun_name, String jpfPath) throws Exception {
        String content = Configuration.JPF_FILE_PLACEHOLDER(target, fun_name, outputJava);
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