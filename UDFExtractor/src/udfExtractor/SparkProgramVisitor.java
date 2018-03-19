package udfExtractor;

import org.eclipse.jdt.core.dom.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.*;

public class SparkProgramVisitor extends ASTVisitor {

    HashMap<String, ArrayList<String>> call_graph = new HashMap<String, ArrayList<String>>();
    UDFDecompilerAndExtractor log = null;
    String jpf_dir = null;

    public SparkProgramVisitor(UDFDecompilerAndExtractor l, String output_jpf) {
        log = l;
        jpf_dir = output_jpf;
    }

    Set names = new HashSet();
    String current_fun = "";
    String current_method_inc = null;


    public boolean visit(ClassInstanceCreation cls) {
        if (current_method_inc != null)
            if (Configuration.isSparkDataflowOperator(current_method_inc)) {
                startUDFClass();
                cls.getAnonymousClassDeclaration().accept(this);
                closeUDFClass();
            }
        return true;
    }

    public boolean visit(MethodDeclaration node) {
        if (current_method_inc == null) return true;
        SimpleName name = node.getName();
        this.names.add(name.getIdentifier());
        current_fun = name.toString();
        // Check if the method declaration is for parameter overloading
        //Todo: Come up with a better fix // FIXME: 9/13/17
        if (node.getReturnType2() != null) {
            if (node.getReturnType2().toString().equals("Object")) {
                boolean vol = false;
                for (Modifier m : (List<Modifier>) node.modifiers()) {
                    if (m.isVolatile()) {
                        vol = true;
                    }
                }
                if (vol) return true;
            }
        }
       // log.loginfo(Logging.LogType.DEBUG, node.toString());
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
        if (Configuration.isSparkDataflowOperator(inv.getName().toString())) {
            for (Expression e : (List<Expression>) inv.arguments()) {
                current_method_inc = inv.getName().toString();
                e.accept(this);
                current_method_inc = null;
            }
        }
        return true;
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
        for (String funname : fun) {
            if (funname.contains("apply"))
                return getJPFFunction(funname);
        }
        return s;
    }

    UDFWriter u_writer;
    int op_id = 0;

    public void addToCallGraph(String caller, String callee){
        ArrayList<String> temp = new ArrayList<String>();
        temp.add(callee);
        call_graph.put(caller, temp);
    }
    String target_func_jpf  = null;
    public void setTargetJPF(String fun){
            target_func_jpf = fun;
    }

    public void startUDFClass() {
        op_id += 1;
        String class_name = current_method_inc + op_id;
        u_writer = new UDFWriter(jpf_dir + class_name + ".java", Configuration.getArgs(class_name));
        call_graph = new HashMap<>();
        names = new HashSet();
        current_fun = "";
        target_func_jpf = null;
    }

    public void closeUDFClass() {
        Set<String> functions_set = new HashSet<>();
        String jpffunction = getJPFFunction("apply");
        functions_set.add(jpffunction);
        getAllCallee(jpffunction, functions_set);
        u_writer.write(functions_set, jpffunction , this);
        u_writer.close();
        String new_classname = u_writer.filename.replace(".java", "");
        try {
            createJPFile(new_classname, getJPFFunction("apply"), jpf_dir + new_classname + ".jpf" , u_writer.isString);

            Runner.runCommand(new String[]{"javac", "-g",
                            Configuration.JPF_HOME + "jpf-symbc/src/examples/" + new_classname + ".java"},
                    Configuration.JAVA_RUN_DIR);
            log.jpf_dag.add(0, new JPFDAGNode(new_classname, jpf_dir + new_classname + ".jpf"));
        } catch (Exception e) {
            e.printStackTrace();
        }


    }

    public void createJPFile(String target, String fun_name, String jpfPath , boolean isString) throws Exception {
        if(target_func_jpf!=null)
        {
            fun_name = target_func_jpf;
        }
        String content = Configuration.JPF_FILE_PLACEHOLDER(target, fun_name, log.outputJava , isString);
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
}