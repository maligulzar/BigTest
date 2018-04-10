package udfExtractor;

import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Set;


public class UDFWriter {
    String filename = null;
    BufferedWriter bw = null;
    HashMap<String, FunctionStructure> functions = new HashMap<>();
    String argsToMain = null;
    boolean isString = false;


    public UDFWriter(String filen, String argsmain) {
        argsToMain = argsmain;
        try {

            filename = filen.replace("$", "");
            String arr[] = filename.split("/");
            String file_name = arr[arr.length - 1];
            File file = new File(filename);
            filename = file_name;
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

    public void enrollFunction(String name, FunctionStructure code) {
        functions.put(name, code);
    }

    public void write(Set<String> used_func, String target_func, SparkProgramVisitor visitor) {
        String wrapper_func_body = "";
        String wrapper_name = "applyReduce";
        isString = argsToMain.startsWith("\"") && argsToMain.endsWith("\"");
        String method_call = target_func + "(" + argsToMain + ");\n";
        if (filename.startsWith("reduce")) {
            wrapper_func_body = "static int " + wrapper_name + "( int[] a) {\n" +
                    "   int s = a[0];\n" +
                    "   for(int i = 1 ; i < " + Runner.loop_bound + " ; i++){\n" + //// This is where we set the upper bound for the loop in reduce.
                    "       s = " + target_func + "( s , a[i] );\n" +
                    "   }\n" +
                    "   return s;\n" +
                    "}\n";
            visitor.setTargetJPF(wrapper_name);
            target_func = wrapper_name;
            method_call = "int[] arr = " + argsToMain + ";\n       " + target_func + "(arr);\n";
        }


        String skeleton =
                "public class " + filename.replace(".java", "") + " { \n" +
                        "   public static void main(String[] args) { \n" +
                        "       " + method_call +
                        "   }\n ";

        String content = skeleton;
        content = content + wrapper_func_body;

        for (String fun : used_func) {
            if (functions.containsKey(fun)) {
            	String fun_code = getFunctionCode(fun);
            	if(fun_code.contains("Tuple2")) {
            		fun_code = fun_code.replaceAll("Tuple2", filename.replace(".java", ""));
            		content += fun_code;
            		content += replaceTuple2(filename.replace(".java", ""));
            						
            	}else
            		content += getFunctionCode(fun);
            	
            }
               
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

    public String getReturnInstant(String s) {
    	switch(s) {
    	case "int":
    			return "0";
    		
    	case "String":
    			return "\"a\"";
    			
    	default :
    			return "null";
    			
    	}
    }
    String wrapNullAroundBody(String body, String returnT, String Varname) {
    	String retVa = getReturnInstant(returnT);
    	return " { \n if( " + Varname + " == null ){ \n"
    			+ "return "+retVa + ";"
    			+ "\n"
    			+ "}else\n"
    			+ body + "\n}";
    }
    public String getFunctionCode(String name) {
        FunctionStructure fs = functions.get(name);
        String s = "";
        for (Modifier m : fs.mods) {
            s = s + " " + m.getKeyword().toString();
        }
        s = s + " " + fs.returnType.toString();
        s = s + " " + name + "(";
        if(name.equals("apply")){
            System.out.println("");
        }
        boolean wrapNull = false;
        
        for (Object par : fs.parameters) {
            SingleVariableDeclaration p = (SingleVariableDeclaration) par;
            String para = getParameterType(p,fs) ;
            if(para.startsWith("Tuple")) {
            		wrapNull = true;
            }
            s = s + para + ",";
        }
        if (s.endsWith(",")) {
            s = s.substring(0, s.length() - 1);
        }
        s = s + ")"; //+ fs.body.toString();
        String body_str = fs.body.toString();
        if(wrapNull) {
        	body_str =  	wrapNullAroundBody(body_str,  fs.returnType.toString() ,((SingleVariableDeclaration)fs.parameters.get(0)).getName().getIdentifier() );
        }
        
        for(String ty : fs.map.keySet()){
            String typ = fs.map.get(ty);
            body_str = body_str.replaceAll("\\("+typ+"\\)","");
        }
        return s + body_str;
    }

    private String getParameterType(SingleVariableDeclaration p, FunctionStructure fs) {
        if(p.getType().toString().equals("Tuple2")) {
            String _1 = null;
            String _2 = null;
            for (String s : fs.map.keySet()) {
                String[] s_arr = s.split("\\.");
                if (p.getName().getIdentifier().equals(s_arr[0])) {
                    if (s_arr.length > 1) {
                        if (s_arr[1].startsWith("_1")) {
                                _1 = fs.map.get(s);
                        } else if (s_arr[1].startsWith("_2")) {
                                _2 = fs.map.get(s);
                        }
                    }
                }

            }
            if(_1 == null && _2==null){
                return "TupleII "+p.getName().getIdentifier();
            }
            else if(_1 == null ){
                if(_2.equals("String")){
                		isString  = true;
                    return "TupleIS "+p.getName().getIdentifier();
                }else if(_2.equals("Tuple2")){
                		isString  = true;
                    return "TupleSIS "+p.getName().getIdentifier();
                }
            }
            else if(_2 == null){
                if(_1.equals("String")) {
                		isString  = true;
                    return "TupleSI " + p.getName().getIdentifier();
                }
            } else{
                if(_1.equals("String") && _2.equals("String")) {
                		isString  = true;
                    return "TupleSS "+p.getName().getIdentifier();
                }
            }
            return "TupleII "+p.getName().getIdentifier();
        }
        else{
            return p.toString();
        }
    }
    
    String replaceTuple2(String s) {
    	return "\nint ia,ib;\n" + 
    		"String sa,sb;\n" + 
    		"public int _1(){\n" + 
    		"	return ia;\n" + 
    		"}\n" + 
    		"public int _2(){\n" + 
    		"	return ib;\n" + 
    		"}\n" + 
    		"public "+s+"(int k, int v){\n" + 
    		"        ia = k;\n" + 
    		"        ib = v;\n" + 
    		"}\n" + 
    		"public "+s+"(String k, int v){\n" + 
    		"        sa = k;\n" + 
    		"        ib = v;\n" + 
    		"}\n" + 
    		"public "+s+"(int k, String v){\n" + 
    		"        ia = k;\n" + 
    		"        sb = v;\n" + 
    		"}\n" + 
    		"public "+s+"(String k, String v){\n" + 
    		"        sa = k;\n" + 
    		"        sb = v;\n" + 
    		"}";
    }
}
