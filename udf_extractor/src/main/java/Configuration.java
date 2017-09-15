import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

public class Configuration {
    static String JPF_HOME = "/Users/amytis/Projects/jpf/"; // Assuming that jpf/ contains jpf-core and jpf-symb
    static String HOME = ""; // Project Home to extract the class files of UDFs
    static String JUNIT_HOME = "/Users/amytis/Projects/jpf/"; // Junit Home folder
    static String JAD_EXE = "/Users/amytis/Projects/Test-Minimization-in-Big-Data/udf_extractor/jadmx158/jad";
    static String JAVA_RUN_DIR = "/Users/amytis/Projects/jpf/jpf-symbc/src/examples";
    static String arr[] = "map,flatmap,filter,reduceByKey,reduce".split(",");
    static ArrayList<String> spark_ops = new ArrayList<>(Arrays.asList(arr));
    static HashMap<String, String> map_args = new HashMap<>();
    //// TODO: 9/14/17 Populate the input arguments to each of the udfs
    static String JPF_FILE_PLACEHOLDER(String target, String fun_name , String example_build ) {

        return "target=" + target + "\n" +
                "\n" +
                "classpath="+example_build+"\n" +
                "#sourcepath=${jpf-symbc}/src/examples\n" +
                "\n" +
                "symbolic.method=" + target + "." + fun_name + "(sym)\n" +
                "\n" +
                "symbolic.debug=true\n" +
                "\n" +
                "#listener = gov.nasa.jpf.symbc.SymbolicListener\n" +
                "#listener = gov.nasa.jpf.symbc.sequences.SymbolicSequenceListener #for test-case generation" +
                "\n" + 
                "symbolic.dp=no_solver";
    }

    static boolean isSparkDataflowOperator(String op){
        return spark_ops.contains(op);
    }


    static String getArgs(String op_name){
        if(map_args.containsKey(op_name)){
            return map_args.get(op_name);
        }
        return "";
    }

}