public class Configuration {
    static String JPF_HOME = "/Users/malig/workspace/jpf/"; // Assuming that jpf/ contains jpf-core and jpf-symb
    static String HOME = ""; // Project Home to extract the class files of UDFs
    static String JUNIT_HOME = "/Users/malig/workspace/jpf/"; // Junit Home folder
    static String JAD_EXE = "/Users/malig/workspace/git/Test-Minimization-in-Big-Data/udf_extractor/jadmx158/jad";
    static String JAVA_RUN_DIR = "/Users/malig/workspace/jpf/jpf-symbc/src/examples";

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
}