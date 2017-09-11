import java.util.ArrayList;
import java.util.List;

public class Runner {

    public static void main(String[] args) throws Exception {
        String classfile = "/Users/malig/workspace/git/Test-Minimization-in-Big-Data/udf_extractor/target/scala-2.11/classes/WordCount$$anonfun$main$1";
        String classFile_jad = classfile.split("/")[classfile.split("/").length - 1] + ".jad";
        String mainArgs = "15";
        String outputJava = "/Users/malig/workspace/jpf/jpf-symbc/src/examples/spf/";
        String jpfJar = "/Users/malig/workspace/jpf/jpf-core/build/RunJPF.jar";
        String jpfModel = "/Users/malig/workspace/jpf/jpf-symbc/src/examples/spf/WC.jpf";

        UDFDecompilerAndExtractor udf_ex = new UDFDecompilerAndExtractor(classfile, classFile_jad, mainArgs, outputJava);
        udf_ex.ParseFilesInDir(jpfJar, jpfModel);
        String dir = "/Users/malig/workspace/jpf/jpf-symbc/src/examples";
        runCommand(new String[]{"java", "-jar", jpfJar, "spf/WC.jpf"}, dir);
    }

    public static void runCommand(String[] args, String dir) throws Exception {
// build the system command we want to run
        String s = "";
        for (String a : args) {
            s = s + "  " + a;
        }
        try {
            List<String> commands = new ArrayList<String>();
            commands.add("/bin/sh");
            commands.add("-c");
            commands.add(s);
            //commands.add("echo $JAVA_HOME");

            // execute the command
            SystemCommandExecutor commandExecutor = new SystemCommandExecutor(commands, dir);
            int result = commandExecutor.executeCommand();

            // get the stdout and stderr from the command that was run
            StringBuilder stdout = commandExecutor.getStandardOutputFromCommand();
            StringBuilder stderr = commandExecutor.getStandardErrorFromCommand();

            // print the stdout and stderr
            System.out.println("The numeric result of the command was: " + result);
            System.out.println("STDOUT:");
            System.out.println(stdout);
            System.out.println("STDERR:");
            System.out.println(stderr);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}

