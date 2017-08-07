import gov.nasa.jpf.symbc.Debug;

public class UDF {

    static int run(int x) {
        int y = -1;
        if(x > 100)
            y = x;
        else y = 0;
        // System.out.println("y = "+Debug.getSymbolicIntegerValue(y));
        Debug.printPC("PC: ");
        System.out.println("---------------------------");
        return y;
    }

    public static void main(String[] args) {
        run(2000);
    }

}
