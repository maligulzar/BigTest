public class Effect {

    static int test(int x, int y) {
        if(x > 100) {
            x = x * 4;
            y = y - 20;
        }
        else {
            x = x * 2;
            y = y + 10;
        }

        if(y > 10 && x > 150){
            x = x + y;
        }
        else {
            x = x - y;
        }
        
        return x;
        
    }

    public static void main(String[] args) {    
        test(150, 20);
    }
}
