package strings;

public class GoodbyeWorld {
	public static void main (String [] args) {
		hello("input string");
	}
	
	public static int hello(String var) {
		int i = 0;
		if (var.substring(4,7).equals("o World")){
			return var.length();
		}
		else {
			if(var.charAt(1) == 'o') {
				return 1;
			}
				return -1;
		}
	}
}
