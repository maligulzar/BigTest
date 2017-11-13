public class Test {
    public static void main(String[] args) {
        final int Size = 6;
        int[] arr = new int[Size];
            //   arr[] {1,2,3,-4,3,1};
        sum(0, arr);

    }
    public static int sum(int s , int[] arr){
        for(int i = 0 ; i < 2 ; i++){
		for(int j = 0 ; j <= arr[i] ; j++){
			s  = (j % 2 == 1) ? s + arr[i] : s;
		}
//            s = (s < 8)? s  + arr[i] : s;
        }
        return s;
    }
}
