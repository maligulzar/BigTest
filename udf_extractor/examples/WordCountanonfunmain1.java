public class WordCountanonfunmain1 { 
   public static void main(String[] args) { 
       apply(15);
   }
 static final int apply(int p){
  return apply$mcII$sp(p);
}

  static int apply$mcII$sp(int p){
  return p <= 10 ? ((byte)(p >= 5 ? 0 : -1)) : p;
}

  static final volatile Object apply(Object v1){
  return BoxesRunTime.boxToInteger(apply(BoxesRunTime.unboxToInt(v1)));
}

  }