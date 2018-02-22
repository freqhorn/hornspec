// dilig-benchmarks/single/08.c
/*
 *  Based on "Automatically refining abstract interpretations" fig.1
 */

procedure main() {
 var x,y : int;
 x := 0;
 y := 0;
 while(*)
 //invariant (x>=1 ==> y >= 100);
 {
   if(*){
      x := x + 1;
      y := y + 100;
   }
   else if (*){
      if (x >= 4) {
          x := x + 1;
          y := y + 1;
      }
      if (x < 0){
          y := y - 1;
      }
   }

 }
 assert(x < 4 || y > 2);
}
