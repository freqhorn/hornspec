// dilig-benchmarks/single/13.c
/*
 * Based on "Property-Directed Incremental Invariant Generation" by Bradley et al.
 */

procedure main() {
   var flag, j, k : int;
   
   j := 2;
   k := 0;

   while(*)
   //invariant ((flag != 0) ==> k == 0) && ((flag == 0) ==> (j == 2*k+2));
   {
     if (flag != 0) {
       j := j + 4;
     } else {
       j := j + 2;
       k := k + 1;
     }
   }
   assert(k != 0 ==> (j==2*k+2));
}
