// c/loop-acceleration/phases_true-unreach-call1.c

procedure main() {
  var tmp1: int;
  var tmp2: int;
  var x: int;
  var LRG1: int;
  var LRG2: int;

  x := 0;
  LRG1 := 2 * tmp1;
  LRG2 := (2 * tmp2) + 1;

  assume 0 < LRG1;
  assume LRG1 < LRG2;

  while (x < LRG2)  //0x0fffffff
  // invariant x >= LRG1 ==> (x mod 2 == 0) ;
  {
    if (x < LRG1) { // 0xfff0
      x := x + 1; 
    } else {
      x := x + 2;
    }
  }
  
  assert(0 == (x mod 2));
}
