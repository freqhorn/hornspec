// dilig-benchmarks/single/20.c
procedure main()
{
    var x,y,k,j,i,n,m : int;
    
    assume((x+y)== k);
    m := 0;
    j := 0;
    while(j<n)
    // invariant (x+y)==k && m >= 0 && j >= 0 && (n>0 ==> m < n);
    {
      if(j==i)
      {
         x:=x+1;
         y:=y-1;
      }else
      {
         y:=y+1;
         x:=x-1;
      }
      
      if(*) {
        m := j;
      }
      
      j := j + 1;
    }
    
    assert ((n>0) ==> m<n);
}
