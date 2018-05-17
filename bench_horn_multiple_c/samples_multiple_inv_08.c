#include "common.h"

int main()
{
  int k=0, j=0;

  RESET();
  
  while (j < 1000) {
    /* print should have same order as argument order for corresponding relation in CHC */
    PRINT(k,j);
    j++;
    k++;
  }

  RESET();
  j=0;
  while (j < 1000) {
    PRINT(k,j);
    j++;
    k++;
  }
  
  RESET();
  j=0;
  while (j < 1000) {
    PRINT(k,j);
    j++;
    k++;
  }

  FIN();
  
  assert(k>=3000);

  return 0;
}

    
