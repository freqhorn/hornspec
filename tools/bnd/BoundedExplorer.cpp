#include "deep/BndExpl.hpp"

using namespace ufo;
using namespace std;

int main (int argc, char ** argv)
{
  if (argc == 1){
    outs() << "At least an input file should be given\n";
    return 0;
  }

  int lower = 2;           //default
  int upper = 10000;       //default

  if (argc > 2) lower = max(2, atoi(argv[1]));
  if (argc > 3) upper = atoi(argv[2]);

  unrollAndCheck(string(argv[argc-1]), lower, upper);

  return 0;
}
