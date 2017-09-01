#include "deep/BndExpl.hpp"

using namespace ufo;
using namespace std;

int main (int argc, char ** argv)
{
  if (argc == 1){
    outs() << "At least an input file should be given\n";
    return 0;
  }

  int upper = 1000;           //default

  if (argc > 2) upper = min(upper, atoi(argv[1]));

  kInduction(string(argv[argc-1]), upper);

  return 0;
}
