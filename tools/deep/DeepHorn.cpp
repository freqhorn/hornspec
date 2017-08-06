#include "deep/RndLearner.hpp"

using namespace ufo;
using namespace std;

int main (int argc, char ** argv)
{
  if (argc == 1){
    outs() << "At least an input file should be given\n";
    return 0;
  }
    
  int maxAttempts = 2000000;       //default
  if (argc > 2) maxAttempts = atoi(argv[1]);
  
  bool densecode = true;           //default
  if (argc > 3) densecode = atoi(argv[2]);

  bool aggressivepruning = true;   //default
  if (argc > 4) aggressivepruning = atoi(argv[3]);
  
  learnInvariants(string(argv[argc-1]), maxAttempts, densecode, aggressivepruning);

  return 0;
}
