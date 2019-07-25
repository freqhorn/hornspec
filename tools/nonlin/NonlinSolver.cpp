#include "deep/NonlinCHCsolver.hpp"

using namespace ufo;
using namespace std;

int main (int argc, char ** argv)
{
  solveNonlin(string(argv[argc-1]));
  return 0;
}
