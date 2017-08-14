#include "deep/RndLearner.hpp"

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc < 3){
    outs () <<
        "* * *                           FreqHorn-IVC v.0.1 - Copyright (C) 2017                           * * *\n" <<
        "                                   Grigory Fedyukovich & Sam Kaufman                                   \n\n" <<
        "Usage:                                Purpose:\n" <<
        " ivc [--help]                          show help\n" <<
        " ivc <chc.smt2> <inv.smt2>             get an inductive validity core:\n" <<
        "                                       `chc.smt2` - system of CHCs;\n" <<
        "                                       `inv.smt2` - asserts for invariants in lexicographical order\n" <<
        "                                                    (will be rewritten)\n";
    return 0;
  }
  
  getInductiveValidityCore(argv[1], argv[2]);
  return 0;
}
