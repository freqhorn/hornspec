#include "deep/NonlinCHCsolver.hpp"

using namespace ufo;
using namespace std;

static inline bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc == 1){
    outs () <<
        "* * *                              FreqHorn-Nonlin v.0.1 - Copyright (C) 2019                              * * *\n" <<
        "                                          Grigory Fedyukovich et al                                      \n\n" <<
        "Usage:                          Purpose:\n" <<
        " freqn [--help]                   show help\n" <<
        " freqn [options] <file.smt2>      discover invariants for a system of constrained Horn clauses\n\n" <<
        "Options:\n" <<
        "  --cex                           search for counterexamples                         \n";

    return 0;
  }
  bool cex = getBoolValue("--cex", false, argc, argv);
  solveNonlin(string(argv[argc-1]), !cex);
  return 0;
}
