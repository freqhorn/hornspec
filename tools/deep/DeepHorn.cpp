#include "deep/RndLearner.hpp"

using namespace ufo;
using namespace std;

bool getBoolOption(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return atoi(argv[i+1]);
    }
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  const char *OPT_HELP = "--help";
  const char *OPT_MAX_ATTEMPTS = "--attempts";
  const char *OPT_GET_FREQS = "--freqs";
  const char *OPT_ADD_EPSILON = "--eps";
  const char *OPT_AGG_PRUNING = "--aggp";

  if (getBoolOption(OPT_HELP, false, argc, argv) || argc == 1){
    outs () <<
        "* * *                             FreqHorn v.0.1 - Copyright (C) 2017                             * * *\n" <<
        "                                   Grigory Fedyukovich & Sam Kaufman                                   \n\n" <<
        "Usage:                          Purpose:\n" <<
        " deephorn [--help]               show help\n" <<
        " deephorn [options] <file.smt2>  discover invariants for a system of constrained Horn clauses\n" <<
        "                                 (`file.smt2` in a datalog format extending SMT-LIB2)\n" <<
        "Options:\n" <<
        " " << OPT_MAX_ATTEMPTS << "                      maximal number of candidates to sample and check\n" <<
        " " << OPT_ADD_EPSILON << "                           add small probabilities to features that never happen in the code\n" <<
        " " << OPT_AGG_PRUNING << "                          prioritize and prune the search space aggressively\n" <<
        " " << OPT_GET_FREQS << "                         calculate frequency distributions and sample from them\n" <<
        "                                 (if not specified, sample from uniform distributions)\n";

    return 0;
  }
  
  int maxAttempts = getIntValue(OPT_MAX_ATTEMPTS, 2000000, argc, argv);
  bool densecode = getBoolOption(OPT_GET_FREQS, false, argc, argv);
  bool addepsilon = getBoolOption(OPT_ADD_EPSILON, false, argc, argv);
  bool aggressivepruning = getBoolOption(OPT_AGG_PRUNING, false, argc, argv);
  
  learnInvariants(string(argv[argc-1]), maxAttempts, densecode, addepsilon, aggressivepruning);
  return 0;
}
