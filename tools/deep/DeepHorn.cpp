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

char * getStrValue(const char * opt, char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
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
  const char *OPT_K_IND = "--kind";
  const char *OPT_OUT_FILE = "--out";
  const char *OPT_GET_FREQS = "--freqs";
  const char *OPT_ADD_EPSILON = "--eps";
  const char *OPT_AGG_PRUNING = "--aggp";

  if (getBoolValue(OPT_HELP, false, argc, argv) || argc == 1){
    outs () <<
        "* * *                             FreqHorn v.0.1 - Copyright (C) 2017                             * * *\n" <<
        "                                   Grigory Fedyukovich & Sam Kaufman                                   \n\n" <<
        "Usage:                          Purpose:\n" <<
        " deephorn [--help]               show help\n" <<
        " deephorn [options] <file.smt2>  discover invariants for a system of constrained Horn clauses\n" <<
        "                                 (`file.smt2` in a datalog format extending SMT-LIB2)\n" <<
        "Options:\n" <<
        " " << OPT_MAX_ATTEMPTS << " <N>                  maximal number of candidates to sample and check\n" <<
        " " << OPT_OUT_FILE << " <file.smt2>               serialize invariants to `file.smt2`\n" <<
        " " << OPT_ADD_EPSILON << "                           add small probabilities to features that never happen in the code\n" <<
        " " << OPT_AGG_PRUNING << "                          prioritize and prune the search space aggressively\n" <<
        " " << OPT_GET_FREQS << "                         calculate frequency distributions and sample from them\n" <<
        "                                 (if not specified, sample from uniform distributions)\n" <<
        " " << OPT_K_IND << "                          run k-induction after each learned lemma\n" <<
        "                                 (for pure k-induction, run 'kind <file.smt2>')\n";

    return 0;
  }

  int maxAttempts = getIntValue(OPT_MAX_ATTEMPTS, 2000000, argc, argv);
  bool kinduction = getBoolValue(OPT_K_IND, false, argc, argv);
  bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
  bool addepsilon = getBoolValue(OPT_ADD_EPSILON, false, argc, argv);
  bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
  char * outfile = getStrValue(OPT_OUT_FILE, NULL, argc, argv);

  learnInvariants(string(argv[argc-1]), outfile, maxAttempts, kinduction, densecode, addepsilon, aggressivepruning);
  return 0;
}
