#include "deep/RndLearnerV2.hpp"

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
  const char *OPT_V1 = "--v1";
  const char *OPT_V2 = "--v2";
  const char *OPT_MAX_ATTEMPTS = "--attempts";
  const char *OPT_K_IND = "--kind";
  const char *OPT_ITP = "--itp";
  const char *OPT_BATCH = "--batch";
  const char *OPT_RETRY = "--retry";
  const char *OPT_OUT_FILE = "--out";
  const char *OPT_GET_FREQS = "--freqs";
  const char *OPT_ADD_EPSILON = "--eps";
  const char *OPT_AGG_PRUNING = "--aggp";

  if (getBoolValue(OPT_HELP, false, argc, argv) || argc == 1){
    outs () <<
        "* * *                                 FreqHorn v.0.2 - Copyright (C) 2017                                 * * *\n" <<
        "                                       Grigory Fedyukovich & Sam Kaufman                                       \n\n" <<
        "Usage:                          Purpose:\n" <<
        " freqhorn [--help]               show help\n" <<
        " freqhorn [options] <file.smt2>  discover invariants for a system of constrained Horn clauses\n" <<
        "                                 (`file.smt2` in a datalog format extending SMT-LIB2)\n" <<
        "Options:\n" <<
        " " << OPT_V1 << "                            original version (just one-by-one sampling)\n"
        " " << OPT_V2 << " (default)                  revised version (all-at once bootstrapping and sampling)\n\n"
        " " << OPT_MAX_ATTEMPTS << " <N>                  maximal number of candidates to sample and check\n" <<
        " " << OPT_OUT_FILE << " <file.smt2>               serialize invariants to `file.smt2`\n\n" <<
        "V1 options only:\n" <<
        " " << OPT_ADD_EPSILON << "                           add small probabilities to features that never happen in the code\n" <<
        " " << OPT_AGG_PRUNING << "                          prioritize and prune the search space aggressively\n" <<
        " " << OPT_GET_FREQS << "                         calculate frequency distributions and sample from them\n" <<
        "                                 (if not specified, sample from uniform distributions)\n" <<
        " " << OPT_K_IND << "                          run k-induction after each learned lemma\n\n" <<
        "V2 options only:\n" <<
        " " << OPT_AGG_PRUNING << "                          prioritize and prune the search space aggressively\n" <<
        " " << OPT_ITP << "                           bound for itp-based proofs\n" <<
        " " << OPT_BATCH << "                         threshold for how many candidates to check at once\n" <<
        " " << OPT_RETRY << "                         threshold for how many lemmas to wait before giving failures a second chance\n";
    
    return 0;
  }

  bool vers1 = getBoolValue(OPT_V1, false, argc, argv);
  bool vers2 = getBoolValue(OPT_V2, false, argc, argv);
  if (vers1 && vers2)
  {
    outs() << "Only one version of the algorithm can be chosen\n";
    return 0;
  }

  if (!vers1 && !vers2) vers2 = true; // default
  
  int maxAttempts = getIntValue(OPT_MAX_ATTEMPTS, 2000000, argc, argv);
  bool kinduction = getBoolValue(OPT_K_IND, false, argc, argv);
  bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
  bool addepsilon = getBoolValue(OPT_ADD_EPSILON, false, argc, argv);
  bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
  int itp = getIntValue(OPT_ITP, 0, argc, argv);
  int batch = getIntValue(OPT_BATCH, 3, argc, argv);
  int retry = getIntValue(OPT_RETRY, 3, argc, argv);
  char * outfile = getStrValue(OPT_OUT_FILE, NULL, argc, argv);

  if (vers2)  // run a revised algorithm
    learnInvariants2(string(argv[argc-1]), outfile, maxAttempts,
                  itp, batch, retry, aggressivepruning);
  else        // run an old algorithm
    learnInvariants(string(argv[argc-1]), outfile, maxAttempts,
                  kinduction, itp, densecode, addepsilon, aggressivepruning);
  return 0;
}
