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

vector<string> getCommaSepStrValues(const char * opt, vector<string> defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      stringstream tmpss(argv[i+1]);
      vector<string> values;
      while (tmpss.good()) {
	string tmpstr;
	getline(tmpss, tmpstr, ',');
	values.push_back(tmpstr);
      }
      return values;
    }
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc == 1){
    outs () <<
        "* * *                              FreqHorn-Nonlin v.0.2 - Copyright (C) 2020                              * * *\n" <<
        "                                          Grigory Fedyukovich et al                                      \n\n" <<
        "Usage:                          Purpose:\n" <<
        " freqn [--help]                   show help\n" <<
        " freqn [options] <file.smt2>      discover invariants for a system of constrained Horn clauses\n\n" <<
        "Options:\n" <<
        "  --stren <NUM>                   number of strengthening iterations (by default, 1)          \n" <<
      "  --cex <NUM>                     search for counterexamples of given length                  \n" <<
      "  --maximal                       get maximal specifications for under-constrained relations \n" <<      
      "  --rel-order <String List>       comma separated list of relations' order to be followed while finding maximal solution\n"
      " --nogas                         Run only SMT solving \n"
      " --usesygus                     Use SyGuS solver instead of CHC \n"
      " --useuc                        Use underconstrained relations\n"
      " --fixcrel                      Fix constrained relations after getting initial solution\n"
      " --newenc                       Use the new encoding\n";

    return 0;
  }
  int cex = getIntValue("--cex", 0, argc, argv);
  int str = getIntValue("--stren", 1, argc, argv);
  bool maximal = getBoolValue("--maximal", false, argc, argv);
  vector<string> relsOrder = getCommaSepStrValues("--rel-order", vector<string>(), argc, argv);
  bool noGAS = getBoolValue("--nogas", false, argc, argv);
  bool usesygus = getBoolValue("--usesygus", false, argc, argv);
  bool useUC = getBoolValue("--useuc", false, argc, argv);
  bool newenc = getBoolValue("--newenc", false, argc, argv);
  bool fixcrel = getBoolValue("--fixcrel", false, argc, argv);

  if (fixcrel && !useUC) {
    outs() << "Can't use --fixcrel wihout --useuc\n";
    return 1;
  }
  
  solveNonlin(string(argv[argc-1]), cex, str, maximal, relsOrder, !noGAS, usesygus, useUC, newenc, fixcrel);
  return 0;
}
