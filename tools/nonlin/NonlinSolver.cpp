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

string getStrValue(const char * opt, string defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return string(argv[i+1]);
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
        "* * *                                   HornSpec v.1.0 - Copyright (C) 2021                                    * * *\n" <<
        "                                       Sumanth Prabhu and Grigory Fedyukovich                                  \n\n" <<
        "Usage:                            Purpose:\n" <<
        "  hornspec [--help]                 show help\n" <<
        "  hornspec [options] <CHC.smt2>     discover invariants/specifications for a CHC system\n\n" <<
        "Options:\n" <<
//        "  --stren <NUM>                   number of strengthening iterations (by default, 1)          \n" <<
//        "  --cex <NUM>                     search for counterexamples of given length                  \n" <<
        "  --skip-maximal                    return after the first iteration (i.e., could be non-maximal) \n" <<
//        "  --rel-order <String List>         comma separated list of relations to follow while finding maximal solution\n" <<
        "  --use-smt-model                   weakening with Z3 models (disabled by default)\n" <<
        "  --sygus \"<path/bin [options]>\"    weakening with CVC4 (a path to external binary + options, disabled by default)\n" <<
        "                                    (for CVC4, use options \"--sygus-add-const-grammar --sygus-out=status-or-def\")\n";
    //These are experimental options 
      // " --useuc                        Use underconstrained relations\n"
      // " --fixcrel                      Fix constrained relations after getting initial solution\n"
      // " --newenc                       Use the new encoding\n";

    return 0;
  }
  int cex = getIntValue("--cex", 0, argc, argv);
  int str = getIntValue("--stren", 1, argc, argv);
  bool maximal = !getBoolValue("--skip-maximal", false, argc, argv);
  vector<string> relsOrder = getCommaSepStrValues("--rel-order", vector<string>(), argc, argv);
  bool noGAS = getBoolValue("--use-smt-model", false, argc, argv);
  string syguspath = getStrValue("--sygus", "", argc, argv);
  bool usesygus = syguspath != "";
  bool useUC = getBoolValue("--useuc", false, argc, argv);
  bool newenc = getBoolValue("--newenc", false, argc, argv);
  bool fixcrel = getBoolValue("--fixcrel", false, argc, argv);

  if (fixcrel && !useUC) {
    outs() << "Can't use --fixcrel wihout --useuc\n";
    return 1;
  }

  std::ifstream infile(argv[argc-1]);
  if (!infile.good())
  {
    outs() << "Could not read file \"" << argv[argc-1] << "\"\n";
    return 0;
  }

  if (usesygus)
  {
    string toolname = syguspath.substr(0, syguspath.find(" "));
    std::ifstream cvc4file(toolname);
    if (!cvc4file.good())
    {
      outs() << "Could not read file \"" << toolname << "\"\n";
      return 0;
    }
  }

  solveNonlin(string(argv[argc-1]), cex, str, maximal, relsOrder, !noGAS, usesygus, useUC, newenc, fixcrel, syguspath);
  return 0;
}
