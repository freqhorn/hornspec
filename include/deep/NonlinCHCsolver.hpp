#ifndef BNDEXPL__HPP__
#define BNDEXPL__HPP__

#include "HornNonlin.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  static void getCombinations(vector<vector<int>>& in, vector<vector<int>>& out, int pos = 0)
  {
    if (pos == 0) out.push_back(vector<int>());
    if (pos == in.size()) return;

    vector<vector<int>> out2;

    for (auto & a : in[pos])
    {
      for (auto & b : out)
      {
        out2.push_back(b);
        out2.back().push_back(a);
      }
    }
    out = out2;
    getCombinations(in, out, pos + 1);
  }

  class NonlinCHCsolver
  {
    private:

    ExprFactory &m_efac;
    SMTUtils u;
    CHCs& ruleManager;
    int varCnt = 0;
    ExprVector ssaSteps;

    public:

    NonlinCHCsolver (CHCs& r) : m_efac(r.m_efac), ruleManager(r), u(m_efac) {}

    bool solveIncrementally(int unr, ExprVector& rels, vector<ExprVector>& args)
    {
      if (unr > 1000) // hardcoded bound
      {
        outs () << "(maximum bound reached)\n";
        return true;
      }
      else if (rels.empty())
      {
        return false;
      }

      bool res = true;

      // reserve copy;
      auto ssaStepsTmp = ssaSteps;
      int varCntTmp = varCnt;

      vector<vector<int>> availableRules;
      for (int i = 0; i < rels.size(); i++)
      {
        vector<int> available;
        for (auto & b : ruleManager.incms[rels[i]])
        {
          Expr postcond = ruleManager.getPostcondition(b, args[i]);
          // identifying available rules
          if (u.isSat(postcond, conjoin(ssaSteps, m_efac)))
          {
            available.push_back(b);
          }
        }
        availableRules.push_back(available);
      }
      vector<vector<int>> ruleCombinations;
      getCombinations(availableRules, ruleCombinations);

      for (auto & c : ruleCombinations)
      {
        ssaSteps = ssaStepsTmp;
        varCnt = varCntTmp;
        ExprVector rels2;
        vector<ExprVector> args2;

        for (int i = 0; i < c.size(); i++)
        {
          // clone all srcVars and rename in the body
          auto &hr = ruleManager.chcs[c[i]];
          Expr body = hr.body;
          if (!hr.dstVars.empty()) body = replaceAll(body, hr.dstVars, args[i]);
          vector<ExprVector> tmp;
          for (int j = 0; j < hr.srcRelations.size(); j++)
          {
            rels2.push_back(hr.srcRelations[j]);
            ExprVector tmp1;
            for(auto &a: hr.srcVars[j])
            {
              Expr new_name = mkTerm<string> ("_fh_" + to_string(varCnt++), m_efac);
              tmp1.push_back(cloneVar(a, new_name));
            }
            args2.push_back(tmp1);
            body = replaceAll(body, hr.srcVars[j], tmp1);
          }

          ssaSteps.push_back(body);
        }
        if (u.isSat(conjoin(ssaSteps, m_efac))) // TODO: optimize with incremental SMT solving (i.e., using push / pop)
        {
          res = res && solveIncrementally(unr + 1, rels2, args2);
        }
      }
      return res;
    }

    void solveModular()
    {
      ExprVector query;
      query.push_back(ruleManager.failDecl);
      vector<ExprVector> empt;
      outs () << ((solveIncrementally (0, query, empt)) ? "unsat\n" : "sat\n");
    }
  };

  inline void solveModular(string smt)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    NonlinCHCsolver nonlin(ruleManager);
    nonlin.solveModular();
  };
}

#endif
