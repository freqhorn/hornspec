#ifndef BNDEXPL__HPP__
#define BNDEXPL__HPP__

#include "Horn.hpp"
#include "Distribution.hpp"
#include "ae/SMTUtils.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class BndExpl
  {
    private:

    ExprFactory &m_efac;
    SMTUtils u;
    CHCs& ruleManager;

    public:

    BndExpl (ExprFactory &efac, EZ3 &z3, CHCs& r) :
      m_efac(efac), ruleManager(r), u(efac) {}

    void guessRandomTrace(vector<int>& trace)
    {
      std::srand(std::time(0));
      Expr curRel = mk<TRUE>(m_efac);

      while (curRel != ruleManager.failDecl)
      {
        int range = ruleManager.outgs[curRel].size();
        int chosen = guessUniformly(range);
        int chcId = ruleManager.outgs[curRel][chosen];
        curRel = ruleManager.chcs[chcId].dstRelation;
        trace.push_back(chcId);
      }
    }

    void getAllTraces (Expr src, Expr dst, int len, vector<int> trace, vector<vector<int>>& traces)
    {
      if (len == 1)
      {
        for (auto a : ruleManager.outgs[src])
        {
          if (ruleManager.chcs[a].dstRelation == dst)
          {
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : ruleManager.outgs[src])
        {
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllTraces(ruleManager.chcs[a].dstRelation, dst, len-1, newtrace, traces);
        }
      }
    }

    Expr toExpr(vector<int>& trace)
    {
      ExprVector ssa;

      ExprVector bindVars1;
      ExprVector bindVars2;
      int bindVar_index = 0;
      int locVar_index = 0;

      for (auto &step : trace)
      {
        bindVars2.clear();
        HornRuleExt& hr = ruleManager.chcs[step];
        Expr body = hr.body;
        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          body = replaceAll(body, hr.srcVars[i], bindVars1[i]);
        }

        for (int i = 0; i < hr.dstVars.size(); i++)
        {
          bool kept = false;
          for (int j = 0; j < hr.srcVars.size(); j++)
          {
            if (hr.dstVars[i] == hr.srcVars[j])
            {
              bindVars2.push_back(bindVars1[i]);
              kept = true;
            }
          }
          if (!kept)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(bindVar_index++), m_efac);
            bindVars2.push_back(bind::intConst(new_name));
          }

          body = replaceAll(body, hr.dstVars[i], bindVars2[i]);
        }

        for (int i = 0; i < hr.locVars.size(); i++)
        {
          Expr new_name = mkTerm<string> ("__loc_var_" + to_string(locVar_index++), m_efac);
          Expr var = bind::intConst(new_name);

          body = replaceAll(body, hr.locVars[i], var);
        }

        bindVars1 = bindVars2;

        ssa.push_back(body);
      }

      return conjoin(ssa, m_efac);
    }

    void doit(int cur_bnd, int bnd)
    {
      bool unsat = true;
      int num_traces = 0;

      outs () << "Exploring traces (up to bound): 1";     // GF: trace of length 1 is always empty
      while (unsat && cur_bnd <= bnd)
      {
        outs () << ", " << cur_bnd;
        vector<vector<int>> traces;
        vector<int> empttrace;

        getAllTraces(mk<TRUE>(m_efac), ruleManager.failDecl, cur_bnd++, vector<int>(), traces);

        for (auto &a : traces)
        {
//        for (auto &b : a) outs() << " -> " << * ruleManager.chcs[b].dstRelation; outs() << "\n";
          num_traces++;
          unsat = !u.isSat(toExpr(a));
          if (!unsat) break;
        }
      }

      outs () << "\nTotal number of traces explored: " << num_traces <<"\n\n"
              << (unsat ? "UNSAT for all traces up to " : "SAT for a trace with ")
              << (cur_bnd - 1) << " steps\n";
    }
  };

  inline void unrollAndCheck(string smt, int bnd1, int bnd2)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    BndExpl ds(m_efac, z3, ruleManager);
    ds.doit(bnd1, bnd2);
  };
}

#endif
