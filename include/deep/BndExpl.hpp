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
    Expr extraLemmas;

    ExprVector bindVars1;

    int tr_ind; // helper vars
    int pr_ind;
    int k_ind;

    Expr inv;   // 1-inductive proof

    public:

    BndExpl (CHCs& r) :
      m_efac(r.m_efac), ruleManager(r), u(m_efac) {}

    BndExpl (CHCs& r, Expr lms) :
    m_efac(r.m_efac), ruleManager(r), u(m_efac), extraLemmas(lms) {}

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

    vector<ExprVector> bindVars;

    Expr toExpr(vector<int>& trace)
    {
      ExprVector ssa;

      ExprVector bindVars2;
      bindVars.clear();
      ExprVector bindVars1 = ruleManager.chcs[trace[0]].srcVars;
      int bindVar_index = 0;
      int locVar_index = 0;

      for (int s = 0; s < trace.size(); s++)
      {
        auto &step = trace[s];
        bindVars2.clear();
        HornRuleExt& hr = ruleManager.chcs[step];
        Expr body = hr.body;
        if (!hr.isFact && extraLemmas != NULL) body = mk<AND>(extraLemmas, body);

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
            bindVars2.push_back(cloneVar(hr.dstVars[i],new_name));
          }

          body = replaceAll(body, hr.dstVars[i], bindVars2[i]);
        }

        for (int i = 0; i < hr.locVars.size(); i++)
        {
          Expr new_name = mkTerm<string> ("__loc_var_" + to_string(locVar_index++), m_efac);
          Expr var = cloneVar(hr.locVars[i], new_name);

          body = replaceAll(body, hr.locVars[i], var);
        }

        ssa.push_back(body);
        bindVars.push_back(bindVars2);
        bindVars1 = bindVars2;
      }

      return conjoin(ssa, m_efac);
    }

    bool exploreTraces(int cur_bnd, int bnd, bool print = false)
    {
      bool unsat = true;
      int num_traces = 0;

      if (print) outs () << "Exploring traces (up to bound): 1";     // GF: trace of length 1 is always empty
      while (unsat && cur_bnd <= bnd)
      {
        if (print) outs () << ", " << cur_bnd;
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

      if (print)
        outs () << "\nTotal number of traces explored: " << num_traces << "\n\n"
              << (unsat ? "UNSAT for all traces up to " : "SAT for a trace with ")
              << (cur_bnd - 1) << " steps\n";
      return unsat;
    }

    bool kIndIter(int bnd1, int bnd2)
    {
      assert (bnd1 <= bnd2);
      assert (bnd2 > 1);
      bool init = exploreTraces(bnd1, bnd2);
      if (!init)
      {
        outs() << "Base check failed at step " << bnd2 << "\n";
        exit(0);
      }

      k_ind = ruleManager.chcs.size(); // == 3

      for (int i = 0; i < k_ind; i++)
      {
        auto & r = ruleManager.chcs[i];
        if (r.isInductive) tr_ind = i;
        if (r.isQuery) pr_ind = i;
      }

      ruleManager.chcs.push_back(HornRuleExt());   // trick for now: a new artificial CHC
      HornRuleExt& hr = ruleManager.chcs[k_ind];
      HornRuleExt& tr = ruleManager.chcs[tr_ind];
      HornRuleExt& pr = ruleManager.chcs[pr_ind];

      hr.srcVars = tr.srcVars;
      hr.dstVars = tr.dstVars;
      hr.locVars = tr.locVars;

      hr.body = mk<AND>(tr.body, mkNeg(pr.body));

      if (extraLemmas != NULL) hr.body = mk<AND>(extraLemmas, hr.body);

      for (int i = 0; i < hr.srcVars.size(); i++)
      {
        hr.body = replaceAll(hr.body, pr.srcVars[i], hr.srcVars[i]);
      }

      vector<int> gen_trace;
      for (int i = 1; i < bnd2; i++) gen_trace.push_back(k_ind);
      gen_trace.push_back(pr_ind);
      Expr q = toExpr(gen_trace);
      bool res = !u.isSat(q);

      if (bnd2 == 2) inv = mkNeg(pr.body);

      // prepare for the next iteration
      ruleManager.chcs.erase (ruleManager.chcs.begin() + k_ind);

      return res;
    }

    Expr getInv() { return inv; }

    Expr getBoundedItp(int k)
    {
      assert(k >= 0);

      int fc_ind;
      for (int i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto & r = ruleManager.chcs[i];
        if (r.isInductive) tr_ind = i;
        if (r.isQuery) pr_ind = i;
        if (r.isFact) fc_ind = i;
      }

      HornRuleExt& fc = ruleManager.chcs[fc_ind];
      HornRuleExt& tr = ruleManager.chcs[tr_ind];
      HornRuleExt& pr = ruleManager.chcs[pr_ind];

      Expr prop = pr.body;
      Expr init = fc.body;
      for (int i = 0; i < tr.srcVars.size(); i++)
      {
        init = replaceAll(init, tr.dstVars[i],  tr.srcVars[i]);
      }

      Expr itp;

      if (k == 0)
      {
        itp = getItp(init, prop);
      }
      else
      {
        vector<int> trace;
        for (int i = 0; i < k; i++) trace.push_back(tr_ind);

        Expr unr = toExpr(trace);
        for (int i = 0; i < pr.srcVars.size(); i++)
        {
          prop = replaceAll(prop, pr.srcVars[i], bindVars.back()[i]);
        }
        itp = getItp(unr, prop);
        if (itp != NULL)
        {
          for (int i = 0; i < pr.srcVars.size(); i++)
          {
            itp = replaceAll(itp, bindVars.back()[i], pr.srcVars[i]);
          }
        }
        else
        {
          itp = getItp(init, mk<AND>(unr, prop));
        }
      }
      return itp;
    }

    //used for multiple loops to unroll inductive clauses k times and collect corresponding models
    bool unrollAndExecuteMultiple(ufo::ZSolver<ufo::EZ3> & m_smt_solver,
				  map<Expr, vector<vector<int> > > & models, int k = 10)
    {
      vector<int> traces;
      map<int, Expr> indexToInv;
      int chcIndex = 0;

      for (auto & r : ruleManager.chcs) {
	if (r.isInductive) {
	  for (int i = 0; i < k; i++) {
	    traces.push_back(chcIndex);
	    indexToInv[traces.size()-1] = r.srcRelation;
	  }
	  chcIndex++;
	} else if (r.isQuery) {
	  chcIndex++;
	  continue;
	} else {
	  //fact or non-inductive clauses
	  traces.push_back(chcIndex++);
	}
      }

      Expr unrolledTr = toExpr(traces);

      m_smt_solver.reset();
      m_smt_solver.assertExpr(unrolledTr);

      if (!m_smt_solver.solve()) {
	cout << unrolledTr << " found to be unsat with k = " << k << endl;
	return false;
      }

      ZSolver<EZ3>::Model m = m_smt_solver.getModel();

      for (int bvIndex = 0; bvIndex < bindVars.size(); bvIndex++) {
	auto invItr = indexToInv.find(bvIndex);
	if (invItr == indexToInv.end()) {
	  continue;
	}
	
	auto vars = bindVars[bvIndex];
	vector<int> model;
	for (auto var : vars) {
	  int value;
	  if (var != m.eval(var)) {
	    stringstream tmpstream;
	    tmpstream << m.eval(var);
	    tmpstream >> value;
	  } else {
	    value = guessUniformly(1000)-500;
	  }
	  model.push_back(value);
	}
	models[invItr->second].push_back(model);
      }

      return true;
    }
    
    bool unrollAndExecute(const Expr & invRel, ufo::ZSolver<ufo::EZ3> & m_smt_solver, vector<vector<int> > & models, int k = 10, Expr initCondn = nullptr)
    {

      int initIndex;
      int trIndex;
      bool initFound = false;

      for (int i = 0; i < ruleManager.chcs.size(); i++) {
        auto & r = ruleManager.chcs[i];
        if (r.isFact) {
	  initIndex = i;
	  initFound = true;
	}
	if (r.isInductive && r.srcRelation == invRel && r.dstRelation == invRel) {
	  trIndex = i;
	}
      }

      if (!initFound && initCondn == nullptr) {
	cout << "ERR: init not found for given transition (index: " << trIndex << ")" << endl;
	return false;
      }
      
      Expr init = initCondn == nullptr ? ruleManager.chcs[initIndex].body : initCondn;

      HornRuleExt& tr = ruleManager.chcs[trIndex];

      for (int i = 0; i < tr.srcVars.size(); i++) {
	init = replaceAll(init, tr.dstVars[i], tr.srcVars[i]);
      }

	
      vector<int> trace;
      for (int i = 0; i < k; i++) {
	trace.push_back(trIndex);
      }

      Expr unrolledTr = toExpr(trace);

      //      cout << init << " && " << unrolledTr << endl;

      m_smt_solver.reset();
      m_smt_solver.assertExpr(init);
      m_smt_solver.assertExpr(unrolledTr);

      if (!m_smt_solver.solve()) {
	cout << init << " && " << unrolledTr << "\nfound to be unsat\n";
	return false;
      }

      ZSolver<EZ3>::Model m = m_smt_solver.getModel();
      
      for (auto vars : bindVars) {
	vector<int> model;
	for (auto var : vars) {
	  int value;
	  if (var != m.eval(var)) {
	    stringstream tmpstream;
	    tmpstream << m.eval(var);
	    tmpstream >> value;
	  } else {
	    value = guessUniformly(1000)-500;
	    cout << "random guess for: " << var << endl; //DEBUG
	  }
	  cout << value << "\t";//DEBUG
	  model.push_back(value);
	}
	cout << endl;//DEBUG
	models.push_back(model);
      }

      return true;
    }
  };

  inline void unrollAndCheck(string smt, int bnd1, int bnd2)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    BndExpl ds(ruleManager);
    ds.exploreTraces(bnd1, bnd2, true);
  };

  inline bool kInduction(CHCs& ruleManager, int bnd)
  {
    if (ruleManager.chcs.size() != 3)
    {
      outs () << "currently not supported\n";
      return false;
    }

    BndExpl ds(ruleManager);

    bool success = false;
    int i;
    for (i = 2; i < bnd; i++)
    {
      if (ds.kIndIter(i, i))
      {
        success = true;
        break;
      }
    }

    outs () << "\n" <<
      (success ? "K-induction succeeded " : "Unknown result ") <<
      "after " << (i-1) << " iterations\n";

    return success;
  };

  inline void kInduction(string smt, int bnd)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    kInduction(ruleManager, bnd);
  };
}

#endif
