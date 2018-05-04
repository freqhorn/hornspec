#ifndef RNDLEARNERV3__HPP__
#define RNDLEARNERV3__HPP__

#include "RndLearner.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class RndLearnerV3 : public RndLearner
  {
    private:

    ExprSet checked;
    map<int, Expr> candidates;

    public:

    RndLearnerV3 (ExprFactory &efac, EZ3 &z3, CHCs& r, bool freqs, bool aggp) :
      RndLearner (efac, z3, r, /*k-induction*/ false, freqs, /*epsilon*/ true, aggp){}

    int getInductiveRule(Expr rel)
    {
      for (auto a : ruleManager.outgs[rel])
      {
        if (ruleManager.chcs[a].srcRelation == ruleManager.chcs[a].dstRelation)
          return a;
      }
      return -1;
    }

    bool checkInit(int invNum, Expr rel)
    {
      for (int i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto & a = ruleManager.chcs[i];
        if (a.isFact && a.dstRelation == rel)
        {
          bool res = checkCHC(a);
          if (!res)
          {
            SamplFactory& sf = sfs[invNum].back();
            Sampl& s = sf.exprToSampl(candidates[invNum]);
            sf.assignPrioritiesForFailed();
          }
          return res;
        }
      }
      return true;
    }

    bool checkAllAdjacent(Expr rel)
    {
      for (auto &hr: ruleManager.chcs)
      {
        if ((hr.srcRelation == rel || hr.dstRelation == rel) && !hr.isQuery)
          if (!checkCHC(hr)) return false; // TODO: use this knowledge somehow
      }
      return true;
    }
    
    bool checkInductiveness(Expr rel)
    {
      int indRule = getInductiveRule(rel);
      return (indRule == -1) ? checkAllAdjacent(rel) : checkCHC(ruleManager.chcs[indRule]);
    }

    bool getCandForAdjacentRel(Expr formula, ExprVector& varsRenameFrom, Expr rel)
    {
      if (findNonlin(formula))
      {
        // Currently unsupported,
        // Cannot propagate anything,
        // So simply try checking if "TRUE" is OK
        return checkAllAdjacent(rel);
      }

      ExprSet allVars;
      ExprSet quantified;
      expr::filter (formula, bind::IsConst(), std::inserter (allVars, allVars.begin ()));
      for (auto & v : allVars)
        if (find(varsRenameFrom.begin(), varsRenameFrom.end(), v) == varsRenameFrom.end())
          quantified.insert(v);

      AeValSolver ae(mk<TRUE>(m_efac), formula, quantified);
      if (ae.solve())
      {
        Expr newCand = ae.getValidSubset();
        if (newCand != NULL)
        {
          int invNum = getVarIndex(rel, decls);
          for (auto & v : invarVars[invNum]) newCand = replaceAll(newCand, varsRenameFrom[v.first], v.second);
          return checkCand(invNum, newCand);
        }
      }
      return false;
    }

    // TODO: try propagating learned lemmas too
    bool propagate(int invNum, Expr cand)
    {
      bool res = true;
      Expr rel = decls[invNum];
      for (int i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto & a = ruleManager.chcs[i];
        if (a.srcRelation == a.dstRelation) continue;

        // forward:
        if (a.srcRelation == rel && find(checked.begin(), checked.end(), a.dstRelation) == checked.end() && !a.isQuery)
        {
          Expr replCand = cand;
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, a.srcVars[v.first]);
          res = res && getCandForAdjacentRel (mk<AND> (replCand, a.body), a.dstVars, a.dstRelation);
        }

        // backward (very similarly):
        if (a.dstRelation == rel && find(checked.begin(), checked.end(), a.srcRelation) == checked.end() && !a.isFact)
        {
          Expr replCand = cand;
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, a.dstVars[v.first]);
          res = res && getCandForAdjacentRel (mk<AND> (replCand, a.body), a.srcVars, a.srcRelation);
        }
      }
      return res;
    }

    bool checkCand(int curInv, Expr cand)
    {
      Expr rel = decls[curInv];
//      outs () << "  -- cand for " << *rel << ": " << *cand << "\n";
      candidates[curInv] = cand;

      if (!checkInit(curInv, rel)) return false;
      if (!checkInductiveness(rel)) return false;
      
      checked.insert(rel);
      bool res = propagate(curInv, cand);
      if (res)
      {
//        outs() << "lemma learned for " << *rel << "\n";
        SamplFactory& sf = sfs[curInv].back();
        sf.learnedExprs.insert(cand);
        Sampl& s = sf.exprToSampl(cand);
        sf.assignPrioritiesForLearned();
      }
      return res;
    }

    void synthesize(int maxAttempts, char * outfile)
    {
      int curInv = 0;
      for (int i = 0; i < maxAttempts; i++)
      {
        checked.clear();
        candidates.clear();
        SamplFactory& sf = sfs[curInv].back();
        Expr cand = sf.getFreshCandidate();
        if (cand == NULL) continue;

        if (checkCand(curInv, cand) && checkAllLemmas()) {
          outs () << "Success after " << (i+1) << " iterations\n";
          return;
        }

        // next cand (to be sampled)
        curInv = (curInv + 1) % invNumber;
        // just natural order; TODO: find a smarter way to calculate; make parametrizable
      }
    }

    bool checkAllLemmas()
    {
      candidates.clear();
      for (auto &hr: ruleManager.chcs)
      {
        if (!checkCHC(hr)) {
          if (!hr.isQuery)
            assert(0);    // only queries are allowed to fail
          else
            return false; // TODO: use this fact somehow
        }
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr)
    {
      m_smt_solver.reset();
      m_smt_solver.assertExpr (hr.body);

      if (!hr.isFact)
      {
        int ind = getVarIndex(hr.srcRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        Expr lmApp = sf.getAllLemmas();
        if (candidates[ind] != NULL) lmApp = mk<AND>(lmApp, candidates[ind]);
        for (auto & v : invarVars[ind]) lmApp = replaceAll(lmApp, v.second, hr.srcVars[v.first]);
        m_smt_solver.assertExpr(lmApp);
      }

      if (!hr.isQuery)
      {
        int ind = getVarIndex(hr.dstRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        Expr lmApp = sf.getAllLemmas();
        if (candidates[ind] != NULL) lmApp = mk<AND>(lmApp, candidates[ind]);
        for (auto & v : invarVars[ind]) lmApp = replaceAll(lmApp, v.second, hr.dstVars[v.first]);
        m_smt_solver.assertExpr(mk<NEG>(lmApp));
      }

      return !m_smt_solver.solve ();
    }
  };

  inline void learnInvariants3(string smt, char * outfile, int maxAttempts, bool freqs, bool aggp)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    RndLearnerV3 ds(m_efac, z3, ruleManager, freqs, aggp);

    ds.setupSafetySolver();
    std::srand(std::time(0));

    if (ruleManager.decls.size() <= 1)
    {
      outs() << "This is an experimental thing for multiple invariants.\nFor a single invariant synthsis, run --v1 or --v2.\n";
      return;
    }

    ExprSet stub;
    for (auto& dcl: ruleManager.decls)
    {
      ds.initializeDecl(dcl);
      ds.doSeedMining(dcl->arg(0), stub);
    }

    ds.calculateStatistics();
    ds.synthesize(maxAttempts, outfile);
  }
}

#endif
