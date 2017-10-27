#ifndef RNDLEARNERV2__HPP__
#define RNDLEARNERV2__HPP__

#include "Horn.hpp"
#include "CodeSampler.hpp"
#include "Distribution.hpp"
#include "LinCom.hpp"
#include "BndExpl.hpp"
#include "RndLearner.hpp"
#include "ae/SMTUtils.hpp"
#include <iostream>
#include <fstream>

using namespace std;
using namespace boost;
namespace ufo
{
  class RndLearnerV2 : public RndLearner
  {
    private:

    map<Expr, ExprSet> modelsOfFailures;

    vector<HornRuleExt*> tr;
    vector<HornRuleExt*> fc;
    vector<HornRuleExt*> qr;

    public:

    RndLearnerV2 (ExprFactory &efac, EZ3 &z3, CHCs& r, bool freqs, bool aggp) :
      RndLearner (efac, z3, r, /*k-induction*/ false, freqs, /*epsilon*/ true, aggp){}

    Expr getModel(ExprVector& vars)
    {
      ExprVector eqs;
      ZSolver<EZ3>::Model m = m_smt_solver.getModel();
      for (auto & v : vars) if (v != m.eval(v))
      {
        eqs.push_back(mk<EQ>(v, m.eval(v)));
      }
      else
      {
        eqs.push_back(mk<EQ>(v, mkTerm (mpz_class (guessUniformly (1000)-500), m_efac)));
      }
      return conjoin (eqs, m_efac);
    }

    ExprSet& getLearntLemmas(int num)
    {
      return lfs[num].back().learntExprs;
    }

    void categorizeCHCs()
    {
      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr.push_back(&a);
        else if (a.isFact) fc.push_back(&a);
        else if (a.isQuery) qr.push_back(&a);
    }

    int redundancyCheck (ExprVector& lemmas)
    {
      int num = 0;
      LAfactory& lf = lfs[0].back();
      Expr allLemmas = conjoin(lf.learntExprs, m_efac);
      for (auto & l : lemmas)
      {
        LAdisj lcs;
        if (lf.exprToLAdisj(l, lcs)) lf.assignPrioritiesForLearnt(lcs);

        numOfSMTChecks++;
        if (!u.isImplies(allLemmas, l))
        {
          lf.learntExprs.insert(l);
          num++;
        }
      }
      return num;
    }

    bool checkSafetyAndReset(HornRuleExt* qu)
    {
      m_smt_solver.reset();
      m_smt_solver.assertExpr (qu->body);

      int ind = getVarIndex(qu->srcRelation, decls);
      LAfactory& lf = lfs[ind].back();

      Expr lmApp = conjoin(lf.learntExprs, m_efac);
      for (int i = 0; i < qu->srcVars.size(); i++)
      {
        lmApp = replaceAll(lmApp, lf.getVarE(i), qu->srcVars[i]);
      }
      m_smt_solver.assertExpr(lmApp);

      numOfSMTChecks++;
      return !m_smt_solver.solve ();
    }

    void getIS(HornRuleExt* hr, ExprVector& candSet)
    {
      if (candSet.size() == 0) return;
      LAfactory& lf = lfs[0].back();

      Expr cands = conjoin (candSet, m_efac);

      for (int i = candSet.size() - 1; i >= 0; i--)
      {
        Expr candPrime = candSet[i];

        for (int j = 0; j < hr->srcVars.size(); j++)
        {
          candPrime = replaceAll(candPrime, hr->srcVars[j], hr->dstVars[j]);
        }

        m_smt_solver.reset();
        m_smt_solver.assertExpr (hr->body);
        m_smt_solver.assertExpr (cands);
        for (auto & a : lf.learntExprs) m_smt_solver.assertExpr (a);

        m_smt_solver.assertExpr (mk<NEG>(candPrime));

        numOfSMTChecks++;
        if (m_smt_solver.solve ())
        {
          modelsOfFailures[getModel(hr->srcVars)].insert(candSet[i]);

          // GF: to debug (esp. nonlin opers):
          LAdisj lcs;
          if (lf.exprToLAdisj(candSet[i], lcs)) lf.assignPrioritiesForGarbage(lcs);

          candSet.erase(candSet.begin() + i);

          getIS(hr, candSet);
          return;
        }
      }
      return;
    }

    bool initCheckCand(HornRuleExt* fc, Expr cand)
    {
      Expr candPrime = cand;

      for (int j = 0; j < fc->dstVars.size(); j++)
      candPrime = replaceAll(candPrime, lfs[0].back().getVarE(j), fc->dstVars[j]);

      m_smt_solver.reset();
      m_smt_solver.assertExpr (fc->body);
      m_smt_solver.assertExpr (mk<NEG>(candPrime));

      numOfSMTChecks++;
      return (!m_smt_solver.solve ());
    }

    bool houdini (ExprSet& cands, bool skipInit=false, bool print=false)
    {
      LAfactory& lf = lfs[0].back();
      ExprVector exprs;
      for (auto & a : cands) exprs.push_back(a);

      // initiation: remove crap first
      if (!skipInit)
      {
        for (auto a : fc)
          for (int i = exprs.size() - 1; i >= 0; i--)
          {
            if (!initCheckCand(a, exprs[i]))
            {
              LAdisj lcs;
              if (lf.exprToLAdisj(exprs[i], lcs)) lf.assignPrioritiesForFailed(lcs);
              exprs.erase(exprs.begin()+i);
            }
          }
      }

      // consecution
      for (auto a : tr) getIS(a, exprs);

      // safety:
      int num = exprs.size();
      int newLemmaAdded = redundancyCheck(exprs);

      if (newLemmaAdded == 0) return false;

      for (auto a : qr) if (!checkSafetyAndReset(a)) return false;

      return true;
    }

    bool synthesize(int maxAttempts, int batchSz, int scndChSz)
    {
      assert(lfs.size() == 1); // current limitation

      LAfactory& lf = lfs[0].back();

      ExprVector candsBatch;

      bool success = false;
      int iter = 1;
      int triggerSecondChance = 0;
      int numFailInit = 0;

      for (int i = 0; i < maxAttempts; i++)
      {
        candsBatch.clear();

        while (candsBatch.size() < batchSz)
        {
          Expr cand = lf.getFreshCandidate();
          if (cand == NULL) continue;

          if (isTautology(cand))  // keep searching
          {
            lf.assignPrioritiesForLearnt(lf.samples.back());
            continue;
          }

          if (lf.nonlinVars.size() > 0 && !u.isSat(cand))  // keep searching
          {
            lf.assignPrioritiesForFailed(lf.samples.back());
            continue;
          }

          iter++;

          bool toskip = false;
          for (auto a : fc)
            if (!initCheckCand(a, cand))
            {
              numFailInit++;
              lf.assignPrioritiesForFailed(lf.samples.back());
              toskip = true;
              break;
            }
          if (toskip) continue;

          candsBatch.push_back(cand);
        }

        for (auto a : tr) getIS(a, candsBatch);      // houdini

        if (candsBatch.size() == 0) continue;

        success = true;
        for (auto a : qr) success = success && checkSafetyAndReset(a);
        if (success) break;

        // second chance candidates
        triggerSecondChance += redundancyCheck(candsBatch);
        if (triggerSecondChance < scndChSz) continue;

        triggerSecondChance = 0;

        ExprSet secondChanceCands;
        for (auto it = modelsOfFailures.begin(); it != modelsOfFailures.end(); )
        {
          m_smt_solver.reset();
          m_smt_solver.assertExpr (it->first);
          for (auto & a : lfs[0].back().learntExprs) m_smt_solver.assertExpr (a);

          numOfSMTChecks++;
          if (!m_smt_solver.solve ()) // CE violated
          {
            for (auto & e : it->second) secondChanceCands.insert(e);
            modelsOfFailures.erase(it++);
          }
          else ++it;
        }

        if (secondChanceCands.size() > 0) success = houdini(secondChanceCands, true, true);
        if (success) break;
      }

      return success;
    }
  };
  
  inline void learnInvariants2(string smt, char * outfile, int maxAttempts,
                               int itp, int batch, int retry, bool freqs, bool aggp)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    RndLearnerV2 ds(m_efac, z3, ruleManager, freqs, aggp);
    ds.categorizeCHCs();

    std::srand(std::time(0));

    if (ruleManager.decls.size() > 1)
    {
      outs() << "WARNING: learning multiple invariants is currently unsupported in --v2.\n"
             << "         Run --v1\n";
      return;
    }

    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl);

    ExprSet cands;

    if (itp > 0) ds.bootstrapBoundedProofs(itp, cands);

    for (auto& dcl: ruleManager.decls) ds.doCodeSampling (dcl->arg(0), cands);

    bool success = ds.houdini(cands);
    outs () << "Number of bootstrapped lemmas: " << ds.getLearntLemmas(0).size() << "\n";
    if (success)
    {
      outs () << "Success after the bootstrapping\n";
    }
    else
    {
      for (auto& dcl: ruleManager.decls) ds.calculateStatistics(dcl->arg(0));

      success = ds.synthesize(maxAttempts, batch, retry);
      if (success) outs () << "Total number of learned lemmas: " << ds.getLearntLemmas(0).size() << "\n";

      if (success) outs () << "\nSuccess after the sampling\n";
      else         outs () << "\nNo success after " << maxAttempts << " iterations\n";
    }

    if (success && outfile != NULL)
    {
      vector<ExprSet> invs;
      invs.push_back(ds.getLearntLemmas(0));
      ds.serializeInvariants(invs, outfile);
    }
  }
}

#endif
