#ifndef RNDLEARNERV3__HPP__
#define RNDLEARNERV3__HPP__

#include "RndLearner.hpp"

#ifdef HAVE_ARMADILLO
#include "DataLearner.hpp"
#endif

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
        if ((  (hr.srcRelation == rel &&
              find(checked.begin(), checked.end(), hr.dstRelation) != checked.end())
            || (hr.dstRelation == rel &&
              find(checked.begin(), checked.end(), hr.srcRelation) != checked.end())))
          if (!hr.isQuery && !checkCHC(hr)) return false; // TODO: use this knowledge somehow
      }
      return true;
    }

    bool checkInductiveness(Expr rel)
    {
      for (auto &hr: ruleManager.chcs)
      {
        if ((hr.srcRelation == rel && hr.dstRelation == rel) ||
            (hr.srcRelation == rel && find(checked.begin(), checked.end(), hr.dstRelation) != checked.end()) ||
            (hr.dstRelation == rel && find(checked.begin(), checked.end(), hr.srcRelation) != checked.end()))
          if (!hr.isQuery && !checkCHC(hr)) return false;
      }
      return true;
    }

    Expr eliminateQuantifiers(Expr formula, ExprVector& varsRenameFrom, int invNum)
    {
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
        for (auto & v : invarVars[invNum]) newCand = replaceAll(newCand, varsRenameFrom[v.first], v.second);
        return newCand;
      }
      return mk<TRUE>(m_efac);
    }

    bool getCandForAdjacentRel(Expr candToProp, Expr constraint, ExprVector& varsRenameFrom, Expr rel)
    {
      Expr formula = mk<AND>(candToProp, constraint);
      if (findNonlin(formula))
      {
        // Currently unsupported,
        // Cannot propagate anything,
        // So simply try checking if "TRUE" is OK
        if (checkAllAdjacent(rel)){
          checked.insert(rel);
          return true;
        }
        return false;
      }

      ExprSet dsjs;
      getDisj(candToProp, dsjs);
      ExprSet newSeedDsjs;
      int invNum = getVarIndex(rel, decls);

      for (auto & d : dsjs)
        newSeedDsjs.insert(eliminateQuantifiers(mk<AND>(d, constraint), varsRenameFrom, invNum));

      Expr newCand = disjoin(newSeedDsjs, m_efac);

      // reserve
      ExprSet checkedTmp = checked;
      map<int, Expr> candidatesTmp = candidates;

      if (!isOpX<TRUE>(newCand))
      {
        ExprSet cnjs;
        getConj(newCand, cnjs);
        bool resFinal = false;
        if (cnjs.size() > 1)
        {
          resFinal = false;
          for (auto & a : cnjs) // TODO: Houdini style
          {
            candidates[invNum] = a;
            if (!checkAllAdjacent(rel)) {
              candidates = candidatesTmp;
              continue;
            }

            bool res = checkCand(invNum, a);
            if (res)
            {
              checkedTmp = checked;
              candidatesTmp = candidates;
            }
            else
            {
              checked = checkedTmp;
              candidates = candidatesTmp;
            }
            resFinal = resFinal || res;
          }
        }
        else
        {
          resFinal = checkCand(invNum, newCand);
        }

        if (resFinal) return true;
        checked = checkedTmp;
        candidates = candidatesTmp;
        if (checkAllAdjacent(rel)){
          checked.insert(rel);
          return true;
        }
        return false;
      }
      else return true;
    }

    // similar to getCandForAdjacentRel, but not recursive
    Expr getSeedsByQE(Expr candToProp, Expr constraint, ExprVector& varsRenameFrom, Expr rel)
    {
      Expr formula = mk<AND>(candToProp, constraint);
      if (findNonlin(formula)) return mk<TRUE>(m_efac);
      ExprSet dsjs;
      getDisj(candToProp, dsjs);
      ExprSet newSeedDsjs;
      for (auto & d : dsjs)
        newSeedDsjs.insert(eliminateQuantifiers(mk<AND>(d, constraint), varsRenameFrom, getVarIndex(rel, decls)));

      return disjoin(newSeedDsjs, m_efac);
    }

    // TODO: try propagating learned lemmas too
    bool propagate(int invNum, Expr cand)
    {
      bool res = true;
      Expr rel = decls[invNum];
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.srcRelation == hr.dstRelation) continue;

        // forward:
        if (hr.srcRelation == rel && find(checked.begin(), checked.end(), hr.dstRelation) == checked.end() && !hr.isQuery)
        {
          Expr replCand = cand;
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.srcVars[v.first]);
          res = res && getCandForAdjacentRel (replCand, hr.body, hr.dstVars, hr.dstRelation);
        }

        // backward (very similarly):
        if (hr.dstRelation == rel && find(checked.begin(), checked.end(), hr.srcRelation) == checked.end() && !hr.isFact)
        {
          Expr replCand = cand;
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.dstVars[v.first]);
          res = res && getCandForAdjacentRel (replCand, hr.body, hr.srcVars, hr.srcRelation);
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
      return propagate(curInv, cand);
    }

    bool learn (int curInv, Expr cand)
    {
      if (checkCand(curInv, cand))
      {
        for (auto & a : candidates)
        {
          if (a.second != NULL && !isOpX<TRUE>(a.second))
          {
            SamplFactory& sf = sfs[a.first].back();
            sf.learnedExprs.insert(a.second); // TODO: split conjunctions
//            outs() << "     lemmas learned for " << *decls[a.first] << ": " << *a.second << "\n";
          }
        }

        if (checkAllLemmas(false))
        {
          return true;
        }
        else
        {
          for (auto & a : candidates)
          {
            if (a.second != NULL && !isOpX<TRUE>(a.second))
            {
              SamplFactory& sf = sfs[a.first].back();
              Sampl& s = sf.exprToSampl(cand);  // TODO: split conjunctions
              sf.assignPrioritiesForLearned();
            }
          }
        }
      }
      return false;
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

        if (learn(curInv, cand))
        {
          outs () << "Success after " << (i+1) << " iterations\n";
          return;
        }

        // next cand (to be sampled)
        curInv = (curInv + 1) % invNumber;
        // just natural order; TODO: find a smarter way to calculate; make parametrizable
      }
    }

    // similar to propagate, but not recursive and w/o checking
    void propagateSeeds(int invNum, Expr cand, map<Expr, ExprSet>& cands)
    {
      Expr rel = decls[invNum];
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.srcRelation == hr.dstRelation) continue;

        if (hr.srcRelation == rel && find(checked.begin(), checked.end(), hr.dstRelation) == checked.end() && !hr.isQuery)
        {
          Expr replCand = cand;
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.srcVars[v.first]);
          Expr newcand = getSeedsByQE (replCand, hr.body, hr.dstVars, hr.dstRelation);
//          outs () << " propagated seed for " << *hr.dstRelation << ": " << *newcand << "\n";
          cands[hr.dstRelation].insert(newcand);
        }

        if (hr.dstRelation == rel && find(checked.begin(), checked.end(), hr.srcRelation) == checked.end() && !hr.isFact)
        {
          Expr replCand = cand;
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.dstVars[v.first]);
          Expr newcand = getSeedsByQE (replCand, hr.body, hr.srcVars, hr.srcRelation);
//          outs () << " propagated seed for " << *hr.srcRelation << ": " << *newcand << "\n";
          cands[hr.srcRelation].insert(newcand);
        }
      }
    }

    // adapted from doSeedMining
    void getSeeds(Expr invRel, map<Expr, ExprSet>& cands)
    {
      int ind = getVarIndex(invRel, decls);
      SamplFactory& sf = sfs[ind].back();
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != invRel && hr.srcRelation != invRel) continue;
        SeedMiner sm (hr, invRel, invarVars[ind], sf.lf.nonlinVars);
        sm.analyzeCode();
        for (auto &cand : sm.candidates)
        {
//          outs () << "seed for " << *invRel << ": " << *cand << "\n";
          cands[invRel].insert(cand);
          propagateSeeds(ind, cand, cands);
        }
      }
    }

#ifdef HAVE_ARMADILLO
    void getDataCandidates(map<Expr, ExprSet>& cands, const vector<string> & behaviorfiles){
      int fileIndex = 0;
      for (auto & dcl : decls) {
	DataLearner dl(ruleManager, m_z3);
	dl.initialize(dcl);
	string filename("");
	if (fileIndex < behaviorfiles.size()) {
	  filename = behaviorfiles[fileIndex];
	  fileIndex++;
	}
	if (!dl.computeData(filename)) return;
	(void)dl.computePolynomials(cands[dcl]);
      }	  
    }
#endif

    bool bootstrap(map<Expr, ExprSet>& cands, bool enableDataLearning, const vector<string> & behaviorfiles){
      if (enableDataLearning) {
#ifdef HAVE_ARMADILLO
	getDataCandidates(cands, behaviorfiles);
#else
	outs() << "Skipping learning from data as required library(armadillo) not found\n";
#endif
      }

      // TODO: batching
      for (auto & dcl: decls) {
        for (auto & cand : cands[dcl]) {
          checked.clear();
          candidates.clear();
          if (learn(getVarIndex(dcl, decls), cand)) {
            outs () << "Success after bootstrapping\n";
            return true;
          }
        }
      }
      return false;
    }

    bool checkAllLemmas(bool addCand = true)
    {
      candidates.clear();
      for (auto &hr: ruleManager.chcs)
      {
        if (!checkCHC(hr, addCand)) {
          if (!hr.isQuery)
            assert(0);    // only queries are allowed to fail
          else
            return false; // TODO: use this fact somehow
        }
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr, bool addCand = true)
    {
      m_smt_solver.reset();
      m_smt_solver.assertExpr (hr.body);

      if (!hr.isFact)
      {
        int ind = getVarIndex(hr.srcRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        Expr lmApp = sf.getAllLemmas();
        if (addCand && candidates[ind] != NULL) lmApp = mk<AND>(lmApp, candidates[ind]);
        for (auto & v : invarVars[ind]) lmApp = replaceAll(lmApp, v.second, hr.srcVars[v.first]);
        m_smt_solver.assertExpr(lmApp);
      }

      if (!hr.isQuery)
      {
        int ind = getVarIndex(hr.dstRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        Expr lmApp = sf.getAllLemmas();
        if (addCand && candidates[ind] != NULL) lmApp = mk<AND>(lmApp, candidates[ind]);
        for (auto & v : invarVars[ind]) lmApp = replaceAll(lmApp, v.second, hr.dstVars[v.first]);
        m_smt_solver.assertExpr(mk<NEG>(lmApp));
      }

      return !m_smt_solver.solve ();
    }
  };

  inline void learnInvariants3(string smt, char * outfile, int maxAttempts, bool freqs, bool aggp, bool enableDataLearning, const vector<string> & behaviorfiles)
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

    map<Expr, ExprSet> cands;
    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl);
    for (auto& dcl: ruleManager.decls) ds.getSeeds(dcl->arg(0), cands);
    for (auto& dcl: ruleManager.decls) ds.doSeedMining(dcl->arg(0), cands[dcl->arg(0)]);

    ds.calculateStatistics();
    if (ds.bootstrap(cands, enableDataLearning, behaviorfiles)) return;
    ds.synthesize(maxAttempts, outfile);
  }
}

#endif
