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
  class RndLearnerV3 : public RndLearnerV2
  {
    private:

    ExprSet checked;
    map<int, ExprVector> candidates;
    int updCount = 1;

    public:

    RndLearnerV3 (ExprFactory &efac, EZ3 &z3, CHCs& r, bool freqs, bool aggp) :
      RndLearnerV2 (efac, z3, r, freqs, aggp){}

    bool checkInit(int invNum, Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isFact && hr.dstRelation == rel)
        {
          adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    bool checkInductiveness(Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        bool checkedSrc = find(checked.begin(), checked.end(), hr.srcRelation) != checked.end();
        bool checkedDst = find(checked.begin(), checked.end(), hr.dstRelation) != checked.end();
        if ((hr.srcRelation == rel && hr.dstRelation == rel) ||
            (hr.srcRelation == rel && checkedDst) ||
            (hr.dstRelation == rel && checkedSrc) ||
            (checkedSrc && checkedDst) ||
            (hr.isFact && checkedDst))
        {
          if (!hr.isQuery) adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    Expr eliminateQuantifiers(Expr formula, ExprVector& varsRenameFrom, int invNum)
    {
      ExprSet allVars;
      ExprSet quantified;
      expr::filter (formula, bind::IsConst(), std::inserter (allVars, allVars.begin ()));
      for (auto & v : allVars)
        if (find(varsRenameFrom.begin(), varsRenameFrom.end(), v) == varsRenameFrom.end())
          quantified.insert(v);

      if (findNonlin(formula)) return simpleQE(formula, quantified);

      AeValSolver ae(mk<TRUE>(m_efac), formula, quantified);
      if (ae.solve())
      {
        Expr newCand = ae.getValidSubset();
        for (auto & v : invarVars[invNum]) newCand = replaceAll(newCand, varsRenameFrom[v.first], v.second);
        return newCand;
      }
      return mk<TRUE>(m_efac);
    }

    bool getCandForAdjacentRel(Expr candToProp, Expr constraint, ExprVector& varsRenameFrom, Expr rel, bool seed)
    {
      Expr formula = mk<AND>(candToProp, constraint);
      if (!u.isSat(formula)) return false; // sometimes, maybe we should return true.

      ExprSet dsjs;
      getDisj(candToProp, dsjs);
      ExprSet newSeedDsjs;
      int invNum = getVarIndex(rel, decls);

      for (auto & d : dsjs)
        newSeedDsjs.insert(eliminateQuantifiers(mk<AND>(d, constraint), varsRenameFrom, invNum));

      Expr newCand = disjoin(newSeedDsjs, m_efac);

      if (seed)
      {
        ExprSet cnjs;
        ExprSet newCnjs;
        getConj(newCand, cnjs);
        for (auto & cnd : cnjs)
        {
          newCnjs.insert(cnd);
          addCandidate(invNum, cnd);
        }

        newCand = conjoin(newCnjs, m_efac);
        checked.insert(rel);
        if (isOpX<TRUE>(newCand)) return true;
        else return propagate(invNum, newCand, true);
      }
      else
      {
        if (!isOpX<TRUE>(newCand))
        {
          ExprSet cnjs;
          getConj(newCand, cnjs);
          for (auto & a : cnjs) addCandidate(invNum, a);
          return checkCand(invNum);
        }
        else return true;
      }
    }

    void addCandidate(int invNum, Expr cnd)
    {
      for (auto & a : candidates[invNum])
      {
        if (u.isEquiv(a, cnd)) return;
      }
      candidates[invNum].push_back(cnd);
    }

    bool propagate(int invNum, Expr cand, bool seed)
    {
      bool res = true;
      Expr rel = decls[invNum];

      for (auto & hr : ruleManager.chcs)
      {
        if (hr.srcRelation == hr.dstRelation || hr.isQuery) continue;

        SamplFactory* sf1;
        SamplFactory* sf2;

        // adding lemmas to the body. GF: not sure if it helps
        Expr constraint = hr.body;
        sf2 = &sfs[getVarIndex(hr.dstRelation, decls)].back();
        Expr lm2 = sf2->getAllLemmas();
        for (auto & v : invarVars[getVarIndex(hr.dstRelation, decls)])
          lm2 = replaceAll(lm2, v.second, hr.dstVars[v.first]);
        constraint = mk<AND>(constraint, lm2);

        if (!hr.isFact)
        {
          sf1 = &sfs[getVarIndex(hr.srcRelation, decls)].back();
          constraint = mk<AND>(constraint, sf1->getAllLemmas());
        }

        // forward:
        if (hr.srcRelation == rel && find(checked.begin(), checked.end(), hr.dstRelation) == checked.end())
        {
          Expr replCand = cand;
          for (int i = 0; i < 3; i++) for (auto & v : sf1->lf.nonlinVars) replCand = replaceAll(replCand, v.second, v.first);
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.srcVars[v.first]);
          res = res && getCandForAdjacentRel (replCand, constraint, hr.dstVars, hr.dstRelation, seed);
        }

        // backward (very similarly):
        if (hr.dstRelation == rel && find(checked.begin(), checked.end(), hr.srcRelation) == checked.end() && !hr.isFact)
        {
          Expr replCand = cand;
          for (int i = 0; i < 3; i++) for (auto & v : sf2->lf.nonlinVars) replCand = replaceAll(replCand, v.second, v.first);
          for (auto & v : invarVars[invNum]) replCand = replaceAll(replCand, v.second, hr.dstVars[v.first]);
          res = res && getCandForAdjacentRel (replCand, constraint, hr.srcVars, hr.srcRelation, seed);
        }
      }
      return res;
    }

    bool checkCand(int invNum)
    {
      Expr rel = decls[invNum];
//            outs () << "  -- checkCand for " << *rel << ": " << *conjoin(candidates[invNum], m_efac) << "\n";
      if (!checkInit(invNum, rel)) return false;
      if (!checkInductiveness(rel)) return false;

      checked.insert(rel);
      return propagate(invNum, conjoin(candidates[invNum], m_efac), false);
    }

    void assignPrioritiesForLearned()
    {
      bool progress = true;
      for (auto & cand : candidates)
      {
        if (cand.second.size() > 0)
        {
          ExprVector invVars;
          SamplFactory& sf = sfs[cand.first].back();
          for (auto & a : invarVars[cand.first]) invVars.push_back(a.second);
          for (auto & b : cand.second)
          {
            Expr learnedCand = normalizeDisj(b, invVars);
            SamplFactory& sf = sfs[cand.first].back();
            Sampl& s = sf.exprToSampl(learnedCand);
            sf.assignPrioritiesForLearned();
            if (!u.implies(sf.getAllLemmas(), learnedCand))
            {
              sf.learnedExprs.insert(learnedCand);
//              outs() << "     lemmas learned for " << *decls[cand.first] << ": " << *learnedCand << "\n";
            }
            else progress = false;
          }
        }
      }
      //      if (progress) updateGrammars(); // GF: doesn't work great :(
    }

    void synthesize(int maxAttempts, char * outfile)
    {
      ExprSet cands;
      for (int i = 0; i < maxAttempts; i++)
      {
        // next cand (to be sampled)
        // TODO: find a smarter way to calculate; make parametrizable
        int invNum = getVarIndex(ruleManager.wtoDecls[i % ruleManager.wtoDecls.size()], decls);
        checked.clear();
        candidates.clear();
        SamplFactory& sf = sfs[invNum].back();
        Expr cand = sf.getFreshCandidate();
        if (cand == NULL) continue;

        addCandidate(invNum, cand);
        if (checkCand(invNum))
        {
          assignPrioritiesForLearned();
          if (checkAllLemmas())
          {
            outs () << "Success after " << (i+1) << " iterations\n";
            return;
          }
        }
      }
    }

    bool splitUnsatSets(ExprVector & src, ExprVector & dst1, ExprVector & dst2)
    {
      if (u.isSat(conjoin(src, m_efac))) return false;

      for (auto & a : src) dst1.push_back(a);

      for (auto it = dst1.begin(); it != dst1.end(); )
      {
        dst2.push_back(*it);
        it = dst1.erase(it);
        if (u.isSat(conjoin(dst1, m_efac))) break;
      }

      // now dst1 is SAT, try to get more things from dst2 back to dst1

      for (auto it = dst2.begin(); it != dst2.end(); )
      {
        if (!u.isSat(conjoin(dst1, m_efac), *it)) { ++it; continue; }
        dst1.push_back(*it);
        it = dst2.erase(it);
      }

      return true;
    }

    bool filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(conjoin(candidates[i], m_efac)))
        {
          for (auto & hr : ruleManager.chcs)
          {
            if (hr.dstRelation == decls[i]) worklist.push_back(&hr);
          }
        }
      }

      // basically, just checks initiation and immediately removes bad candidates
      multiHoudini(worklist, false);

      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(conjoin(candidates[i], m_efac)))
        {
          ExprVector tmp;
          ExprVector stub; // TODO: try greedy search, maybe some lemmas are in stub?
          splitUnsatSets(candidates[i], tmp, stub);
          candidates[i] = tmp;
        }
      }

      return true;
    }

    bool multiHoudini(vector<HornRuleExt*> worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) return false;

      map<int, ExprVector> candidatesTmp = candidates;
      bool res1 = true;
      for (auto &h: worklist)
      {
        HornRuleExt& hr = *h;

        if (hr.isQuery) continue;

        if (!checkCHC(hr, candidatesTmp))
        {
          bool res2 = true;
          Expr model = getModel(hr.dstVars);
          int ind = getVarIndex(hr.dstRelation, decls);
          ExprVector& ev = candidatesTmp[ind];

          ExprVector invVars;
          for (auto & a : invarVars[ind]) invVars.push_back(a.second);
          SamplFactory& sf = sfs[ind].back();

          for (auto it = ev.begin(); it != ev.end(); )
          {
            Expr repl = *it;
            for (auto & v : invarVars[ind]) repl = replaceAll(repl, v.second, hr.dstVars[v.first]);

            if (!u.isSat(model, repl))
            {
              if (hr.isFact)
              {
                Expr failedCand = normalizeDisj(*it, invVars);
//                outs () << "failed cand for " << *hr.dstRelation << ": " << *failedCand << "\n";
                Sampl& s = sf.exprToSampl(failedCand);
                sf.assignPrioritiesForFailed();
              }
              it = ev.erase(it);
              res2 = false;
            }
            else
            {
              ++it;
            }
          }

          if (recur && !res2)
          {
            res1 = false;
            break;
          }
        }
      }
      candidates = candidatesTmp;
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    // adapted from doSeedMining
    void getSeeds(Expr invRel, map<Expr, ExprSet>& cands)
    {
      int ind = getVarIndex(invRel, decls);
      SamplFactory& sf = sfs[ind].back();
      ExprSet candsFromCode;
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != invRel && hr.srcRelation != invRel) continue;
        SeedMiner sm (hr, invRel, invarVars[ind], sf.lf.nonlinVars);
        sm.analyzeCode();
        for (auto &cand : sm.candidates) candsFromCode.insert(cand);
      }

      for (auto & cand : candsFromCode)
      {
        checked.clear();
        propagate (getVarIndex(invRel, decls), cand, true);
      }

      for (auto & a : candidates)
      {
        cands[decls[a.first]].insert(a.second.begin(), a.second.end());
      }
    }

    bool anyProgress(vector<HornRuleExt*> worklist)
    {
      bool res = false;
      for (int i = 0; i < invNumber; i++)
      {
        // simple check if there is a non-empty candidate
        for (auto & hr : worklist)
        {
          if (hr->srcRelation == decls[i] || hr->dstRelation == decls[i])
          {
            if (candidates[i].size() > 0) return true;
          }
        }
      }
      return res;
    }

#ifdef HAVE_ARMADILLO
    void getDataCandidates(map<Expr, ExprSet>& cands, const vector<string> & behaviorfiles){
      int fileIndex = 0;
      for (auto & dcl : decls) {
        DataLearner dl(ruleManager, m_z3);
        dl.initialize(dcl, true /*multipleLoops*/);
        string filename("");
        if (fileIndex < behaviorfiles.size()) {
          filename = behaviorfiles[fileIndex];
          fileIndex++;
        }
        if (!dl.computeData(filename)) continue;
        (void)dl.computePolynomials(cands[dcl]);
      }
    }
#endif

    bool bootstrap(map<Expr, ExprSet>& cands, bool enableDataLearning, const vector<string> & behaviorfiles){

      for (int i = 0; i < invNumber; i++)
      {
        for (auto & cnd : cands[decls[i]]) addCandidate(i, cnd);
      }

      filterUnsat();

      if (multiHoudini(ruleManager.wtoCHCs))
      {
        assignPrioritiesForLearned();
        if (checkAllLemmas())
        {
          outs () << "Success after bootstrapping\n";
          return true;
        }
      }
      return false;
    }

    void updateGrammars()
    {
      // convert candidates to curCandidates and run the method from RndLearner
      for (int ind = 0; ind < invNumber; ind++)
      {
        if (candidates[ind].size() == 0) curCandidates[ind] = mk<TRUE>(m_efac);
        else curCandidates[ind] = conjoin(candidates[ind], m_efac);
      }
      updateRels();
      updCount++;
    }

    bool checkAllLemmas()
    {
      candidates.clear();
      for (int i = ruleManager.wtoCHCs.size() - 1; i >= 0; i--)
      {
        auto & hr = *ruleManager.wtoCHCs[i];
        if (!checkCHC(hr, candidates)) {
          if (!hr.isQuery)
            assert(0);    // only queries are allowed to fail
          else
            return false; // TODO: use this fact somehow
        }
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr, map<int, ExprVector>& annotations)
    {
      m_smt_solver.reset();
      m_smt_solver.assertExpr (hr.body);

      if (!hr.isFact)
      {
        int ind = getVarIndex(hr.srcRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        Expr lmApp = sf.getAllLemmas();
        if (annotations[ind].size() > 0) lmApp = mk<AND>(lmApp, conjoin(annotations[ind], m_efac));
        for (auto & v : invarVars[ind]) lmApp = replaceAll(lmApp, v.second, hr.srcVars[v.first]);
        m_smt_solver.assertExpr(lmApp);
      }

      if (!hr.isQuery)
      {
        int ind = getVarIndex(hr.dstRelation, decls);
        SamplFactory& sf = sfs[ind].back();
        Expr lmApp = sf.getAllLemmas();
        if (annotations[ind].size() > 0) lmApp = mk<AND>(lmApp, conjoin(annotations[ind], m_efac));
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

    if (ruleManager.decls.size() == 1)
    {
      outs() << "WARNING.\n" <<
                "This is an experimental thing for multiple invariants.\n" <<
                "For a single invariant synthsis, we suggest to use the --v2 option.\n";
    }

    map<Expr, ExprSet> cands;
    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl);
    
    if (enableDataLearning) {
#ifdef HAVE_ARMADILLO
      ds.getDataCandidates(cands, behaviorfiles);
#else
      outs() << "Skipping learning from data as required library(armadillo) not found\n";
#endif
    }
    for (auto& dcl: ruleManager.decls) ds.getSeeds(dcl->arg(0), cands);
    for (auto& dcl: ruleManager.decls) ds.doSeedMining(dcl->arg(0), cands[dcl->arg(0)]);
    ds.calculateStatistics();
    if (ds.bootstrap(cands, enableDataLearning, behaviorfiles)) return;
    std::srand(std::time(0));
    ds.synthesize(maxAttempts, outfile);
  }
}

#endif
