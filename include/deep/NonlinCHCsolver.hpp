#ifndef NONLINCHCSOLVER__HPP__
#define NONLINCHCSOLVER__HPP__

#include "HornNonlin.hpp"

#include <fstream>
#include <chrono>
#include <queue>
// #include <stdlib.h>

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

  enum class Result_t {SAT=0, UNSAT, UNKNOWN};
  
  class NonlinCHCsolver
  {
    private:

    ExprFactory &m_efac;
    SMTUtils u;
    CHCs& ruleManager;
    int varCnt = 0;
    ExprVector ssaSteps;
    map<Expr, ExprSet> candidates;
    bool hasArrays = false;
    ExprSet declsVisited;
    map<HornRuleExt*, vector<ExprVector>> abdHistory;
    int globalIter = 0;
    int strenBound;
    bool debug = false;
    map<Expr, Expr> extend;
    ExprVector fixedRels;
    map<Expr, vector<int> > reachChcs;
    string SYGUS_BIN;

    public:

    NonlinCHCsolver (CHCs& r, int _b) : m_efac(r.m_efac), ruleManager(r), u(m_efac), strenBound(_b), SYGUS_BIN("") {}

    bool checkAllOver (bool checkQuery = false)
    {
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery && !checkQuery) continue;
        if (!checkCHC(hr, candidates)) return false;
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr, map<Expr, ExprSet>& annotations)
    {
      ExprSet checkList;
      checkList.insert(hr.body);
      Expr rel;
      for (int i = 0; i < hr.srcRelations.size(); i++)
      {
        Expr rel = hr.srcRelations[i];
        ExprSet lms = annotations[rel];
        Expr overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars[i]);
        getConj(overBody, checkList);
      }
      if (!hr.isQuery)
      {
        rel = hr.dstRelation;
        ExprSet negged;
        ExprSet lms = annotations[rel];
        for (auto a : lms) negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
        checkList.insert(disjoin(negged, m_efac));
      }
      return bool(!u.isSat(checkList));
    }

    void shrinkCnjs(ExprSet & cnjs)
    {
      ExprSet shrunk;
      ExprSet cnjsTmp = cnjs;
      for (auto c1 = cnjsTmp.begin(); c1 != cnjsTmp.end(); ++c1)
      {
        if (isOpX<OR>(*c1)) continue;
        for (auto c2 = cnjs.begin(); c2 != cnjs.end();)
        {
          if (!isOpX<OR>(*c2)) { ++c2; continue; };
          ExprSet dsjs;
          ExprSet newDsjs;
          getDisj(*c2, dsjs);
          for (auto & d : dsjs)
            if (u.isSat(*c1, d))
              newDsjs.insert(d);
          shrunk.insert(disjoin(newDsjs, m_efac));
          c2 = cnjs.erase(c2);
          cnjs.insert(disjoin(newDsjs, m_efac));
        }
        cnjs.insert(shrunk.begin(), shrunk.end());
        shrunk.clear();
      }
    }

    void preproGuessing(Expr e, ExprVector& ev1, ExprVector& ev2, ExprSet& guesses, bool backward = false, bool mutate = true)
    {
      if (!containsOp<FORALL>(e)) e = rewriteSelectStore(e);
      ExprSet complex;
      findComplexNumerics(e, complex);
      ExprMap repls;
      ExprMap replsRev;
      map<Expr, ExprSet> replIngr;
      for (auto & a : complex)
      {
        Expr repl = bind::intConst(mkTerm<string>
              ("__repl_" + lexical_cast<string>(repls.size()), m_efac));
        repls[a] = repl;
        replsRev[repl] = a;
        ExprSet tmp;
        filter (a, bind::IsConst (), inserter (tmp, tmp.begin()));
        replIngr[repl] = tmp;
      }
      Expr eTmp = replaceAll(e, repls);

      ExprSet ev3;
      filter (eTmp, bind::IsConst (), inserter (ev3, ev3.begin())); // prepare vars
      for (auto it = ev3.begin(); it != ev3.end(); )
      {
        if (find(ev1.begin(), ev1.end(), *it) != ev1.end()) it = ev3.erase(it);
        else
        {
          Expr tmp = replsRev[*it];
          if (tmp == NULL) ++it;
          else
          {
            ExprSet tmpSet = replIngr[*it];
            minusSets(tmpSet, ev1);
            if (tmpSet.empty()) it = ev3.erase(it);
            else ++it;
          }
        }
      }

      eTmp = eliminateQuantifiers(eTmp, ev3);
      if (backward) eTmp = mkNeg(eTmp);
      eTmp = simplifyBool(simplifyArithm(eTmp, false, true));

      ExprSet tmp;

      if (mutate)
        mutateHeuristic(eTmp, tmp);
      else
        getConj(eTmp, tmp);

      for (auto g : tmp)
      {
        g = replaceAll (g, replsRev);
        if (!ev2.empty())
          g = replaceAll(g, ev1, ev2);
        guesses.insert(g);
      }
    }

    bool isFixedRel(const Expr & rel)
    {
      return find(fixedRels.begin(), fixedRels.end(), rel) != fixedRels.end(); 
    }

    void addFixedRel(Expr rel)
    {
      fixedRels.push_back(rel);
    }

    // search for a CHC having the form r1 /\ .. /\ rn => rel, where rel \not\in {r1, .., rn}
    bool hasNoDef(Expr rel)
    {
      for (auto & hr : ruleManager.chcs)
        if (hr.dstRelation == rel &&
          find (hr.srcRelations.begin(), hr.srcRelations.end(), rel) == hr.srcRelations.end())
            return false;
      return true;
    }

    // lightweight (non-inductive) candidate propagation both ways
    // subsumes bootstrapping (ssince facts and queries are considered)
    void propagate(bool fwd = true)
    {
      // outs() << "Entry\n";//DEBUG
      // printCands(false);//DEBUG
      int szInit = declsVisited.size();
      for (auto & hr : ruleManager.chcs)
      {
	// outs() << "hrd: " << *(hr.dstRelation) << "\n";//DEBUG

        bool dstVisited = declsVisited.find(hr.dstRelation) != declsVisited.end();
        bool srcVisited = hr.isFact || (hr.isInductive && hasNoDef(hr.dstRelation) && extend.find(hr.dstRelation) == extend.end());
        bool dstFixed = isFixedRel(hr.dstRelation);

	// outs() << "sv: " << srcVisited << " fwd: " << fwd << " dv: " << dstVisited << "\n";//DEBUG

        for (auto & a : hr.srcRelations)
          srcVisited |= declsVisited.find(a) != declsVisited.end();

	// outs() << "sv: " << srcVisited << " fwd: " << fwd << " dv: " << dstVisited << "\n";//DEBUG
        if (fwd && srcVisited && !dstVisited && !dstFixed)
        {
          propagateCandidatesForward(hr);
          declsVisited.insert(hr.dstRelation);
        }
        else if (!fwd && !hr.isInductive && !srcVisited && dstVisited)
        {
          propagateCandidatesBackward(hr);
          declsVisited.insert(hr.srcRelations.begin(), hr.srcRelations.end());
        }
	// printCands(false);//DEBUG
      }

      if (declsVisited.size() != szInit) propagate(fwd);
      // outs() << "Exit\n";//DEBUG
      // printCands(false);//DEBUG
    }

    void propagateCandidatesForward(HornRuleExt& hr)
    {
//      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery) return;

        Expr body = getQuantifiedCands(true, hr);

        ExprSet all;
        all.insert(body);
        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          Expr rel = hr.srcRelations[i];
          if (!hasArrays) // we need "clean" invariants in the case of arrays (to be used as ranges)
          {
            // currently, tries all candidates; but in principle, should try various subsets
            for (auto & c : candidates[rel])
              all.insert(replaceAll(c, ruleManager.invVars[rel], hr.srcVars[i]));
          }
        }

	// //DEBUG
	// for (auto c : candidates[hr.dstRelation])
	//   outs() << "before: " << *c << "\n";

        if (hr.isInductive)   // get candidates of form [ <var> mod <const> = <const> ]
          retrieveDeltas (body, hr.srcVars[0], hr.dstVars, candidates[hr.dstRelation]);

        preproGuessing(conjoin(all, m_efac), hr.dstVars, ruleManager.invVars[hr.dstRelation], candidates[hr.dstRelation]);
	// //DEBUG
	// for (auto c : candidates[hr.dstRelation])
	//   outs() << "after: " << *c << "\n";
      }
    }

    void propagateCandidatesBackward(HornRuleExt& hr, bool forceConv = false)
    {
      // outs() << "in backward\n";//DEBUG
//      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isFact) return;

        Expr dstRel = hr.dstRelation;
        ExprVector& rels = hr.srcRelations;

        ExprVector invVars;
        ExprVector srcVars;

        // identifying nonlinear cases (i.e., when size(occursNum[...]) > 1)
        map<Expr, set<int>> occursNum;
        for (int i = 0; i < rels.size(); i++)
        {
          occursNum[rels[i]].insert(i);
          for (int j = i+1; j < rels.size(); j++)
            if (rels[i] == rels[j])
              occursNum[rels[i]].insert(j);
        }

        for (int i = 0; i < hr.srcVars.size(); i++)
          srcVars.insert(srcVars.end(), hr.srcVars[i].begin(), hr.srcVars[i].end());

        if (hr.srcVars.size() == 1) invVars = ruleManager.invVars[rels[0]];

        ExprSet cands;
        if (hr.isQuery)
        {
          if (getQuantifiedCands(false, hr) == NULL) return;
          else cands.insert(mk<FALSE>(m_efac));
        }
        else cands.insert(simplifyBool(conjoin(candidates[dstRel], m_efac)));

        ExprSet mixedCands;
        ExprVector curCnd;

        for (int i = 0; i < rels.size(); i++)
        {
          ExprSet tmp;
          getConj(replaceAll(conjoin(candidates[rels[i]], m_efac),
                             ruleManager.invVars[rels[i]], hr.srcVars[i]), tmp);
          curCnd.push_back(conjoin(tmp, m_efac));
        }

        // actually, just a single candidate, in the most recent setting;
        // TODO: remove the loop (or find use of it)
        for (auto & c : cands)
        {
          ExprSet all, newCnd;
          all.insert(hr.body);
          all.insert(mkNeg(replaceAll(c, ruleManager.invVars[dstRel], hr.dstVars)));
          all.insert(curCnd.begin(), curCnd.end());

          // TODO: add more sophisticated blocking based on unseccussful tries from abdHistory

          preproGuessing(conjoin(all, m_efac), srcVars, invVars, newCnd, true, false);

          if (!(u.isSat(conjoin(curCnd, m_efac), conjoin(newCnd, m_efac))))
          {
            // simple heuristic: find if some current guess was already created by abduction
            // then, delete it and try again
            if (!hr.isInductive)
              for (auto & t : abdHistory[&hr])
                for (int j = 0; j < t.size(); j++)
                  if (u.implies(conjoin(candidates[rels[j]], m_efac), t[j]))
                    candidates[rels[j]].clear();
            continue;
          }

          // oftentimes, newCnd is a disjunction that can be simplified
          // by considering other candidates in curCnd
          ExprSet tmp, tmp2;
          for (auto c : newCnd) getConj(c, tmp);
          for (auto c : curCnd) getConj(c, tmp);
          shrinkCnjs(tmp);
          getConj(conjoin(tmp, m_efac), tmp2);
          ineqMerger(tmp2, true);
          simplifyPropagate(tmp2);
          Expr stren = simplifyArithm(conjoin(tmp2, m_efac));
          mixedCands.insert(stren);
        }

        if (hr.srcVars.size() == 1)
        {
          if (!isFixedRel(rels[0])) {
            if (forceConv) forceConvergence(candidates[rels[0]], mixedCands);
            for (auto & m : mixedCands) getConj(m, candidates[rels[0]]);
          }
        }
        else
        {
          // decomposition here
          // fairness heuristic: prioritize candidates for all relations, which are true
          // TODO: find a way to disable it if for some reason some invariant should only be true
          vector<bool> trueCands;
          ExprSet trueRels;
          int numTrueCands = 0;
          for (int i = 0; i < rels.size(); i++)
          {
            trueCands.push_back(u.isTrue(curCnd[i]));
            if (trueCands.back())
            {
              trueRels.insert(rels[i]);
              numTrueCands++;
            }
          }

          // numTrueCands = 0;       // GF: hack to disable fairness

          ExprSet allGuessesInit;
          if (numTrueCands > 0)      // at least one curCnd should be true
            for (int i = 0; i < rels.size(); i++)
              if (!trueCands[i])
                allGuessesInit.insert(curCnd[i]);

          // actually, just a single candidate, in the most recent setting;
          // TODO: remove the loop (or find use of it)
          for (auto it = mixedCands.begin(); it != mixedCands.end(); )
          {
            if (containsOp<ARRAY_TY>(*it)) { ++it; continue; }
            Expr a = *it;
            ExprSet processed;
            ExprSet allGuesses = allGuessesInit;
            ExprVector histRec;

            auto candidatesTmp = candidates;

            for (int i = 0; i < rels.size(); i++)
            {
              // skip the relation if it already has a candidate and there exists a relation with no candidate
              // (existing candidates are already in allGuesses)
              if (numTrueCands > 0 && !trueCands[i]) continue;
              if (isFixedRel(rels[i])) continue;
              Expr r = rels[i];
	      
	      // Expr modelphi = conjoin(curCnd, m_efac);

	      // if (rels.size() == 1) {
	      // 	if (extend.find(r) != extend.end()) {
	      // 	  modelphi = mk<AND>(modelphi, replaceAll(extend[r], ruleManager.invVars[r], hr.srcVars[i]));
	      // 	}
	      // } else {
	      // 	for (int j = i+1; j < rels.size(); j++) {
	      // 	  if (extend.find(rels[j]) != extend.end()) {
	      // 	    modelphi = mk<AND>(modelphi, replaceAll(extend[rels[j]], ruleManager.invVars[rels[j]], hr.srcVars[j]));
	      // 	  }
	      // 	}
	      // }

              if (!u.isSat(a, conjoin(curCnd, m_efac))) return; // need to recheck because the solver has been reset
		
              if (processed.find(r) != processed.end()) continue;

              invVars.clear();
              ExprSet backGuesses, allVarsExcept;
              ExprVector vars;
              for (int j = 0; j < rels.size(); j++)
              {
                Expr t = rels[j];
                if (processed.find(t) != processed.end()) continue;
                if (t == r)
                {
                  vars.insert(vars.begin(), hr.srcVars[j].begin(), hr.srcVars[j].end());
                  if (occursNum[r].size() == 1) invVars = ruleManager.invVars[rels[j]];
                }
                else
                  allVarsExcept.insert(hr.srcVars[j].begin(), hr.srcVars[j].end());
              }

              // model-based cartesian decomposition
              ExprSet all = allGuesses;
              all.insert(mkNeg(a));

              if (trueRels.size() != 1)                  // again, for fairness heuristic:
                all.insert(u.getModel(allVarsExcept));

	      // outs() << "truerels.size: " << trueRels.size() << "\n";//DEBUG
	      // outs() << "model: " << *(u.getModel(allVarsExcept)) << "\n";//DEBUG
	      //DEBUG
	      // for (auto v : allVarsExcept)
	      // 	outs() << "allvarsexcept: " << *v << "\n";
	      // for (auto a : all)
		// outs() << "all: " << *a << "\n";//DEBUG
	      
              // in the case of nonlin, invVars is empty, so no renaming happens:

              preproGuessing(conjoin(all, m_efac), vars, invVars, backGuesses, true, false);

              if (occursNum[r].size() == 1)
              {
                getConj(conjoin(backGuesses, m_efac), candidates[r]);
                histRec.push_back(conjoin(backGuesses, m_efac));
                allGuesses.insert(backGuesses.begin(), backGuesses.end());
		//DEBUG
		// for (auto ag : allGuesses)
		//   outs() << "AG: " << *ag << "\n";
              }
              else
              {
                // nonlinear case; proceed to isomorphic decomposition for each candidate
                map<int, ExprVector> multiabdVars;

                for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                  for (auto & v : ruleManager.invVars[r])
                    multiabdVars[*it2].push_back(
                      cloneVar(v, mkTerm<string> (
                        "__multiabd_var" + lexical_cast<string>(*v) + "_" + to_string(*it2), m_efac)));

                Expr b = conjoin(backGuesses, m_efac);
                {
                  ExprSet sol;
                  int iter = 0;
                  while (++iter < 10 /*hardcode*/)
                  {
                    // preps for obtaining a new model

                    ExprSet cnj;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                    {
                      ExprSet dsj;
                      if (!sol.empty())
                        dsj.insert(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                      for (auto it3 = occursNum[r].begin(); it3 != occursNum[r].end(); ++it3)
                      {
                        ExprSet modelCnj;
                        for (int i = 0; i < ruleManager.invVars[r].size(); i++)
                          modelCnj.insert(mk<EQ>(hr.srcVars[*it2][i], multiabdVars[*it3][i]));
                        dsj.insert(conjoin(modelCnj, m_efac));
                      }
                      cnj.insert(disjoin(dsj, m_efac));
                    }

                    // obtaining a new model
                    ExprVector args;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      for (auto & v : hr.srcVars[*it2])
                        args.push_back(v->left());
                    args.push_back(mk<IMPL>(conjoin(cnj, m_efac), b));

                    ExprSet negModels;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      negModels.insert(mkNeg(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], multiabdVars[*it2])));

                    if (!u.isSat(extend.find(r) != extend.end() ?
                                 mk<AND>(extend[r], mknary<FORALL>(args)) :
                                 mknary<FORALL>(args), sol.empty() ?
                                 mk<TRUE>(m_efac) :
                                 disjoin(negModels, m_efac)))
                    {
                      candidates[r].insert(sol.begin(), sol.end());
                      histRec.push_back(conjoin(sol, m_efac));
                      for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                        allGuesses.insert(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                      break;
                    }
                    else
                    {
                      ExprSet models;
                      for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      {
                        ExprSet elements;
                        for (int i = 0; i < ruleManager.invVars[r].size(); i++)
                          elements.insert(mk<EQ>(ruleManager.invVars[r][i], u.getModel(multiabdVars[*it2][i])));
                        models.insert(conjoin(elements, m_efac));
                      }
                      sol.insert (disjoin(models, m_efac)); // weakening sol by a new model
                    }

                    // heuristic to accelerate convergence
                    ExprVector chk;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      chk.push_back(replaceAll(disjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                    sol.clear();
                    for (auto it1 = occursNum[r].begin(); it1 != occursNum[r].end(); ++it1)
                    {
                      int cnt = 0;
                      for (auto it3 = occursNum[r].begin(); it3 != it1; ++it3, ++cnt)
                        chk[cnt] = replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it3]);
                      chk[cnt] = mk<TRUE>(m_efac);

                      ExprSet allNonlin;
                      allNonlin.insert(mkNeg(b));
                      allNonlin.insert(conjoin(chk, m_efac));
                      preproGuessing(conjoin(allNonlin, m_efac), hr.srcVars[*it1], ruleManager.invVars[r], sol, true, false);
                    }
                    u.removeRedundantConjuncts(sol);
                  }
                }
              }
              processed.insert(r);
            }

            // fairness heuristic (need to be tested properly):
            {
              bool tryAgain = false;
              if (!abdHistory[&hr].empty() && equivVecs(abdHistory[&hr].back(), histRec))
              {
                candidates = candidatesTmp;

                for (int i = 0; i < histRec.size(); i++)
                {
                  if (u.isEquiv(curCnd[i], histRec[i]))
                  {
                    numTrueCands++;
                    trueCands[i] = true;
                    trueRels.insert(rels[i]);
                  }
                  else
                  {
                    trueCands[i] = false;
                    allGuessesInit.insert(curCnd[i]);
                  }
                }
                tryAgain = true; // to keep
              }

              abdHistory[&hr].push_back(histRec);

              if (tryAgain)
              {
                if (abdHistory[&hr].size() > 5 /*hardcoded bound*/)
                {
                  tryAgain = false;
                  for (int i = 0; i < 5 /*hardcoded bound*/; i++)
                    if (abdHistory[&hr][abdHistory[&hr].size() - 1 - i] != histRec)
                    {
                      tryAgain = true;
                      break;
                    }
                }
              }

              if (!tryAgain) ++it;
            }
//            outs () << "sanity check: " << u.implies(conjoin(allGuesses, m_efac), a) << "\n";
          }
        }
      }
    }

    // inductive strengthening of candidates (by abduction)
    void strengthen(int deep = 0)
    {
      if (deep >= strenBound) return;

      // currently, relies on the order in CHC file; TBD: proper backwards traversing
      for (auto hr = ruleManager.chcs.rbegin(); hr != ruleManager.chcs.rend(); hr++)
      {
        if (!hr->isFact)
        {
          filterUnsat();
          if (!checkCHC(*hr, candidates))
          {
	    // outs() << "in strengthen before\n";//DEBUG
	     // printCands(false);//DEBUG
            propagateCandidatesBackward(*hr, deep == strenBound - 1);
	    // outs() << "in strengthen after\n";//DEBUG
	    // printCands(false);//DEBUG
            strengthen(deep+1);
          }
        }
      }
    }

    void forceConvergence (ExprSet& prev, ExprSet& next)
    {
      if (prev.size() < 1 || next.size() < 1) return;
      ExprFactory& efac = (*next.begin())->getFactory();

      ExprSet prevSplit, nextSplit, prevSplitDisj, nextSplitDisj, common;

      for (auto & a : prev) getConj (a, prevSplit);
      for (auto & a : next) getConj (a, nextSplit);

      mergeDiseqs(prevSplit);
      mergeDiseqs(nextSplit);

      if (prevSplit.size() != 1 || nextSplit.size() != 1)
        return; // GF: to extend

      getDisj(*prevSplit.begin(), prevSplitDisj);
      getDisj(*nextSplit.begin(), nextSplitDisj);

      for (auto & a : prevSplitDisj)
        for (auto & b : nextSplitDisj)
          if (a == b) common.insert(a);

      if (common.empty()) return;
      next.clear();
      next.insert(disjoin(common, efac));
    }

    bool equivVecs (ExprVector e1, ExprVector e2)
    {
      if (e1.size() != e2.size()) return false;
      for (int i = 0; i < e1.size(); i++)
      {
        if (!u.isEquiv(e1[i], e2[i])) return false;
      }
      return true;
    }

    void getImplicationGuesses(map<Expr, ExprSet>& postconds)
    {
      map<Expr, ExprSet> preconds;
      for (auto & r : ruleManager.chcs)
      {
        if (r.isQuery) continue;

        int srcRelInd = -1;
        Expr rel = r.head->left();

        if (isFixedRel(rel)) continue;

        for (int i = 0; i < r.srcVars.size(); i++) if (r.srcRelations[i] == rel) srcRelInd = i;
        if (srcRelInd >= 0)
          preproGuessing(r.body, r.srcVars[srcRelInd], ruleManager.invVars[rel], preconds[rel]);

        if (srcRelInd == -1) continue;
        int tot = 0;
        for (auto guess : postconds[rel])
        {
          if (tot > 5) break; // empirically chosen bound
          if (isOpX<IMPL>(guess) || isOpX<OR>(guess)) continue; // hack

          for (auto & pre : preconds[rel])
          {
            if (u.implies(pre, guess)) continue;
            tot++;
            Expr newGuess = mk<IMPL>(pre, guess);
            ExprVector tmp;
            tmp.push_back(replaceAll(newGuess, ruleManager.invVars[rel], r.srcVars[srcRelInd]));
            tmp.push_back(r.body);
            // simple invariant check (for speed, need to be enhanced)
            if (u.implies (conjoin(tmp, m_efac), replaceAll(newGuess, ruleManager.invVars[rel], r.dstVars)))
            {
              candidates[rel].insert(newGuess);
              ExprSet newPost;
              tmp.push_back(mkNeg(replaceAll(pre, ruleManager.invVars[rel], r.dstVars)));
              preproGuessing(conjoin(tmp, m_efac), r.dstVars, ruleManager.invVars[rel], newPost);
              for (auto & a : newPost)
                candidates[rel].insert(mk<IMPL>(mk<NEG>(pre), a));
            }
          }
        }
      }
    }

    void printCands(bool unsat = true, map<Expr, ExprSet> partialsolns = map<Expr,ExprSet>(), bool nonmaximal = false, bool simplify = false)
    {
      printCands(unsat, partialsolns, nonmaximal, simplify, outs());
    }

    template <typename OutputStream>
    void printCands(bool unsat = true, map<Expr, ExprSet> partialsolns = map<Expr,ExprSet>(), bool nonmaximal = false, bool simplify = false, OutputStream & out = outs())
    {
      if (unsat)
      {
        out << "unsat";
        if (nonmaximal)
          out << " (may not be maximal solution) \n";
        else
          out << "\n";
      }

      for (auto & a : partialsolns.empty() ? candidates : partialsolns)
      {
        out << "(define-fun " << *a.first << " (";
        for (auto & b : ruleManager.invVars[a.first])
        {
          out << "(" << *b << " " << u.varType(b) << ")";
        }
        out << ") Bool\n  ";

        ExprSet lms = a.second;
        Expr sol = conjoin(lms, m_efac);

        // sanity checks:
        ExprSet allVars;
        filter (sol, bind::IsConst (), inserter (allVars, allVars.begin()));
        minusSets(allVars, ruleManager.invVars[a.first]);
        map<Expr, ExprVector> qv;
        getQVars (sol, qv);
        for (auto & q : qv) minusSets(allVars, q.second);
        assert (allVars.empty());
//        if (!u.isSat(sol)) assert(0);

        Expr res = simplifyBool(simplifyArithm(sol));
        if (simplify)
        {
          lms.clear();
          getConj(res, lms);
          shrinkCnjs(lms);
          u.removeRedundantConjuncts(lms);
          res = conjoin(lms, m_efac);
        }
        u.print(res, out);
        out << ")\n";
      }
    }

    bool dropUnsat(map<Expr, ExprSet>& annotations, const ExprVector & unsatCore, const map<Expr, pair<Expr, Expr>> & flagToCand)
    {
      for (auto & c : unsatCore) {
        auto entry = flagToCand.find(c);
        if (entry == flagToCand.end()) continue;
        Expr rel = (entry->second).first;
        Expr cand = (entry->second).second;
        annotations[rel].erase(cand);
        return true;
      }

      return false;
    }

    /* vacuity check based on SAT check */
    void vacCheck(map<Expr, ExprSet>& annotations)
    {
      bool recurse = false;

      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isFact) continue;

        ExprVector flags;
        ExprSet finalExpr;
        map<Expr, pair<Expr, Expr>> flagToCand;
        bool hasArray = false;

        for (int i = 0; i < hr.srcRelations.size(); i++) {
          Expr rel = hr.srcRelations[i];
          if (isFixedRel(rel)) {
            for (auto cand : annotations[rel]) {
              cand = replaceAll(cand, ruleManager.invVars[rel], hr.srcVars[i]);
              finalExpr.insert(cand);
            }
          } else {
            for (auto cand : annotations[rel]) {
              if (!hasArray && containsOp<FORALL>(cand)) hasArray = true;
              Expr flag = bind::boolConst(mkTerm<string>("__unsatcoreVar__" + to_string(flags.size()+1), m_efac));
              flags.push_back(flag);
              flagToCand[flag] = make_pair(rel, cand);
              cand = replaceAll(cand, ruleManager.invVars[rel], hr.srcVars[i]);
              finalExpr.insert(mk<IMPL>(flag, cand));
            }
          }
        }

        if (!hr.isQuery && u.isSat(hr.body)) {
          finalExpr.insert(hr.body);
        }

        // outs() << "BODY: " << *(hr.body) << "\n";
        // for (auto f : finalExpr)
        //   outs() << *f << "\n";

        if (!hasArray) {
          ExprVector unsatCore;
          if (!u.isSatAssuming(finalExpr, flags, std::back_inserter(unsatCore))) {
            // outs() << "failed hr: " << *(hr.body) << "\n";
            // outs() << "flags: " << flags.size() << "\n";
            // outs() << "unsatcore: " << unsatCore.size() << "\n";
            assert(dropUnsat(annotations, unsatCore, flagToCand));
            recurse = true;
          }
        } else {
          if (!u.isSat(finalExpr)) {
            ExprVector t1;
            ExprVector t2;
            u.splitUnsatSets(finalExpr, t1, t2);
            for (int i = 0; i < hr.srcRelations.size(); i++) {
              Expr rel = hr.srcRelations[i];
              
              for (auto itr =  annotations[rel].begin(); itr != annotations[rel].end();) {
                Expr c = replaceAll(*itr, hr.srcVars[i], ruleManager.invVars[rel]);
                if (find(t1.begin(), t1.end(), c) == t1.end()) {
                  itr = annotations[rel].erase(itr);
                } else {
                  ++itr;
                }
              }
            }
            recurse = true;
          }
        }

        if (recurse)
          return vacCheck(annotations);
      }
    }


    void filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (auto & a : candidates)
        if (!u.isSat(a.second)) {
          assert(!isFixedRel(a.first));
          for (auto & hr : ruleManager.chcs)
            if (hr.dstRelation == a.first && hr.isFact)
              worklist.push_back(&hr);
        }

      multiHoudini(worklist, false);

      for (auto & a : candidates)
      {
        if (!u.isSat(a.second))
        {
          ExprVector tmp;
          ExprVector stub; // TODO: try greedy search, maybe some lemmas are in stub?
          u.splitUnsatSets(a.second, tmp, stub);
          a.second.clear();
          a.second.insert(tmp.begin(), tmp.end());
        }
      }
      vacCheck(candidates);
    }

    Expr getQuantifiedCands(bool fwd, HornRuleExt& hr)
    {
      ExprSet qVars;
      Expr body = hr.body;
      if (fwd && hr.isFact)
      {
        getQuantifiedVars(hr.body, qVars);
        if (!qVars.empty())  // immediately try proving properties if already quantified
        {
          // make sure that we can use it as a property (i.e., variables check)

          ExprSet allVars;
          filter (hr.body, bind::IsConst (), inserter (allVars, allVars.begin()));
          minusSets(allVars, qVars);
          bool allGood = true;
          for (auto & v : allVars)
            if (find (hr.dstVars.begin(), hr.dstVars.end(), v) == hr.dstVars.end())
              { allGood = false; break; }
          if (allGood)
          {
            ExprSet tmpSet;
            getQuantifiedFormulas(hr.body, tmpSet);
            for (auto c : tmpSet)
            {
              // over-approximate the body such that it can pass through the seed mining etc..
              body = replaceAll(body, c, mk<TRUE>(m_efac));
              c = replaceAll(c, hr.dstVars, ruleManager.invVars[hr.dstRelation]);
              candidates[hr.dstRelation].insert(c);
            }
          }
        }
      }
      if (!fwd && hr.isQuery)  // similar for the query
      {
        getQuantifiedVars(hr.body, qVars);
        if (!qVars.empty())
        {
          ExprSet allVars;
          filter (hr.body, bind::IsConst (), inserter (allVars, allVars.begin()));
          minusSets(allVars, qVars);
          for (int i = 0; i < hr.srcVars.size(); i++)
          {
            bool toCont = false;
            for (auto & v : allVars)
              if (find (hr.srcVars[i].begin(), hr.srcVars[i].end(), v) == hr.srcVars[i].end())
                { toCont = true; break; }
            if (toCont) continue;
            getQuantifiedFormulas(mkNeg(hr.body), candidates[hr.srcRelations[i]]);
          }
          return NULL; // just as an indicator that everything went well
        }
      }
      return body;
    }

    bool isSkippable(Expr model, ExprVector vars, map<Expr, ExprSet>& cands)
    {
      if (model == NULL) return true;

      for (auto v: vars)
      {
        if (!containsOp<ARRAY_TY>(v)) continue;
        Expr tmp = u.getModel(v);
        if (tmp != v && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp))
        {
          return true;
        }
      }

      for (auto & a : cands)
        for (auto & b : a.second)
          if (containsOp<FORALL>(b)) return true;

      return false;
    }

    // adapted from RndLearnerV3
    bool multiHoudini(vector<HornRuleExt*>& worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) return false;
      auto candidatesTmp = candidates;
      bool res1 = true;
      for (auto & hr : worklist)
      {
        if (hr->isQuery) continue;
        if (isFixedRel(hr->dstRelation)) continue;

        if (!checkCHC(*hr, candidatesTmp))
        {
          bool res2 = true;
          Expr dstRel = hr->dstRelation;

          Expr model = u.getModel(hr->dstVars);
          if (isSkippable(model, hr->dstVars, candidatesTmp))
          {
            candidatesTmp[dstRel].clear();
            res2 = false;
          }
          else
          {
            for (auto it = candidatesTmp[dstRel].begin(); it != candidatesTmp[dstRel].end(); )
            {
              Expr repl = *it;
              repl = replaceAll(*it, ruleManager.invVars[dstRel], hr->dstVars);

              if (!u.isSat(model, repl)) { it = candidatesTmp[dstRel].erase(it); res2 = false; }
              else ++it;
            }
          }

          if (recur && !res2) res1 = false;
          if (!res1) break;
        }
      }
      candidates = candidatesTmp;
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    bool anyProgress(vector<HornRuleExt*>& worklist)
    {
      for (auto & a : candidates)
        for (auto & hr : worklist)
          if (find(hr->srcRelations.begin(), hr->srcRelations.end(), a.first) !=
              hr->srcRelations.end() || hr->dstRelation == a.first)
            if (!a.second.empty()) return true;
      return false;
    }

    // only one level of propagation here; to be extended
    void arrayGuessing(Expr tgt)
    {
      bool arrFound = false;
      for (auto & var : ruleManager.invVars[tgt])
        if (bind::isConst<ARRAY_TY> (var)) {
          arrFound = true;
          break;
        }
      if (!arrFound) return;

      int ind;
      bool iterGrows;
      Expr iterator;
      Expr qVar = bind::intConst(mkTerm<string> ("_FH_arr_it", m_efac));
      Expr range;
      HornRuleExt *hr = 0;
      HornRuleExt *qr = 0;

      // preprocessing
      for (auto & a : ruleManager.chcs)
      {
        if (a.isQuery && a.srcRelations[0] == tgt /*hack for now*/ &&
            (containsOp<SELECT>(a.body) || containsOp<STORE>(a.body)))
          qr = &a;
        if (a.isInductive && a.dstRelation == tgt &&
            (containsOp<SELECT>(a.body) || containsOp<STORE>(a.body)))
        {
          ExprVector counters;
          hr = &a;

          getCounters(a.body, counters);
          for (Expr c : counters)
          {
            ind = getVarIndex(c, a.srcVars[0] /*hack for now*/);
            if (ind < 0) continue;

            if (u.implies(a.body, mk<GT>(c, a.dstVars[ind])))
            {
              iterator = c;
              iterGrows = false;
              break;
            }
            else if (u.implies(a.body, mk<LT>(c, a.dstVars[ind])))
            {
              iterator = c;
              iterGrows = true;
            }
          }
        }
      }

      if (iterator == NULL) return;

      // range computation
      for (auto & a : ruleManager.chcs)
      {
        if (!a.isInductive && a.dstRelation == tgt)
        {
          int max_sz = INT_MAX;
          for (Expr e : candidates[tgt])
          {
            if ((iterGrows &&
               ((isOpX<GEQ>(e) && iterator == e->left()) ||
                (isOpX<LEQ>(e) && iterator == e->right()))) ||
               (!iterGrows &&
                 ((isOpX<GEQ>(e) && iterator == e->right()) ||
                  (isOpX<LEQ>(e) && iterator == e->left()))))
            {
              Expr bound = (e->left() == iterator) ? e->right() : e->left();
              if (treeSize(bound) < max_sz)
              {
                range = iterGrows ? mk<AND>(mk<LEQ>(bound, qVar), mk<LT>(qVar, iterator)) :
                                    mk<AND>(mk<LT>(iterator, qVar), mk<LEQ>(qVar, bound));
                max_sz = treeSize(bound);
              }
            }
          }
        }
      }

      if (range == NULL) return;

      // cell property guessing
      Expr body = hr->body;
      body = unfoldITE(body);
      body = rewriteSelectStore(body);
      ExprSet tmp;
      ExprVector qVars1, qVars2;
      for (int i = 0; i < hr->dstVars.size(); i++)
      {
        if (ruleManager.invVars[hr->srcRelations[0]][i] == iterator)
        {
          qVars1.push_back(hr->dstVars[i]);
          qVars2.push_back(iterator);
        }
        else
        {
          qVars1.push_back(ruleManager.invVars[hr->srcRelations[0]][i]);
          qVars2.push_back(hr->dstVars[i]);
        }
      }
      body = simpleQE(body, qVars1);

      preproGuessing(body, qVars2, ruleManager.invVars[hr->srcRelations[0]], tmp);

      for (auto s : tmp)
      {
        if (!containsOp<SELECT>(s)) continue;
        s = replaceAll(s, iterator, qVar);

        ExprVector args;
        args.push_back(qVar->left());
        args.push_back(mk<IMPL>(range, s));
        Expr newGuess = mknary<FORALL>(args);

        ExprSet chk;
        chk.insert(replaceAll(newGuess, ruleManager.invVars[tgt], hr->srcVars[0]));
        chk.insert(hr->body);
        chk.insert(candidates[tgt].begin(), candidates[tgt].end());
        // simple invariant check (for speed, need to be enhanced)
        if (u.implies (conjoin(chk, m_efac), replaceAll(newGuess, ruleManager.invVars[tgt], hr->dstVars)))
        {
          candidates[tgt].insert(newGuess);
          // try to propagate (only one level now; TODO: extend)
          for (auto & hr2 : ruleManager.chcs)
          {
            if (hr2.isQuery) continue;
            if (find(hr2.srcRelations.begin(), hr2.srcRelations.end(), tgt) != hr2.srcRelations.end() &&
                hr2.dstRelation != tgt)
            {
              ExprSet cnjs;
              getConj(hr2.body, cnjs);
              Expr newRange;
              for (auto c : cnjs)
              {
                if (emptyIntersect(c, iterator)) continue;
                if (isOpX<NEG>(c)) c = mkNeg(c->left());
                c = ineqSimplifier(iterator, c);
                if (!isOp<ComparissonOp>(c)) continue;

                if (isOpX<EQ>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, c->right());
                if (iterGrows && isOpX<GEQ>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, c->right());
                if (iterGrows && isOpX<GT>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, mk<PLUS>(c->right(), mkTerm (mpz_class (1), m_efac)));
                if (!iterGrows && isOpX<LEQ>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, c->right());
                if (!iterGrows && isOpX<LT>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, mk<MINUS>(c->right(), mkTerm (mpz_class (1), m_efac)));

                if (newRange != NULL) break;
              }

              if (newRange == NULL) continue;

              ExprVector args;
              args.push_back(qVar->left());
              args.push_back(mk<IMPL>(newRange, s));
              Expr newCand = getForallCnj(
                    simpleQE(
                        mk<AND>(hr2.body,mknary<FORALL>(args)), hr2.srcVars[0]));

              newCand = replaceAll(newCand, hr2.dstVars, ruleManager.invVars[hr2.dstRelation]);
              // finally, try the propagated guess:
              candidates[hr2.dstRelation].insert(newCand);
            }
          }
        }
      }

      if (qr == 0) return;

      tmp.clear();
      getArrIneqs(mkNeg(qr->body), tmp);

      for (auto s : tmp)
      {
        ExprSet allv;
        filter (s, bind::IsConst (), inserter (allv, allv.begin()));
        for (auto & a : allv)
          if (bind::typeOf(a) == bind::typeOf(qVar) && find(hr->srcVars[0].begin(), hr->srcVars[0].end(), a) ==
              hr->srcVars[0].end()) s = replaceAll(s, a, qVar);

        ExprVector args;
        args.push_back(qVar->left());
        args.push_back(mk<IMPL>(range, s));
        Expr newGuess = mknary<FORALL>(args);

        ExprSet chk;
        chk.insert(replaceAll(newGuess, ruleManager.invVars[tgt], qr->srcVars[0]));
        chk.insert(hr->body);
        chk.insert(candidates[tgt].begin(), candidates[tgt].end());
        // simple invariant check (for speed, need to be enhanced)
        if (u.implies (conjoin(chk, m_efac), replaceAll(newGuess, ruleManager.invVars[tgt], hr->dstVars)))
          candidates[tgt].insert(newGuess);
      }
    }

    Expr getForallCnj (Expr cands)
    {
      ExprSet cnj;
      getConj(cands, cnj);
      for (auto & cand : cnj)
        if (isOpX<FORALL>(cand)) return cand;
      return NULL;
    }

    bool equalCands(map<Expr, ExprSet>& cands)
    {
      for (auto & a : candidates)
      {
        if (a.second.size() != cands[a.first].size()) return false;
        if (!u.isEquiv(conjoin(a.second, m_efac), conjoin(cands[a.first], m_efac))) return false;
      }
      return true;
    }

    Result_t guessAndSolve()
    {
      vector<HornRuleExt*> worklist;
      for (auto & hr : ruleManager.chcs)
      {
        if (containsOp<ARRAY_TY>(hr.body)) hasArrays = true;
        worklist.push_back(&hr);
      }

      while (true)
      {
        auto candidatesTmp = candidates;
        for (bool fwd : { false, true })
        {
          if (debug)
          {
            outs () << "iter " << globalIter << "." << fwd << "\nCurrent candidates:\n";
            printCands(false);
          }
          declsVisited.clear();
          declsVisited.insert(ruleManager.failDecl);
          // outs() << "1st\n";//DEBUG
          // printCands(false);//DEBUG
          // outs() << "fwd: " << fwd << "\n";//DEBUG
          propagate(fwd);
          filterUnsat();
          // outs() << "2nd\n";//DEBUG
          // printCands(false);//DEBUG
          if (fwd) multiHoudini(worklist);  // i.e., weaken
          else strengthen();
          filterUnsat();
          // outs() << "3rd\n";//DEBUG
          // printCands(false);//DEBUG
          if (checkAllOver(true)) return Result_t::UNSAT;
        }
        if (equalCands(candidatesTmp)) break;
        if (hasArrays) break; // just one iteration is enough for arrays (for speed)
      }

      getImplicationGuesses(candidates);  // seems broken now; to revisit completely
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return Result_t::UNSAT;

      for (auto tgt : ruleManager.decls) arrayGuessing(tgt->left());
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return Result_t::UNSAT;

      return Result_t::UNKNOWN;
    }

    void sanitizeForDump(string & in)
    {
      in.erase(remove(in.begin(), in.end(), '_'), in.end());
      in.erase(remove(in.begin(), in.end(), '|'), in.end());

      map<char,char> substmap;
      // substmap['_'] = 'U';
      // substmap['|'] = 'B';
      substmap['\''] = 'P';
      substmap['$'] = 'D';
      substmap[':'] = 'C';
      substmap[';'] = 'c';

      for (size_t i = 0; i < in.size(); i++) {
        auto subst = substmap.find(in[i]);
        if (subst != substmap.end()) {
          in[i] = subst->second;
        }
      }
      // std::replace(in.begin(), in.end(), '\'', 'p');
      // std::replace(in.begin(), in.end(), '$', 'D');
      // std::replace(in.begin(), in.end(), ':', 'C');
    }

    void printAllVarsRels(const ExprSet & allVars, stringstream & decls, bool sygus = false, map<Expr, ExprVector> syvars = map<Expr, ExprVector>())
    {
      for (auto v : allVars) {
        decls << "(declare-var " << *v << " " << u.varType(v) << ")\n";
      }

      for (auto d : ruleManager.decls) {
        if (d == ruleManager.failDecl) continue;
        if (sygus) {
          decls << "(synth-fun " << *(d->left()) << " (";
          if (syvars.find(d->left()) != syvars.end()) {
            for (auto var : syvars[d->left()]) {
              decls << "( " << *var << " " << u.varType(var) << ")";
            }
          } else {
            for (auto itr = ruleManager.invVars[d->left()].begin(), end = ruleManager.invVars[d->left()].end(); itr != end; ++itr) {
              decls << "( " << *itr << " " << u.varType(*itr) << ")";
            }
          }
          decls << ") Bool)\n";
        } else {
          decls << "(declare-rel " << *bind::fname(d) << " (";
          for (unsigned i = 0; i < bind::domainSz(d); i++)
          {
            Expr ty = bind::domainTy(d, i);
            if (isOpX<BOOL_TY>(ty)) decls << "Bool ";
            else if (isOpX<REAL_TY>(ty)) decls << "Real ";
            else if (isOpX<INT_TY>(ty)) decls << "Int ";
            else decls << "UnSupportedSort";
          }
          decls << ")) \n";
        }
      }
    }

    string dumpToFile(stringstream & decls, stringstream & rules, string oldsmt = "", string postfix = "", bool sygus = false)
    {
      if (oldsmt.size() == 0) {
        oldsmt = ruleManager.infile;
      }

      string newsmt = oldsmt.substr(oldsmt.find_last_of("/"));
      newsmt = "/tmp/" + newsmt.substr(0, newsmt.find_last_of("."));
      newsmt += postfix + "_" + to_string(std::chrono::system_clock::now().time_since_epoch().count());
      newsmt += sygus ? ".sl" : ".smt2";

      string ds = decls.str();
      string rs = rules.str();

      sanitizeForDump(ds);
      sanitizeForDump(rs);

      ofstream newsmtFile(newsmt);      
      newsmtFile << ds << "\n" << rs << "\n";
      newsmtFile.close();

      return newsmt;
    }

    ExprVector getUnderConsRels(bool recurse = true)
    {
      ExprVector ucRels = getAllRels();

      for (auto uItr = ucRels.begin(); uItr != ucRels.end();) {
        bool found = false;
        for (auto & hr : ruleManager.chcs) {
          if (hr.isQuery) continue;
          if (hr.dstRelation == *uItr && hr.srcRelations.size() == 0) {
            found = true;
            break;
          }
        }
        if (found) {
          uItr = ucRels.erase(uItr);
        } else {
          ++uItr;
        }
      }

      for (auto uItr = ucRels.begin(); uItr != ucRels.end();) {
        bool update = false;
        for (auto & hr : ruleManager.chcs) {
          if (hr.isQuery) continue;
          if (hr.dstRelation != *uItr) continue;
          bool found;
          for (auto src : hr.srcRelations) {
            if (find(ucRels.begin(), ucRels.end(), src) != ucRels.end()) {
              found = true;
              break;
            }
          }
          if (!found) {
            update = true;
            break;
          }
        }
        if (update) {
          (void)ucRels.erase(uItr);
          uItr = ucRels.begin();
        } else {
          uItr++;
        }
      }

      return ucRels;
    }

    void getCurSoln(map<Expr, ExprSet> & soln, const ExprVector & rels, map<Expr, ExprVector> & invVars)
    {
      // outs() << "getcursoln: \n";
      for (auto r : rels) {
        soln[r].clear();
        for (auto e : candidates) {
          string saneName = lexical_cast<string>(*r);
          sanitizeForDump(saneName);
          if (saneName == lexical_cast<string>(*(e.first))) {
            // outs() << "rel: " << *r << "\n cands: " << *(conjoin(e.second, m_efac)) << "\n";
            for (auto c : e.second) {
              soln[r].insert(replaceAll(c, ruleManager.invVars[e.first], invVars[r]));
            }
          }
        }
      }
    }

    Result_t getWeakerSoln(const Expr & rel, const ExprVector & rels, const string & newsmt, map<Expr, ExprSet> & soln)
    {
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(newsmt);
      NonlinCHCsolver newNonlin(nrm, 1);
      ExprVector query;

      Result_t res = newNonlin.guessAndSolve();
      assert(res != Result_t::SAT);

      if (res == Result_t::UNSAT) {
        newNonlin.getCurSoln(soln, rels, ruleManager.invVars);
        return Result_t::SAT;
      }

      return Result_t::UNKNOWN;
    }

    void dumpSMT(const ExprVector & constraints, const ExprSet & allVars, const bool newenc = false)
    {
      stringstream asserts;
      stringstream decls;

      printAllVarsRels(allVars, decls);

      for (auto c : constraints) {
        asserts << "(assert ";
        u.print(c, asserts);
        asserts << ")\n";
      }

      asserts << "(check-sat)\n(get-model)\n";

      dumpToFile(decls, asserts, ruleManager.infile, newenc ? "_smt_V2_" : "_smt_");

    }

    Result_t checkMaximalSMT(ExprVector & weakenRels, ExprVector & fixedRels, map<Expr, Expr> & soln, ExprVector rels = ExprVector())
    {            
      map<Expr, ExprVector> newVars;
      map<Expr, ExprVector> newVarsp;
      map<Expr, Expr> newCand;
      map<Expr, Expr> newCandp;

      for (auto rel : rels) {
        string relName = lexical_cast<string>(*(rel));
        ExprVector tvars;
        ExprVector tvarsp;
        ExprVector eqVars;
        ExprVector eqVarsp;
        for (int i = 0; i < ruleManager.invVars[rel].size(); i++) {
          Expr var = ruleManager.invVars[rel][i];
          string name_suff = relName + "_" + to_string(i);
          Expr newVar = cloneVar(var, mkTerm<string>("_MAX_" + name_suff, m_efac));
          Expr newVarp = cloneVar(var, mkTerm<string>("_MAXP_" + name_suff, m_efac));
          tvars.push_back(newVar);
          tvarsp.push_back(newVarp);
          eqVars.push_back(mk<EQ>(var, newVar));
          eqVarsp.push_back(mk<EQ>(var, newVarp));
        }
        Expr curCand = conjoin(candidates[rel], m_efac);
        newCand.insert({rel, mk<OR>(curCand, conjoin(eqVars, m_efac))});
        newCandp.insert({rel, mk<OR>(curCand, conjoin(eqVarsp, m_efac))});
        newVars.insert({rel, tvars});
        newVarsp.insert({rel, tvarsp});
      }

      ExprVector constraints;

      //weaker solution constraint
      if (rels.size() > 0) {
        //at least one solution should be weaker
        ExprVector disj;
        for (auto rel : rels) {
          Expr cand = mk<NEG>(conjoin(candidates[rel], m_efac));
          cand = replaceAll(cand, ruleManager.invVars[rel], newVars[rel]);
          disj.push_back(cand);
        }
        constraints.push_back(disjoin(disj, m_efac));
      }

      map<Expr, ExprVector> funcs;
      ExprSet allVars;

      for (auto hr : ruleManager.chcs)
      {
        ExprSet antec;
        bool addVacuity = false;

        for (int i = 0; i < hr.srcRelations.size(); i++) {
          if (find(fixedRels.begin(), fixedRels.end(), hr.srcRelations[i]) != fixedRels.end()) {
            Expr curCand = conjoin(candidates[hr.srcRelations[i]], m_efac);
            antec.insert(replaceAll(curCand, ruleManager.invVars[hr.srcRelations[i]], hr.srcVars[i]));
          } else if (find(rels.begin(), rels.end(), hr.srcRelations[i]) == rels.end()) {
            for (auto d : ruleManager.decls) {
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.srcRelations[i]))) {
                Expr t = bind::fapp(d, hr.srcVars[i]);
                funcs.insert({t, hr.srcVars[i]});
                antec.insert(t);
                addVacuity = true;
                break;
              }
            }
          } else {
            Expr t = replaceAll(newCand[hr.srcRelations[i]], ruleManager.invVars[hr.srcRelations[i]], hr.srcVars[i]);
            antec.insert(t);
          }
        }

        Expr conseq;

        if (!hr.isQuery) {
          antec.insert(hr.body);
          if (find(fixedRels.begin(), fixedRels.end(), hr.dstRelation) != fixedRels.end()) {
            Expr curCand = conjoin(candidates[hr.dstRelation], m_efac);
            conseq = replaceAll(curCand, ruleManager.invVars[hr.dstRelation], hr.dstVars);
          } else if (find(rels.begin(), rels.end(), hr.dstRelation) == rels.end()) {
            for (auto d : ruleManager.decls) {
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
          Expr t = bind::fapp(d, hr.dstVars);
          conseq = t;
          // funcs.push_back(t);
          break;
              }
            }
          } else {
            conseq = replaceAll(newCand[hr.dstRelation], ruleManager.invVars[hr.dstRelation], hr.dstVars);
          }
        } else {
          conseq = mkNeg(hr.body);
        }

        ExprVector forallArgs;
        // ExprVector existsArgs;

        for (int i = 0; i < hr.srcRelations.size(); i++) {
          for (auto v : hr.srcVars[i]) {
            forallArgs.push_back(v->left());
            allVars.insert(v);
          }
          
          for (auto nv : newVars[hr.srcRelations[i]]) {
            // existsArgs.push_back(nv->left());
            allVars.insert(nv);
          }
        }

        for (auto v : hr.dstVars) {
          forallArgs.push_back(v->left());
          allVars.insert(v);
        }

        for (auto nv : newVarsp[hr.dstRelation]) {
          // existsArgs.push_back(nv->left());
          allVars.insert(nv);
        }

        for (auto lv : hr.locVars) {
          forallArgs.push_back(lv->left());
          allVars.insert(lv);
        }

        // existsArgs.push_back(mk<IMPL>(conjoin(antec, m_efac), conseq));
        // forallArgs.push_back(mknary<EXISTS>(existsArgs));

        forallArgs.push_back(mk<IMPL>(conjoin(antec, m_efac), conseq));

        constraints.push_back(mknary<FORALL>(forallArgs));

        if (addVacuity) {
          forallArgs.pop_back();
          forallArgs.push_back(conjoin(antec, m_efac));
          constraints.push_back(mknary<EXISTS>(forallArgs));
        }
      }

      //DEBUG
      dumpSMT(constraints, allVars);
      boost::tribool res = u.isSat(constraints);

      if (boost::logic::indeterminate(res)) {
        //	outs() << "result is indeterminate \n";//DEBUG
        return Result_t::UNKNOWN;

      } else if (!res) {
        //	outs() << "result is us!\n";//DEBUG
        return Result_t::UNSAT;
      } 

      //debug
      // u.printModel();
      // for (auto func : funcs) {
      // 	Expr fm = u.getModel(func.first);
      // 	outs() << *(func.first) << " -> " << *fm << "\n";
      // }

      for (auto rel : rels) {
        Expr model = u.getModel(newVars[rel]);
        // outs() << "model: " << *model << "\n";//DEBUG
        Expr weakerSoln = mk<OR>(conjoin(candidates[rel],m_efac), replaceAll(model, newVars[rel], ruleManager.invVars[rel]));
        soln.insert({rel, weakerSoln});
        // outs() << "weakersoln: " << *weakerSoln << "\n";//DEBUG
      }	

      for (auto d : ruleManager.decls) {
        if (find(rels.begin(), rels.end(), d->left()) != rels.end()) continue;
        for (auto func : funcs) {
          if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*((func.first)->left()->left()))) {
            soln.insert({d->left(), replaceAll(u.getModel(func.first), func.second, ruleManager.invVars[d->left()])});
            break;
          }
        }
      }

      // //debug
      // for (auto se : soln) {
      // 	outs() << *(se.first) << "->\n";
      // 	outs() << *(se.second) << "\n";
      // }
      // for (auto ce : candidates) {
      // 	outs() << *(ce.first) << "->\n";
      // 	for (auto c : ce.second)
      // 	  outs() << *c << "\n";
      // }

      if (rels.size() > 0) {
        for (auto d : ruleManager.decls) {
          Expr rel = d->left();
          if (find(fixedRels.begin(), fixedRels.end(), rel) != fixedRels.end()) continue;
          if (u.isSat(soln[rel], mk<NEG>(conjoin(candidates[rel], m_efac)))) {
            weakenRels.push_back(rel);
          } else {
            fixedRels.push_back(rel);
          }
        }
      }

      return Result_t::SAT;

    }

    ExprVector getAllRels()
    {
      ExprVector retRels;

      for (auto d : ruleManager.decls) {
        retRels.push_back(d->left());
      }

      return retRels;
    }

    // Adds two new rules in addition to the rules present in 'oldsmt': 
    // 1) candidate[rel](invVars[rel]) => rel(invVars[rel])
    // 2) ~candidate[rel](invVars[rel]) /\ tmprel(invVars[rel]) => rel(invVars[rel])
    // returns the name of the file where new rules are present 
    string constructWeakeningRules(const ExprVector & weakenRels, const ExprVector & fixedRels)
    {
      stringstream newRules;
      stringstream newDecls;
      ExprSet allVars;
      string queryRelStr = isOpX<FALSE>(ruleManager.failDecl) ? "fail" : lexical_cast<string>(ruleManager.failDecl);

      for (auto inve : ruleManager.invVars) {
        allVars.insert(inve.second.begin(), inve.second.end());
      }

      for (auto rel : weakenRels) {

        const string tmpRelName = "tmprel" + lexical_cast<string>(*rel);

        newDecls << "(declare-rel " << tmpRelName << " (";
        for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
          newDecls << " " << u.varType(*itr);
        }
        newDecls << "))\n";

        //candidate[rel] => rel
        newRules << "(rule (=> ";
        Expr e = simplifyBool(conjoin(candidates[rel], m_efac)); //done to avoid single disjunct, which is causing crash later
        u.print(e, newRules);
        newRules << "( " << *rel;
        for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
          if (itr != ruleManager.invVars[rel].begin())
            newRules << " ";
          newRules << " " << *itr;
        }
        newRules << ")))\n";

        //~candidate[rel] /\ tmprel => rel
        newRules << "(rule (=> (and ";
        u.print(mk<NEG>(conjoin(candidates[rel], m_efac)), newRules);
        newRules << "( " << tmpRelName;
        for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
          if (itr != ruleManager.invVars[rel].begin())
            newRules << " ";
          newRules << " " << *itr;
        }
        newRules << ")) ( " << *rel;
        for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
          if (itr != ruleManager.invVars[rel].begin())
            newRules << " ";
          newRules << " " << *itr;
        }
        newRules << ")))\n";
      }


      for (auto & hr : ruleManager.chcs)
      {
        for (int i = 0; i < hr.srcVars.size(); i++) {
          allVars.insert(hr.srcVars[i].begin(), hr.srcVars[i].end());
        }
        allVars.insert(hr.locVars.begin(), hr.locVars.end());
        allVars.insert(hr.dstVars.begin(), hr.dstVars.end());

        ExprSet antec;
        for (int i = 0; i < hr.srcRelations.size(); i++) {
          Expr src = hr.srcRelations[i];
          if (find(fixedRels.begin(), fixedRels.end(), src) != fixedRels.end()) {
            Expr t = replaceAll(conjoin(candidates[src], m_efac), ruleManager.invVars[src], hr.srcVars[i]);
            antec.insert(t);

          } else {
            for (auto d : ruleManager.decls)
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src)) {
          Expr t = bind::fapp(d, hr.srcVars[i]);
          antec.insert(t);
          break;
              }
          }
        }

        antec.insert(hr.body);
        Expr conseq;
        bool addFail = false;

        if (find(fixedRels.begin(), fixedRels.end(), hr.dstRelation) != fixedRels.end()) {
          antec.insert(mk<NEG>(replaceAll(conjoin(candidates[hr.dstRelation], m_efac), ruleManager.invVars[hr.dstRelation], hr.dstVars)));
          addFail = true;
        } else {
          if (hr.isQuery) {
            addFail = true;
          } else {
            for (auto d : ruleManager.decls)
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
          conseq = bind::fapp(d, hr.dstVars);
          break;
              }
          }
        }

        if (addFail) {
          newRules << "(rule (=> ";
          u.print(conjoin(antec, m_efac), newRules);
          newRules << " " << queryRelStr << "))\n";
        } else {
          newRules << "(rule ";
          u.print(mk<IMPL>(conjoin(antec, m_efac), conseq), newRules);
          newRules << ")\n";
        }
        //debug
        // outs() << newRules.str();
      }
      printAllVarsRels(allVars, newDecls);
      newDecls << "(declare-rel " << queryRelStr << "())\n";
      newRules << "(query " << queryRelStr << ")\n";
      return dumpToFile(newDecls, newRules, ruleManager.infile);
    }

    Result_t solveWeakCHC(const string & newsmt, map<Expr, ExprSet> & soln)
    {
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(newsmt);
      NonlinCHCsolver newNonlin(nrm, 1);
      ExprVector query;

      Result_t res = newNonlin.guessAndSolve();
      assert(res != Result_t::SAT);

      if (res == Result_t::UNSAT) {
        ExprVector allRels = getAllRels();
        newNonlin.getCurSoln(soln, allRels, ruleManager.invVars);
        return Result_t::SAT;
      }

      return Result_t::UNKNOWN;
    }

    // chc solver based weaker solution synthesis
    Result_t weakenUsingCHC(const ExprVector & weakenRels, const ExprVector & fixedRels)
    {
      string newsmt;
      newsmt = constructWeakeningRules(weakenRels, fixedRels);
      map<Expr, ExprSet> soln;
      Result_t res = solveWeakCHC(newsmt, soln);
      if (res == Result_t::SAT) {
        // outs() << "CHC proved s\n";
        for (auto e : soln) {
          if (find (fixedRels.begin(), fixedRels.end(), e.first) == fixedRels.end()) {
              candidates[e.first].clear();
              candidates[e.first].insert(e.second.begin(), e.second.end());
          }
        }
      }
      return res;
    }

    // TODO: move the entire SyGuS-translation to some helper class
    string constructWeakeningSygus(const ExprVector & weakenRels, const ExprVector & fixedRels, map<Expr, ExprVector> & syvars, bool firstTime = false)
    {
      stringstream newRules;
      stringstream newDecls;
      ExprSet allVars;
      string queryRelStr = "false";

      for (auto inve : ruleManager.invVars) {
        allVars.insert(inve.second.begin(), inve.second.end());
      }

      newDecls << "(set-logic LIA)\n";

      if (!firstTime) {
        for (auto rel : weakenRels) {
          const string tmpRelName = "tmprel" + lexical_cast<string>(*rel);

          newDecls << "(synth-fun " << tmpRelName << " (";
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            newDecls << "( " << *itr << " " << u.varType(*itr) << ")";
          }
          newDecls << ") Bool)\n";

          //candidate[rel] => rel
          newRules << "(constraint (=> ";
          Expr e = simplifyBool(conjoin(candidates[rel], m_efac)); //done to avoid single disjunct, which is causing crash later
          u.print(e, newRules);
          newRules << "( " << *rel;
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            if (itr != ruleManager.invVars[rel].begin())
              newRules << "  ";
            newRules << " " << *itr;
          }
          newRules << ")))\n";

          //~candidate[rel] /\ tmprel => rel
          newRules << "(constraint (=> (and ";
          u.print(mk<NEG>(conjoin(candidates[rel], m_efac)), newRules);
          newRules << "( " << tmpRelName;
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            if (itr != ruleManager.invVars[rel].begin())
              newRules << " ";
            newRules << " " << *itr;
          }
          newRules << ")) ( " << *rel;
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            if (itr != ruleManager.invVars[rel].begin())
              newRules << " ";
            newRules << " " << *itr;
          }
          newRules << ")))\n";

          //vacuity
          newRules << "(constraint (exists ( ";
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            newRules << "( " << *itr << " " << u.varType(*itr) << ")";
          }
          newRules << ") (and";
          u.print(mk<NEG>(conjoin(candidates[rel], m_efac)), newRules);
          newRules << "( " << tmpRelName;
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            if (itr != ruleManager.invVars[rel].begin())
              newRules << " ";
            newRules << " " << *itr;
          }
          newRules << "))))\n";
        }
      }

      for (auto rel : weakenRels) {
        //these variables will be used later to get solution from sygus solver
        ExprVector newvars;
        for (int i = 0; i < ruleManager.invVars[rel].size(); i++) {
          Expr var = ruleManager.invVars[rel][i];
          Expr newVar;
          string varname =  "sygus" + lexical_cast<string>(*rel) + to_string(i);
          sanitizeForDump(varname);
          if (bind::isIntConst(var)) {
            newVar = bind::intConst(mkTerm<string>(varname, m_efac));
          } else if (bind::isRealConst(var)) {
            newVar = bind::realConst(mkTerm<string>(varname, m_efac));
          } else if (bind::isBoolConst(var)) {
            newVar = bind::intConst(mkTerm<string>(varname, m_efac));
          } else {
            outs() << "Unsupport vartype: " << u.varType(var) << "\n";
            assert(0);
          }
          newvars.push_back(newVar);
        }
        syvars.insert({rel, newvars});
      }

      for (auto & hr : ruleManager.chcs)
      {
        for (int i = 0; i < hr.srcVars.size(); i++) {
          allVars.insert(hr.srcVars[i].begin(), hr.srcVars[i].end());
        }
        allVars.insert(hr.locVars.begin(), hr.locVars.end());
        allVars.insert(hr.dstVars.begin(), hr.dstVars.end());

        ExprSet antec;
        for (int i = 0; i < hr.srcRelations.size(); i++) {
          Expr src = hr.srcRelations[i];
          if (find(fixedRels.begin(), fixedRels.end(), src) != fixedRels.end()) {
            Expr t = replaceAll(conjoin(candidates[src], m_efac), ruleManager.invVars[src], hr.srcVars[i]);
            antec.insert(t);
          } else {
            for (auto d : ruleManager.decls)
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src)) {
          Expr t = bind::fapp(d, hr.srcVars[i]);
          antec.insert(t);
          break;
	      }
      }
    }

    //vacuity
    if (!hr.isQuery) {
      antec.insert(hr.body);
    }

    if (hr.srcRelations.size() != 0) {
      newRules << "(constraint (exists ( ";
      for (int i = 0; i < hr.srcVars.size(); i++) {
        for (auto sv : hr.srcVars[i])
          newRules << "( " << *sv << " " << u.varType(sv) << ")";
      }
      for (int i = 0; i < hr.dstVars.size(); i++) {
        newRules << "( " << *(hr.dstVars[i]) << " " << u.varType(hr.dstVars[i]) << ")";
      }
      for (int i = 0; i < hr.locVars.size(); i++) {
        newRules << "( " << *(hr.locVars[i]) << " " << u.varType(hr.locVars[i]) << ")";
      }
      newRules << ")";
      u.print(conjoin(antec, m_efac),  newRules);
      newRules << "))\n";
    }

    Expr conseq;
    bool addFail = false;

    if (find(fixedRels.begin(), fixedRels.end(), hr.dstRelation) != fixedRels.end()) {
      antec.insert(mk<NEG>(replaceAll(conjoin(candidates[hr.dstRelation], m_efac), ruleManager.invVars[hr.dstRelation], hr.dstVars)));
      addFail = true;
    } else {
      if (hr.isQuery) {
        antec.insert(hr.body);
        addFail = true;
      } else {
        for (auto d : ruleManager.decls)
          if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
            conseq = bind::fapp(d, hr.dstVars);
            break;
          }
        }
      }

      if (addFail) {
        newRules << "(constraint (=> ";
        u.print(conjoin(antec, m_efac), newRules);
        newRules << " " << queryRelStr << "))\n";
      } else {
        newRules << "(constraint ";
        u.print(mk<IMPL>(conjoin(antec, m_efac), conseq), newRules);
        newRules << ")\n";
      }
      //debug
      // outs() << newRules.str();
      }
      printAllVarsRels(allVars, newDecls, true, syvars);
      // newDecls << "(declare-rel " << queryRelStr << "())\n";
      // newRules << "(query " << queryRelStr << ")\n";
      newRules << "(check-synth)\n";
      return dumpToFile(newDecls, newRules, ruleManager.infile, "_sygus_", true);
    }

    Result_t solveWeakSygus(map<Expr, ExprVector> & syvars, const ExprVector & weakenRels, const string & slfile, map<Expr, Expr> & soln)
    {
      // const string SYGUS_BIN = "/home/u1392220/tmp/max_synth/ws/modver/build/run_sygus.sh";
      const string output = slfile.substr(0, slfile.find_last_of(".")) + ".out";
//      outs() << "starting sygus on file " << slfile << "\n";
      string cmd = SYGUS_BIN + " " + slfile + " >" + output;
      outs() << "all " << cmd << "\n";
      int sysret = system(cmd.c_str());
      if (sysret == -1 || WEXITSTATUS(sysret) != 0) {
        return Result_t::UNKNOWN;
      }

      EZ3 z3(m_efac);

      ifstream tmpinfile(output.c_str());
      if (!tmpinfile) {
        return Result_t::UNKNOWN;
      }
      stringstream tmpinstream;
      tmpinstream << tmpinfile.rdbuf();
      tmpinfile.close();
      string defs(tmpinstream.str());

      for (auto rel : weakenRels)
      {
        stringstream smtstream;
        smtstream << defs;
        for (auto sv : syvars[rel]) {
          smtstream << "(declare-fun " << *sv << " () " << u.varType(sv) << ")\n";
        }

        string sanerelname = lexical_cast<string>(*rel);
        sanitizeForDump(sanerelname);
        smtstream <<  "(assert( " + sanerelname;
        for (int i = 0; i < syvars[rel].size(); i++) {
          smtstream << " " + lexical_cast<string>(*(syvars[rel][i]));
        }
        smtstream << "))\n";
        smtstream << "(check-sat)\n";
        // outs() << smtstream.str();

        try {
          Expr funcAsserts = z3_from_smtlib(z3, smtstream.str());
          soln.insert({rel, replaceAll(funcAsserts, syvars[rel], ruleManager.invVars[rel])});
          
        } catch (z3::exception &e){
          char str[3000];
          strncpy(str, e.msg(), 300);
          outs() << "z3 exception: " << str << " while reading : " << smtstream.str() <<"\n";
          return Result_t::UNKNOWN;
        }
      }

      //debug
      // outs() << "soln from sygus: \n";
      // for (auto se : soln) {
      // 	outs() << *(se.first) << " -> " << *(se.second) << "\n";
      // }

      return Result_t::SAT;
    }

    Result_t weakenUsingSygus(const ExprVector & weakenRels, const ExprVector & fixedRels, const bool & firstTime = false)
    {
      map<Expr, ExprVector> syvars;
      string newsl = constructWeakeningSygus(weakenRels, fixedRels, syvars, firstTime);
      map<Expr, Expr> soln;

      Result_t res = solveWeakSygus(syvars, weakenRels, newsl, soln);

      if (res == Result_t::SAT) {
      	// outs() << "sygus proved s\n";
      	for (auto e : soln) {
      	  if (find (fixedRels.begin(), fixedRels.end(), e.first) == fixedRels.end()) {	    
      	      candidates[e.first].clear();
      	      candidates[e.first].insert(e.second);
      	  }
      	}	
      }

      //flip the result as caller expects unsat first time; argh!
      if (firstTime) {
        if (res == Result_t::UNSAT) {
          res = Result_t::SAT;
        } else if (res == Result_t::SAT) {
          res = Result_t::UNSAT;
        }
      }

      return res;
    }

    ExprVector vecDiff(ExprVector vec1, ExprVector vec2) {
      ExprVector diff;
      for (auto v1 : vec1) {
        if (find (vec2.begin(), vec2.end(), v1) == vec2.end()) {
          diff.push_back(v1);
        }
      }
      return diff;
    }

    void maximalSolve (bool useGAS = true, bool usesygus = false, bool useUC = false, bool fixCRels = false)
    {
      int itr = 0;
      bool firstSMTCall = !useGAS;
      ExprVector allRels = getAllRels();
      ExprVector rels = useUC ? getUnderConsRels() : allRels;

      if (useGAS) {
        Result_t res;
        if (!usesygus) {
          res = guessAndSolve();
        }  else {
          ExprVector tmpfrels;
          res = weakenUsingSygus(allRels, tmpfrels, true);
        }

        itr++;
        if (hasArrays) {
          switch (res) {
            case Result_t::UNSAT: printCands(); break;
            case Result_t::UNKNOWN: outs() << "unknown\n"; break;
            case Result_t::SAT: outs() << "sat\n"; break;
          }
          return;
        }

        if (res == Result_t::UNSAT && rels.size() == 0) {
          outs() << "Total iterations: "  << itr << "\n";
          //debug
          for (auto hr : ruleManager.chcs) {
            if (!checkCHC(hr, candidates)) {
              outs() << "something is wrong!(after GAS)\n";
              assert(0);
            }
          }
          printCands(true, candidates);
          return;
        }

        if (res == Result_t::SAT) {
          outs() << "sat\n";
          return;
        }

        if (res == Result_t::UNKNOWN){
          // outs() << "unknown\n";
          // return;
          // outs() << "GAS is uk\n";
          firstSMTCall = true;
        }
      }

      //debug
      // if (!firstSMTCall)
      // 	outs() << "GAS first iteration done\n";
      // for (auto e : candidates) {
      // 	outs() << "rel: " << *(e.first) << "\n";
      // 	for (auto c : e.second) {
      // 	  outs() << *(c) << "\n";
      // 	}
      // }
      // outs() << "rels: \n";
      // for (auto r : rels) {
      // 	outs() << *r << "\n";
      // }

      while (true) {

        Result_t maxRes;
        ExprVector weakenRels;
        ExprVector fixedRels = !firstSMTCall && fixCRels ? vecDiff(allRels, rels) : ExprVector() ;
        map<Expr, Expr> smtSoln;

      //  outs() << "current iteration: "<< itr << "\n";

        maxRes = firstSMTCall ? checkMaximalSMT(weakenRels, fixedRels, smtSoln) : checkMaximalSMT(weakenRels, fixedRels, smtSoln, rels);
        itr++;

        if (maxRes == Result_t::UNSAT) {
      //    outs() << "Total iterations: "  << itr << "\n";

          //debug
          for (auto hr : ruleManager.chcs) {
            if (!checkCHC(hr, candidates)) {
              outs() << "something is wrong!(after SMT us)\n";
              assert(0);
            }
          }
          printCands(true, candidates);
          return;

        } else if (maxRes == Result_t::UNKNOWN){
          if (firstSMTCall) {
            outs() << "unknown\n";
          } else {
            //debug
            for (auto hr : ruleManager.chcs) {
              if (!checkCHC(hr, candidates)) {
                outs() << "something is wrong(after SMT uk)!\n";
                assert(0);
              }
            }
            printCands(true, candidates, true);
          }
          return;
        }

        if (firstSMTCall || !useGAS) {
          firstSMTCall  = false;
          for (auto ce : smtSoln) {
            candidates[ce.first].clear();
            candidates[ce.first].insert(ce.second);
          }
          continue;
        }

        Result_t chcres = usesygus ? weakenUsingSygus(weakenRels, fixedRels) : weakenUsingCHC(weakenRels, fixedRels);

        if (chcres == Result_t::UNKNOWN) {
          for (auto ce : smtSoln) {
            // if (find(fixedRels.begin(), fixedRels.end(), ce.first) == fixedRels.end()) {
            candidates[ce.first].clear();
            candidates[ce.first].insert(ce.second);
            // }
          }
        }

        //debug
        // outs() << "SOLN:\n";
        // for (auto ce : candidates) {
        //   outs() << *(ce.first) << "->\n";
        //   for (auto c : ce.second) {
        //     outs() << *c <<"\n";
        //   }
        // }
        for (auto hr : ruleManager.chcs) {
          if (!checkCHC(hr, candidates)) {
            outs() << "something is wrong (after CHC)!\n";
            assert(0);
          }
        }
      }
    }

    void nonmaximalSolve(bool useGAS, bool usesygus)
    {
      Result_t res;
      if (usesygus) {
        ExprVector tmpfrels;
        ExprVector allrels = getAllRels();
        res = weakenUsingSygus(allrels, tmpfrels, true);
      } else if (useGAS) {
        res = guessAndSolve();
      } else {
        ExprVector weakenRels;
        ExprVector fixedRels;
        map<Expr, Expr> smtSoln;
        res = checkMaximalSMT(weakenRels, fixedRels, smtSoln);
        if (res == Result_t::SAT) {
          for (auto ce : smtSoln) {
            candidates[ce.first].clear();
            candidates[ce.first].insert(ce.second);
          }
          res = Result_t::UNSAT;
        } else {
          res = Result_t::UNKNOWN;
        }
      }

      switch(res) {
        case Result_t::UNSAT: printCands(); break;
        case Result_t::SAT: outs() << "sat!\n"; break;
        case Result_t::UNKNOWN: outs() << "unknown\n"; break;
      }
    }

    // naive solving, without invariant generation
    Result_t solveIncrementally(int bound, int unr, ExprVector& rels, vector<ExprVector>& args)
    {
      if (unr > bound)       // maximum bound reached
      {
        return Result_t::UNKNOWN;
      }
      else if (rels.empty()) // base case == init is reachable
      {
        return Result_t::SAT;
      }

      Result_t res = Result_t::UNSAT;

      // reserve copy;
      auto ssaStepsTmp = ssaSteps;
      int varCntTmp = varCnt;

      vector<vector<int>> applicableRules;
      for (int i = 0; i < rels.size(); i++)
      {
        vector<int> applicable;
        for (auto & r : ruleManager.incms[rels[i]])
        {
          Expr body = ruleManager.chcs[r].body; //ruleManager.getPostcondition(r);
          if (args.size() != 0)
            body = replaceAll(body, ruleManager.chcs[r].dstVars, args[i]);
          // identifying applicable rules
          if (u.isSat(body, conjoin(ssaSteps, m_efac)))
          {
            applicable.push_back(r);
          }
        }
        if (applicable.empty())
        {
          return Result_t::UNSAT;         // nothing is reachable; thus it is safe here
        }
        applicableRules.push_back(applicable);
      }

      vector<vector<int>> ruleCombinations;
      getCombinations(applicableRules, ruleCombinations);

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
            for (auto & a : hr.locVars)
            {
              Expr new_name = mkTerm<string> ("_fh_" + to_string(varCnt++), m_efac);
              body = replaceAll(body, a, cloneVar(a, new_name));
            }
          }

          ssaSteps.push_back(body);
        }

        if (u.isSat(conjoin(ssaSteps, m_efac))) // TODO: optimize with incremental SMT solving (i.e., using push / pop)
        {
          Result_t res_tmp = solveIncrementally(bound, unr + 1, rels2, args2);
          if (res_tmp == Result_t::SAT) return Result_t::SAT;           // bug is found for some combination
          else if (res_tmp == Result_t::UNKNOWN) res = Result_t::UNKNOWN;
        }
      }
      return res;
    }

    // naive solving, without invariant generation
    void solveIncrementally(int bound)
    {
      ExprVector query;
      query.push_back(ruleManager.failDecl);
      vector<ExprVector> empt;
      switch (solveIncrementally (bound, 0, query, empt))
      {
      case Result_t::SAT: outs () << "sat\n"; break;
      case Result_t::UNSAT: outs () << "unsat\n"; break;
      case Result_t::UNKNOWN: outs () << "unknown\n"; break;
      }
    }

    void setSygusPath(string sp)
    {
      SYGUS_BIN=sp;
    }
  };

  inline void solveNonlin(string smt, int inv, int stren, bool maximal, const vector<string> & relsOrder, bool useGAS, bool usesygus, bool useUC, bool newenc, bool fixCRels, string syguspath)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    NonlinCHCsolver nonlin(ruleManager, stren);

    if (usesygus) {
      nonlin.setSygusPath(syguspath);
    }

    if (inv == 0) {
      if (maximal) {
        nonlin.maximalSolve(useGAS, usesygus, useUC, fixCRels);
      } else {
        nonlin.nonmaximalSolve(useGAS, usesygus);
      }
    } else {
      nonlin.solveIncrementally(inv);
    }
  };
}

#endif
