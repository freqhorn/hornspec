#ifndef NONLINCHCSOLVER__HPP__
#define NONLINCHCSOLVER__HPP__

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
    map<Expr, ExprSet> candidates;
    bool hasArrays = false;
    ExprSet declsVisited;
    map<HornRuleExt*, vector<ExprVector>> abdHistory;

    public:

    NonlinCHCsolver (CHCs& r) : m_efac(r.m_efac), ruleManager(r), u(m_efac) {}

    Expr quantifierElimination(Expr& cond, ExprSet& vars)
    {
      if (vars.size() == 0) return simplifyBool(cond);

      if (containsOp<FORALL>(cond) || containsOp<EXISTS>(cond))
        return mk<TRUE>(m_efac);

      Expr newCond;
      if (isNonlinear(cond)) {
        newCond = simpleQE(cond, vars);
        if (!u.implies(cond, newCond)) {
          return mk<TRUE>(m_efac);
        }
      } else {
        AeValSolver ae(mk<TRUE>(m_efac), cond, vars); // exists quantified . formula
        if (ae.solve()) {
          newCond = ae.getValidSubset();
        } else {
          return mk<TRUE>(m_efac);
        }
      }
      if (!emptyIntersect(newCond, vars)) // sanity check
      {
        return mk<TRUE>(m_efac);
      }
      return simplifyBool(newCond);
    }

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
      ExprSet ev3;
      filter (e, bind::IsConst (), inserter (ev3, ev3.begin())); // prepare vars
      for (auto it = ev3.begin(); it != ev3.end(); )
      {
        if (find(ev1.begin(), ev1.end(), *it) == ev1.end()) ++it;
        else it = ev3.erase(it);
      }

      e = quantifierElimination(e, ev3);
      if (backward) e = mkNeg(e);
      e = simplifyBool(simplifyArithm(e, false, true));

//      ExprSet cnjs;
//      getConj(e, cnjs);
//      shrinkCnjs(cnjs);
//      e = conjoin(cnjs, m_efac);
//      e = simplifyBool(e);

      if (!ev2.empty())
        e = replaceAll(e, ev1, ev2); // rename variables only if ev2 is nonempty
      if (mutate)
        mutateHeuristic(e, guesses);
      else
        getConj(e, guesses);
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
      int szInit = declsVisited.size();
      for (auto & hr : ruleManager.chcs)
      {
        bool dstVisited = declsVisited.find(hr.dstRelation) != declsVisited.end();
        bool srcVisited = hr.isFact || (hr.isInductive && hasNoDef(hr.dstRelation));
        for (auto & a : hr.srcRelations)
          srcVisited |= declsVisited.find(a) != declsVisited.end();

        if (fwd && srcVisited && !dstVisited)
        {
          propagateCandidatesForward(hr);
          declsVisited.insert(hr.dstRelation);
        }
        else if (!fwd && !hr.isInductive && !srcVisited && dstVisited)
        {
          propagateCandidatesBackward(hr);
          declsVisited.insert(hr.srcRelations.begin(), hr.srcRelations.end());
        }
      }

      if (declsVisited.size() != szInit) propagate(fwd);
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

        if (hr.isInductive)   // get candidates of form [ <var> mod <const> = <const> ]
          retrieveDeltas (body, hr.srcVars[0], hr.dstVars, candidates[hr.dstRelation]);

        preproGuessing(conjoin(all, m_efac), hr.dstVars, ruleManager.invVars[hr.dstRelation], candidates[hr.dstRelation]);
      }
    }

    void propagateCandidatesBackward(HornRuleExt& hr)
    {
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
        else cands = candidates[dstRel];

        ExprSet mixedCands;
        ExprVector curCnd;

        for (int i = 0; i < rels.size(); i++)
          curCnd.push_back(replaceAll(conjoin(candidates[rels[i]], m_efac),
            ruleManager.invVars[rels[i]], hr.srcVars[i]));

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
          auto tmp = newCnd;
          tmp.insert(curCnd.begin(), curCnd.end());
          shrinkCnjs(tmp);

          for (auto & b : tmp)
            if (find(curCnd.begin(), curCnd.end(), b) == curCnd.end())
              mixedCands.insert(b);
        }

        if (hr.srcVars.size() == 1)
          candidates[rels[0]].insert(mixedCands.begin(), mixedCands.end());
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

          for (auto it = mixedCands.begin(); it != mixedCands.end(); )
          {
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

              Expr r = rels[i];
              if (!u.isSat(a, conjoin(curCnd, m_efac))) return;  // need to recheck because the solver has been reset
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

              // in the case of nonlin, invVars is empty, so no renaming happens:
              preproGuessing(conjoin(all, m_efac), vars, invVars, backGuesses, true, false);

              if (occursNum[r].size() == 1)
              {
                candidates[r].insert(backGuesses.begin(), backGuesses.end());
                histRec.push_back(conjoin(backGuesses, m_efac));
                allGuesses.insert(backGuesses.begin(), backGuesses.end());
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

                    if (!u.isSat(mknary<FORALL>(args), sol.empty() ? mk<TRUE>(m_efac) : disjoin(negModels, m_efac)))
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
              if (!abdHistory[&hr].empty() && abdHistory[&hr].back() == histRec)
              {
                candidates = candidatesTmp;

                for (int i = 0; i < histRec.size(); i++)
                {
                  if (curCnd[i] != histRec[i])
                  {
                    trueCands[i] = false;
                    allGuessesInit.insert(curCnd[i]);
                  }
                  else
                  {
                    numTrueCands++;
                    trueCands[i] = true;
                    trueRels.insert(rels[i]);
                  }
                }

                tryAgain = true; // to keep
              }

              abdHistory[&hr].push_back(histRec);

              if (tryAgain)
              {
                if (abdHistory[&hr].size() > 2 /*hardcoded bound*/)
                {
                  tryAgain = false;
                  for (int i = 0; i < 2 /*hardcoded bound*/; i++)
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
      if (deep > 1) return; // hardcoded bound

      // currently, relies on the order in CHC file; TBD: proper backwards traversing
      for (auto hr = ruleManager.chcs.rbegin(); hr != ruleManager.chcs.rend(); hr++)
      {
        if (!hr->isFact)
        {
          filterUnsat();
          if (!checkCHC(*hr, candidates))
          {
            propagateCandidatesBackward(*hr);
            strengthen(deep+1);
          }
        }
      }
    }

    void getImplicationGuesses(map<Expr, ExprSet>& postconds)
    {
      map<Expr, ExprSet> preconds;
      for (auto & r : ruleManager.chcs)
      {
        if (r.isQuery) continue;

        int srcRelInd = -1;
        Expr rel = r.head->left();
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

    void printCands(bool unsat = true, bool simplify = false)
    {
      if (unsat) outs () << "unsat\n";

      for (auto & a : candidates)
      {
        outs () << "(define-fun " << *a.first << " (";
        for (auto & b : ruleManager.invVars[a.first])
        {
          outs () << "(" << *b << " " << u.varType(b) << ")";
        }
        outs () << ") Bool\n  ";

        ExprSet lms = a.second;
        Expr res = simplifyBool(simplifyArithm(conjoin(lms, m_efac)));
        if (simplify)
        {
          lms.clear();
          getConj(res, lms);
          shrinkCnjs(lms);
          u.removeRedundantConjuncts(lms);
          res = conjoin(lms, m_efac);
        }
        u.print(res);
        outs () << ")\n";
      }
    }

    bool filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (auto & a : candidates)
        if (!u.isSat(a.second))
          for (auto & hr : ruleManager.chcs)
            if (hr.dstRelation == a.first && hr.isFact) worklist.push_back(&hr);

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

      return true;
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

    bool hasQuantifiedCands(map<Expr, ExprSet>& cands)
    {
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

        if (!checkCHC(*hr, candidatesTmp))
        {
          bool res2 = true;
          Expr dstRel = hr->dstRelation;

          Expr model = u.getModel(hr->dstVars);
          if (model == NULL || hasQuantifiedCands(candidatesTmp))
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
            c = simplifyArithm(c);
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
      ExprSet tmp;
      getArrIneqs(unfoldITE(overapproxTransitions(hr->body, hr->srcVars[0], hr->dstVars)), tmp);

      for (auto s : tmp)
      {
        s = replaceAll(s, hr->dstVars, hr->srcVars[0]); // hack for now
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

              ExprSet vvv;
              filter (s, bind::IsConst (), inserter (vvv, vvv.begin())); // prepare vars
              for (auto c : cnjs)
              {
                // naive prop through equalities; works only for some benchs; TODO: extend
                if (!isOpX<EQ>(c)) continue;
                if (find(vvv.begin(), vvv.end(), c->left()) != vvv.end()) s = replaceAll(s, c->left(), c->right());
                else if (find(vvv.begin(), vvv.end(), c->right()) != vvv.end()) s = replaceAll(s, c->right(), c->left());
              }

              ExprVector args;
              args.push_back(qVar->left());
              args.push_back(mk<IMPL>(newRange, s));
              Expr newCand = mknary<FORALL>(args);

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

    bool equalCands(map<Expr, ExprSet>& cands)
    {
      for (auto & a : candidates)
      {
        if (a.second.size() != cands[a.first].size()) return false;
        if (!u.isEquiv(conjoin(a.second, m_efac), conjoin(cands[a.first], m_efac))) return false;
      }
      return true;
    }

    void guessAndSolve()
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
          declsVisited.clear();
          declsVisited.insert(ruleManager.failDecl);
          propagate(fwd);
          filterUnsat();
          if (fwd) multiHoudini(worklist);  // i.e., weaken
          else strengthen();
          if (checkAllOver(true)) return printCands();
        }
        if (equalCands(candidatesTmp)) break;
      }

      getImplicationGuesses(candidates);  // seems broken now; to revisit completely
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return printCands();

      for (auto tgt : ruleManager.decls) arrayGuessing(tgt->left());
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return printCands();
      outs () << "unknown\n";
    }

    // naive solving, without invariant generation
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
          res = res && solveIncrementally(unr + 1, rels2, args2);
        }
      }
      return res;
    }

    // naive solving, without invariant generation
    void solveIncrementally()
    {
      ExprVector query;
      query.push_back(ruleManager.failDecl);
      vector<ExprVector> empt;
      outs () << ((solveIncrementally (0, query, empt)) ? "unsat\n" : "sat\n");
    }
  };

  inline void solveNonlin(string smt, bool inv = true)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    NonlinCHCsolver nonlin(ruleManager);
    if (inv)
      nonlin.guessAndSolve();
    else
      nonlin.solveIncrementally();
  };
}

#endif
