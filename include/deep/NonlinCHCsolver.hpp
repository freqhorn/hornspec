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

    public:

    NonlinCHCsolver (CHCs& r) : m_efac(r.m_efac), ruleManager(r), u(m_efac) {}

    Expr quantifierElimination(Expr& cond, ExprSet& vars)
    {
      if (vars.size() == 0) return cond;
      Expr newCond;
      if (isNonlinear(cond)) {
        newCond = simpleQE(cond, vars, true, true);
        if (!u.implies(cond, newCond)) {
          newCond = mk<TRUE>(m_efac);
        }
      } else {
        AeValSolver ae(mk<TRUE>(m_efac), cond, vars); // exists quantified . formula
        if (ae.solve()) {
          newCond = ae.getValidSubset();
        } else {
          newCond = mk<TRUE>(m_efac);
        }
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
      return !u.isSat(checkList);
    }

    void preproGuessing(Expr e, ExprVector& ev1, ExprVector& ev2, ExprSet& guesses)
    {
      ExprSet ev3;
      filter (e, bind::IsConst (), inserter (ev3, ev3.begin())); // prepare vars
      for (auto it = ev3.begin(); it != ev3.end(); )
      {
        if (find(ev1.begin(), ev1.end(), *it) == ev1.end()) ++it;
        else it = ev3.erase(it);
      }
      e = quantifierElimination(e, ev3);

      ExprSet cnjs;

      getConj(e, cnjs);
      for (auto & c1 : cnjs)
      {
        if (isOpX<OR>(c1)) continue;
        for (auto & c2 : cnjs)
        {
          if (!isOpX<OR>(c2)) continue;
          ExprSet dsjs;
          ExprSet newDsjs;
          getDisj(c2, dsjs);
          for (auto & d : dsjs)
          {
            if (u.implies(c1, d))
            {
              e = replaceAll(e, c2, mk<TRUE>(m_efac));
              newDsjs.clear();
              break;
            }
            if (!u.implies(mkNeg(c1), d)) newDsjs.insert(d);
          }
          if (newDsjs.size() > 0) e = replaceAll(e, c2, disjoin(newDsjs, m_efac));
        }
      }
      mutateHeuristic(replaceAll(e, ev1, ev2), guesses);
    }

    void bootstrapping()
    {
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery)
        {
          if (!containsOp<ARRAY_TY>(hr.body))
          {
            for (int i = 0; i < hr.srcVars.size(); i++)
            {
              ExprSet vars;
              vars.insert(hr.locVars.begin(), hr.locVars.end());
              Expr q = quantifierElimination(hr.body, vars); //we shouldn't do it here; to fix
              preproGuessing(mk<NEG>(q), hr.srcVars[i],
                             ruleManager.invVars[hr.srcRelations[i]], candidates[hr.srcRelations[i]]);
            }
          }
        }
        else
        {
          Expr rel = hr.head->left();
          preproGuessing(hr.body, hr.dstVars, ruleManager.invVars[rel], candidates[hr.dstRelation]);
        }
      }
    }

    void propagateCandidatesForward()
    {
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery) continue;
        ExprSet all;
        all.insert(hr.body);
        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          Expr rel = hr.srcRelations[i];
          // currently, tries all candidates; but in principle, should try various subsets
          for (auto & c : candidates[rel])
            all.insert(replaceAll(c, ruleManager.invVars[rel], hr.srcVars[i]));
        }
        preproGuessing(conjoin(all, m_efac), hr.dstVars,
                       ruleManager.invVars[hr.dstRelation], candidates[hr.dstRelation]);
      }
    }

    void propagateCandidatesBackward()
    {
      // TODO
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

    void printCands(bool unsat = true, bool simplify = true)
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
        if (simplify) u.removeRedundantConjuncts(lms);
        Expr res = simplifyArithm(conjoin(lms, m_efac));
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
            if (hr.dstRelation == a.first) worklist.push_back(&hr);

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
      HornRuleExt *hr;

      // preprocessing
      for (auto & a : ruleManager.chcs)
      {
        if (a.isInductive && a.dstRelation == tgt &&
            (containsOp<SELECT>(a.body) || containsOp<STORE>(a.body)))
        {
          ExprVector counters;
          hr = &a;

          getCounters(a.body, counters);
          for (auto & c : counters)
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
          ExprSet cnjs;
          getConj(a.body, cnjs);
          for (Expr e : cnjs)
          {
            if (isOpX<EQ>(e) && (e->left() == a.dstVars[ind] || e->right() == a.dstVars[ind]))
            {
              Expr bound = (e->left() == a.dstVars[ind]) ? e->right() : e->left();
              range = iterGrows ? mk<AND>(mk<LEQ>(bound, qVar), mk<LT>(qVar, iterator)) :
                                  mk<AND>(mk<LT>(iterator, qVar), mk<LEQ>(qVar, bound));
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
    }

    // very restricted version of FreqHorn (no grammars, limited use of arrays)
    void guessAndSolve()
    {
      bootstrapping();

      auto post = candidates;
      filterUnsat();

      propagateCandidatesForward();

      vector<HornRuleExt*> worklist;
      for (auto & hr : ruleManager.chcs) worklist.push_back(&hr); // todo: wto
      multiHoudini(worklist);

      if (checkAllOver(true)) return printCands();

      getImplicationGuesses(post);
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
