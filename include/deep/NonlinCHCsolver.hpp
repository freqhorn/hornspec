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
    map<Expr, Expr> over;
    map<Expr, ExprSet> allGuesses;

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

      return newCond;
    }

    bool checkAllOver (bool checkQuery = false)
    {
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery && !checkQuery) continue;
        ExprSet checkList;
        checkList.insert(hr.body);
        Expr overBody;
        Expr rel;
        for (int i = 0; i < hr.srcRelations.size(); i++)
        {
          Expr rel = hr.srcRelations[i];
          overBody = replaceAll(over[rel], ruleManager.invVars[rel], hr.srcVars[i]);
          getConj(overBody, checkList);
        }
        if (!hr.isQuery)
        {
          rel = hr.dstRelation;
          ExprSet tmp;
          ExprSet negged;
          getConj(replaceAll(over[rel], ruleManager.invVars[rel], hr.dstVars), tmp);
          for (auto a : tmp) negged.insert(mkNeg(a));
          checkList.insert(disjoin(negged, m_efac));
        }
        if (u.isSat(checkList)) return false;
      }
      return true;
    }

    bool fastGuessCheck (Expr tgt, Expr guess, bool toAdd = true) {
      Expr ov = over[tgt];
      if (u.implies(ov, guess)) return true;
      over[tgt] = mk<AND>(ov, guess);

      if (checkAllOver())
      {
        //errs()  << " guess: " << *guess << " -> true!\n";
        if (toAdd)
        {
          // recheck old guesses
          for (auto it = allGuesses[tgt].begin(); it != allGuesses[tgt].end(); )
          {
            if (fastGuessCheck(tgt, *it, false)) it = allGuesses[tgt].erase(it);
            else ++it;
          }
          for (auto & g : allGuesses[tgt]) fastGuessCheck(tgt, g, false);
        }
        return true;
      }
      else
      {
        over[tgt] = ov;
        if (toAdd) allGuesses[tgt].insert(guess);
        return false;
      }
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
      map<Expr, ExprSet> preconds;
      for (auto & r : ruleManager.chcs) {
        ExprSet guesses;
        if (r.isQuery)
        {
          for (int i = 0; i < r.srcVars.size(); i++)
          {
            ExprSet vars;
            vars.insert(r.locVars.begin(), r.locVars.end());
            Expr q = quantifierElimination(r.body, vars); //we shouldn't do it here; to fix
            guesses.clear();
            preproGuessing(mk<NEG>(q), r.srcVars[i],
                           ruleManager.invVars[r.srcRelations[i]], guesses);
            for (auto & guess : guesses) fastGuessCheck(r.srcRelations[i], guess);
          }

          continue;
        }

        int srcRelInd = -1;
        for (int i = 0; i < r.srcVars.size(); i++) if (r.srcRelations[i] == r.head->arg(0)) srcRelInd = i;
        if (srcRelInd >= 0)
          preproGuessing(r.body, r.srcVars[srcRelInd],
                      ruleManager.invVars[r.head->arg(0)], preconds[r.head->arg(0)]);

        preproGuessing(r.body, r.dstVars, ruleManager.invVars[r.head->arg(0)], guesses);

        for (auto guess : guesses) fastGuessCheck(r.head->arg(0), guess);

        // get "implication" guesses
        int tot = 0;
        for (auto guess : allGuesses[r.head->arg(0)])
        {
          if (tot > 30) break; // empirically chosen bound
          if (isOpX<IMPL>(guess)) continue; // hack

          for (auto & pre : preconds[r.head->arg(0)])
          {
            if (u.implies(pre, guess)) continue;
            tot++;
            Expr newGuess = mk<IMPL>(pre, guess);
            if (fastGuessCheck(r.head->arg(0), newGuess))
            {
              ExprSet tmpGuesses;
              int srcRelInd = -1;
              for (int i = 0; i < r.srcVars.size(); i++) if (r.srcRelations[i] == r.head->arg(0)) srcRelInd = i;
              if (srcRelInd == -1) continue;
              ExprVector tmp;
              tmp.push_back(replaceAll(newGuess, ruleManager.invVars[r.head->arg(0)], r.srcVars[srcRelInd]));
              tmp.push_back(r.body);
              tmp.push_back(mkNeg(replaceAll(pre, ruleManager.invVars[r.head->arg(0)], r.dstVars)));
              preproGuessing(conjoin(tmp, m_efac), r.dstVars, ruleManager.invVars[r.head->arg(0)], tmpGuesses);
              for (auto guess : tmpGuesses) fastGuessCheck(r.head->arg(0), guess);
            }
          }
        }
      }
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
            ind = getVarIndex(c, a.srcVars[0]);

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
        if (fastGuessCheck(tgt, mknary<FORALL>(args), true))
        {
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
              fastGuessCheck(hr2.dstRelation, newCand);
            }
          }
        }
      }
    }

    // very restricted version of FreqHorn (no grammars, limited use of arrays)
    void guessAndSolve()
    {
      for (auto tgt : ruleManager.decls) over[tgt->left()] = mk<TRUE>(m_efac);
      bootstrapping();
      for (auto tgt : ruleManager.decls) arrayGuessing(tgt->left());
      outs () << ((checkAllOver(true)) ? "unsat\n" : "unknown\n");
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
