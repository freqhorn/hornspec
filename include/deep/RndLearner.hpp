#ifndef RNDLEARNER__HPP__
#define RNDLEARNER__HPP__

#include "Horn.hpp"
#include "CodeSampler.hpp"
#include "Distribution.hpp"
#include "LinCom.hpp"
#include "ae/SMTUtils.hpp"
#include <iostream>
#include <fstream>

using namespace std;
using namespace boost;
namespace ufo
{
  
  class RndLearner
  {
    private:
    
    ExprFactory &m_efac;
    EZ3 &m_z3;
    SMTUtils u;
    ufo::ZSolver<ufo::EZ3> m_smt_solver;
    vector<ufo::ZSolver<ufo::EZ3>> m_smt_safety_solvers;
    map<int, bool> safety_progress;
    
    CHCs& ruleManager;
    vector<Expr> decls;
    vector<vector<LAfactory>> lfs;
    vector<Expr> curCandidates;
    int invNumber;
    int all;

    bool densecode;           // catch various statistics about the code (mostly, frequences) and setup the prob.distribution based on them
    bool addepsilon;          // add some small probability to features that never happen in the code
    bool aggressivepruning;   // aggressive pruning of the search space based on SAT/UNSAT (WARNING: may miss some invariants)
    
  public:
    
    RndLearner (ExprFactory &efac, EZ3 &z3, CHCs& r, bool b1, bool b2, bool b3) :
      m_efac(efac), m_z3(z3), ruleManager(r), m_smt_solver (z3), u(efac),
      invNumber(0), all(0),
      densecode(b1), addepsilon(b2), aggressivepruning(b3) {}
    
    bool isTautology (Expr a)     // adjusted for big disjunctions
    {
      if (isOpX<TRUE>(a)) return true;
      
      ExprSet disjs;
      getDisj(a, disjs);
      if (disjs.size() == 1) return false;
      
      map<ExprSet, ExprSet> varComb;
      for (auto &a : disjs)
      {
        ExprSet avars;
        expr::filter (a, bind::IsConst(), std::inserter (avars, avars.begin ()));
        varComb[avars].insert(mkNeg(a));
      }
      
      m_smt_solver.reset();
      
      bool res = false;
      for (auto &v : varComb )
      {
        m_smt_solver.assertExpr(conjoin(v.second, m_efac));
        if (!m_smt_solver.solve ())
        {
          res = true; break;
        }
      }
      return res;
    }
    
    bool checkCandidates()
    {
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery) continue;
        
        m_smt_solver.reset();
        
        int ind1;  // to be identified later
        int ind2 = getVarIndex(hr.dstRelation, decls);

        // pushing body
        m_smt_solver.assertExpr (hr.body);
        Expr cand1;
        Expr cand2;
        Expr lmApp;
      
        // pushing src relation
        if (!isOpX<TRUE>(hr.srcRelation))
        {
          ind1 = getVarIndex(hr.srcRelation, decls);
          LAfactory& lf1 = lfs[ind1].back();
          
          cand1 = curCandidates[ind1];
          for (int i = 0; i < hr.srcVars.size(); i++)
          {
            cand1 = replaceAll(cand1, lf1.getVarE(i), hr.srcVars[i]);
          }
          m_smt_solver.assertExpr(cand1);
          
          lmApp = conjoin(lf1.learntExprs, m_efac);
          for (int i = 0; i < hr.srcVars.size(); i++)
          {
            lmApp = replaceAll(lmApp, lf1.getVarE(i), hr.srcVars[i]);
          }
          m_smt_solver.assertExpr(lmApp);
        }
        
        // pushing dst relation
        cand2 = curCandidates[ind2];
        LAfactory& lf2 = lfs[ind2].back();
    
        for (int i = 0; i < hr.dstVars.size(); i++)
        {
          cand2 = replaceAll(cand2, lf2.getVarE(i), hr.dstVars[i]);
        }
        
        m_smt_solver.assertExpr(mk<NEG>(cand2));
        
        all++;
        boost::tribool res = m_smt_solver.solve ();
        if (res)    // SAT   == candidate failed
        {
          curCandidates[ind2] = mk<TRUE>(m_efac);
          return checkCandidates();
        }
      }

      bool res = false;
      for (auto &cand : curCandidates) res = !isOpX<TRUE>(cand);
      return res;
    }
    
    void assignPriorities()
    {
      for (int i = 0; i < invNumber; i++)
      {
        LAfactory& lf = lfs[i].back();
        if (isOpX<TRUE>(curCandidates[i])) lf.assignPrioritiesForFailed(lf.samples.back());
        else lf.assignPrioritiesForLearnt(lf.samples.back());
      }
    }

    void reportCheckingResults()
    {
      for (int i = 0; i < invNumber; i++)
      {
        Expr cand = curCandidates[i];
        LAfactory& lf = lfs[i].back();
        if (isOpX<TRUE>(cand))
        {
          outs () << "    => bad candidate for " << *decls[i] << "\n";
        }
        else
        {
          outs () << "    => learnt lemma for " << *decls[i] << "\n";
          lf.learntExprs.insert(cand);
          lf.learntLemmas.push_back(lf.samples.size() - 1);
        }
      }
    }
    
    void resetLearntLemmas()
    {
      for (auto & lf : lfs)
      {
        lf.back().learntExprs.clear();
        lf.back().learntLemmas.clear();
      }
    }

    void resetSafetySolver()
    {
      int num = 0;
      for (auto &hr: ruleManager.chcs)
      {
        if (!hr.isQuery) continue;

        m_smt_safety_solvers[num].reset();
        m_smt_safety_solvers[num].assertExpr (hr.body);
        safety_progress[num] = false;
        num++;
      }
    }

    bool checkSafety()
    {
      int num = 0;
      for (auto &hr: ruleManager.chcs)
      {
        if (!hr.isQuery) continue;
        num++;

        int ind = getVarIndex(hr.srcRelation, decls);
        Expr invApp = curCandidates[ind];
        if (safety_progress[num-1] == true) continue;

        LAfactory& lf = lfs[ind].back();

        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          invApp = replaceAll(invApp, lf.getVarE(i), hr.srcVars[i]);
        }

        m_smt_safety_solvers[num-1].assertExpr(invApp);
        safety_progress[num-1] = !m_smt_safety_solvers[num-1].solve ();

        all++;
      }

      for (auto a : safety_progress) if (a.second == false) return false;
      return true;
    }
    
    void setupSafetySolver()
    {
      // setup the safety solver
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery)
        {
          m_smt_safety_solvers.push_back(ufo::ZSolver<ufo::EZ3>(m_z3));
          m_smt_safety_solvers.back().assertExpr (hr.body);
          safety_progress[safety_progress.size()] = false;
        }
      }
    }
    
    void serializeInvariants(vector<ExprSet>& invs, const char * outfile)
    {

      ofstream invfile;
      invfile.open (string(outfile));
      m_smt_solver.reset();

      for (auto & i : invs) m_smt_solver.assertExpr(conjoin(i, m_efac));

      m_smt_solver.toSmtLib (invfile);
      invfile.flush ();
      outs () << "\nInvariant serialized to " << outfile << "\n";
    }

    void updateRels()
    {
      // this should not affect the learning process for a CHC system with one (declare-rel ...)

      set<int> rels2update;

      for (int ind = 0; ind < invNumber; ind++)
      {
        Expr cand = curCandidates[ind];
        LAfactory& lf = lfs[ind].back();
        if (!isOpX<TRUE>(cand))
        {
          for (auto &hr : ruleManager.chcs)
          {
            if ( hr.srcRelation == decls[ind] &&
                hr.dstRelation != decls[ind] &&
                !hr.isQuery)
            {
              Expr lemma2add = curCandidates[ind];
              for (int i = 0; i < hr.srcVars.size(); i++)
              {
                lemma2add = replaceAll(lemma2add, lf.getVarE(i), hr.srcVars[i]);
              }

              all++;
              if (u.isImplies(hr.body, lemma2add)) continue;

              hr.lin.push_back(lemma2add);
              hr.body = mk<AND>(hr.body, lemma2add);

              rels2update.insert(getVarIndex(hr.dstRelation, decls));
            }
          }
        }
      }

      for(auto ind : rels2update)
      {
        vector<LAfactory>& lf = lfs[ind];
        lf.push_back(LAfactory (m_efac, aggressivepruning));
        LAfactory& lf_before = lf[lf.size()-2];
        LAfactory& lf_after = lf.back();

        for (auto a : lf_before.getVars())
        {
          lf_after.addVar(a);
        }

        doCodeSampling(decls[ind]);

        for (auto a : lf_before.learntExprs)
        {
          lf_after.learntExprs.insert(a);
          lf_after.samples.push_back(LAdisj());
          LAdisj& lcs = lf_after.samples.back();
          if (lf_after.exprToLAdisj(a, lcs))
          {
            lf_after.assignPrioritiesForLearnt(lcs);
            lf_after.learntLemmas.push_back (lf_after.samples.size() - 1);
          }
        }
      }
    }

    void initializeDecl(Expr invDecl)
    {
      assert (invDecl->arity() > 2);
      assert(decls.size() == invNumber);
      assert(lfs.size() == invNumber);
      assert(curCandidates.size() == invNumber);
      
      decls.push_back(invDecl->arg(0));
      curCandidates.push_back(NULL);
      
      lfs.push_back(vector<LAfactory> ());
      lfs.back().push_back(LAfactory (m_efac, aggressivepruning));
      LAfactory& lf = lfs.back().back();
      
      invNumber++;
      
      for (int i = 1; i < invDecl->arity()-1; i++)
      {
        Expr new_name = mkTerm<string> ("__v__" + to_string(i - 1), m_efac);
        Expr var = bind::mkConst(new_name, invDecl->arg(i));
        lf.addVar(var);
      }
    }

    void doCodeSampling(Expr invRel, bool print=false)
    {
      vector<CodeSampler> css;
      set<int> orArities;
      set<int> progConstsTmp;
      set<int> progConsts;
      set<int> intCoefs;
      
      int ind = getVarIndex(invRel, decls);
      LAfactory& lf = lfs[ind].back();

      // analize each rule separately:
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != invRel && hr.srcRelation != invRel) continue;
        
        css.push_back(CodeSampler(hr, invRel, lf.getVars(), lf.nonlinVars));
        css.back().analyzeCode();
        
        // convert intConsts to progConsts and add additive inverses (if applicable):
        for (auto &a : css.back().intConsts)
        {
          progConstsTmp.insert( a);
          progConstsTmp.insert(-a);
        }
        
        // same for intCoefs
        for (auto &a : css.back().intCoefs)
        {
          intCoefs.insert( a);
          intCoefs.insert(-a);
        }
      }
      
      if (print && lf.nonlinVars.size() > 0)
      {
        outs() << "Multed vars: ";
        for (auto &a : lf.nonlinVars)
        {
          outs() << *a.first << " = " << *a.second << "\n";
          lf.addVar(a.second);
        }
      }
      
      for (auto &a : intCoefs) if (a != 0) lf.addIntCoef(a);

      for (auto &a : intCoefs)
      {
        for (auto &b : progConstsTmp)
        {
          progConsts.insert(a*b);
        }
      }
      
      // sort progConsts and push to vector:
      while (progConsts.size() > 0)
      {
        int min = INT_MAX;
        for (auto c : progConsts)
        {
          if (c < min)
          {
            min = c;
          }
        }
        progConsts.erase(min);
        lf.addConst(min);
      }
      
      lf.initialize();

      // normalize samples obtained from CHCs and calculate various statistics:
      vector<LAdisj> lcss;
      for (auto &cs : css)
      {
        for (auto &cand : cs.candidates)
        {
          lcss.push_back(LAdisj());
          LAdisj& lcs = lcss.back();
          if (lf.exprToLAdisj(cand, lcs))
          {
            lcs.normalizePlus();
            orArities.insert(lcs.arity);
          }
          else
          {
            lcss.pop_back();
          }
        }
      }
      
      if (orArities.size() == 0)                // default, if no samples were obtained from the code
      {
        for (int i = 1; i <= DEFAULTARITY; i++) orArities.insert(i);
      }
      
      lf.initDensities(orArities);
      
      if (densecode)
      {
        // collect number of occurrences....

        for (auto &lcs : lcss)
        {
          int ar = lcs.arity;

          // of arities of application of OR
          lf.orAritiesDensity[ar] ++;
          
          for (auto & lc : lcs.dstate)
          {
            // of arities of application of PLUS
            lf.plusAritiesDensity[ar][lc.arity] ++;
            
            // of constants
            lf.intConstDensity[ar][lc.intconst] ++;
            
            // of comparison operations
            lf.cmpOpDensity[ar][lc.cmpop] ++;
            
            set<int> vars;
            int vars_id = -1;
            for (int j = 0; j < lc.vcs.size(); j = j+2) vars.insert(lc.vcs[j]);
            for (int j = 0; j < lf.varCombinations[ar][lc.arity].size(); j++)
            {
              if (lf.varCombinations[ar][lc.arity][j] == vars)
              {
                vars_id = j;
                break;
              }
            }
            assert(vars_id >= 0);

            // of variable combinations
            lf.varDensity[ar][lc.arity][vars_id] ++;

            // of variable coefficients
            for (int j = 1; j < lc.vcs.size(); j = j+2)
            {
              lf.coefDensity[ ar ][ lc.vcs [j-1] ] [lc.vcs [j] ] ++;
            }
          }
        }
      }
      else
      {
        // same thing as in above; but instead of precise frequencies, we gather a rough presence
        for (auto &lcs : lcss)
        {
          int ar = lcs.arity;

          // of arities of application of OR
          lf.orAritiesDensity[ar] = 1;

          for (auto & lc : lcs.dstate)
          {
            // of arities of application of PLUS
            lf.plusAritiesDensity[ar][lc.arity] = 1;

            // of constants
            lf.intConstDensity[ar][lc.intconst] = 1;

            // of comparison operations
            lf.cmpOpDensity[ar][lc.cmpop] = 1;

            set<int> vars;
            int vars_id = -1;
            for (int j = 0; j < lc.vcs.size(); j = j+2) vars.insert(lc.vcs[j]);
            for (int j = 0; j < lf.varCombinations[ar][lc.arity].size(); j++)
            {
              if (lf.varCombinations[ar][lc.arity][j] == vars)
              {
                vars_id = j;
                break;
              }
            }
            assert(vars_id >= 0);

            // of variable combinations
            lf.varDensity[ar][lc.arity][vars_id] = 1;

            // of variable coefficients
            for (int j = 1; j < lc.vcs.size(); j = j+2)
            {
              lf.coefDensity[ ar ][ lc.vcs [j-1] ] [lc.vcs [j] ] = 1;
            }
          }
        }
      }

      lf.stabilizeDensities(orArities, addepsilon);
      if (print)
      {
        outs() << "\nStatistics for " << *invRel << ":\n";
        lf.printCodeStatistics(orArities);
      }
    }
    
    void synthesize(int maxAttempts, char * outfile)
    {
      bool success = false;
      int iter = 1;
    
      for (int i = 0; i < maxAttempts; i++)
      {
        // first, guess candidates for each inv.declaration
        
        bool skip = false;
        for (int j = 0; j < invNumber; j++)
        {
          if (curCandidates[j] != NULL) continue;   // if the current candidate is good enough
          LAfactory& lf = lfs[j].back();
          Expr cand = lf.getFreshCandidate();
          if (cand == NULL)
          {
            skip = true;
            break;
          }

          if (isTautology(cand))  // keep searching
          {
            lf.assignPrioritiesForLearnt(lf.samples.back());
            skip = true;
            break;
          }

          if (lf.nonlinVars.size() > 0 && !u.isSat(cand))  // keep searching
          {
            lf.assignPrioritiesForFailed(lf.samples.back());
            skip = true;
            break;
          }

          curCandidates[j] = cand;
        }
        
        if (skip) continue;
        
        outs() << "\n  ---- new iteration " << iter++ <<  " ----\n";
        for (int j = 0; j < invNumber; j++) outs () << "candidate for " << *decls[j] << ": " << *curCandidates[j] << "\n";
        
        // check all the candidates at once for all CHCs :
        
        if (checkCandidates())
        {
          if (checkSafety())       // query is checked here
          {
            success = true;
          }
        }

        reportCheckingResults();

        if (success) break;

        assignPriorities();
        updateRels();

        for (auto &cand : curCandidates) cand = NULL; // preparing for the next iteration
      }
      
      if (success) outs () << "\n -----> Success after " << --iter      << " iterations\n";
      else         outs () <<      "\nNo success after " << maxAttempts << " iterations\n";
      
      outs () << "        total number of SMT checks: " << all << "\n";

      if (success && outfile != NULL)
      {
        vector<ExprSet> invs;
        for (auto & lf : lfs) invs.push_back(lf.back().learntExprs);
        serializeInvariants(invs, outfile);
      }
    }

    void checkAllLemmas(vector<ExprSet>& lms, vector<ExprSet>& curMinLms, int& numTries, int invInd)
    {
      numTries++;
      resetSafetySolver();
      resetLearntLemmas();
      for (int i = 0; i < invNumber; i++) curCandidates[i] = conjoin(lms[i], m_efac);

      if (checkCandidates() && checkSafety())
      {
        if (lms[invInd].size() < curMinLms[invInd].size()) curMinLms[invInd] = lms[invInd];

        for (auto & a : lms[invInd])
        {
          vector<ExprSet> lmsTry = lms;
          lmsTry[invInd].erase(a);

          checkAllLemmas(lmsTry, curMinLms, numTries, invInd);
        }
      }
    }
  };
  
  
  inline void learnInvariants(string smt, char * outfile, int maxAttempts, bool b1=true, bool b2=true, bool b3=true)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    RndLearner ds(m_efac, z3, ruleManager, b1, b2, b3);

    ds.setupSafetySolver();
    std::srand(std::time(0));

    if (ruleManager.decls.size() > 1)
    {
      outs() << "WARNING: learning multiple invariants is currently unstable\n"
             << "         it is suggested to disable \'aggressivepruning\'\n";
    }

    for (auto& dcl: ruleManager.decls)
    {
      ds.initializeDecl(dcl);
      ds.doCodeSampling (dcl->arg(0), true);
    }

    ds.synthesize(maxAttempts, outfile);
  };


  inline void getInductiveValidityCore (const char * chcfile, const char * invfile)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(string(chcfile));
    RndLearner ds(m_efac, z3, ruleManager, false, false, false);
    ds.setupSafetySolver();

    vector<string> invNames;
    for (auto& dcl: ruleManager.decls)
    {
      ds.initializeDecl(dcl);
      invNames.push_back(lexical_cast<string>(dcl->arg(0)));
    }

    Expr invTmp = z3_from_smtlib_file (z3, invfile);

    vector<Expr> invs;
    if (ruleManager.decls.size() == 1) invs.push_back(invTmp);
    else
    {
      // each assert in invfile corresponds to an invariant
      // after deserialization, all asserts are conjoined; so we need to split them now
      for (int i = 0; i < ruleManager.decls.size(); i++)
      {
        invs.push_back(invTmp->arg(i));
      }
    }

    vector<ExprSet> lms;
    vector<vector<int>> sizeHistories;

    for (auto & inv : invs)
    {
      vector<int> sizeHistory;
      sizeHistory.push_back(isOpX<AND>(inv) ? inv->arity() : (isOpX<TRUE>(inv) ? 0 : 1));

      SMTUtils u(m_efac);
      inv = u.removeRedundantConjuncts(inv);       // rough simplification first

      sizeHistory.push_back(isOpX<AND>(inv) ? inv->arity() : (isOpX<TRUE>(inv) ? 0 : 1));
      sizeHistories.push_back(sizeHistory);

      ExprSet lm;
      getConj(inv, lm);
      lms.push_back(lm);
    }

    vector<ExprSet> lmsMin = lms;

    for (int i = 0; i < invs.size(); i++)
    {
      outs () << "Size reduction for " << invNames[i] << ": ";
      for (auto a : sizeHistories[i]) outs () << a << " -> ";
      int numTries = 0;
      ds.checkAllLemmas(lms, lmsMin, numTries, i); // accurate simplification then
      assert (numTries > 1);

      outs () << lmsMin[i].size() << "\n";
    }

    ds.serializeInvariants(lmsMin, invfile);
  }
}

#endif
