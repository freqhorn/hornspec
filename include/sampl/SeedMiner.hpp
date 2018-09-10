#ifndef SEEDMINER__HPP__
#define SEEDMINER__HPP__

#include "ae/AeValSolver.hpp"
#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  class SeedMiner
  {
    public:

    // for arrays
    ExprSet arrCands;
    ExprSet arrSelects;
    ExprSet arrIterRanges;
    ExprSet arrAccessVars;

    ExprSet candidates;
    set<int> intConsts;
    set<int> intCoefs;

    HornRuleExt& hr;
    Expr invRel;
    map<int, Expr>& invVars;
    ExprMap& extraVars;

    ExprFactory &m_efac;

    SeedMiner(HornRuleExt& r, Expr& d, map<int, Expr>& v, ExprMap& e) :
      hr(r), invRel(d), invVars(v), extraVars(e), m_efac(d->getFactory()) {};

    void getSelectTmpl (Expr tmpl)
    {
      ExprSet dsjs;
      ExprSet tmp;
      getDisj(tmpl, dsjs);
      ExprVector invAndIterVarsAll;
      for (auto & a : invVars) invAndIterVarsAll.push_back(a.second);

      for (auto dsj : dsjs)
      {
        ExprSet se;
        filter (dsj, bind::IsSelect (), inserter(se, se.begin()));
        if (se.size() == 0)
        {
          tmp.insert(mkNeg(dsj));
          continue;
        }

        ExprVector invAndIterVars;
        for (auto & a : invVars) invAndIterVars.push_back(a.second);

        for (auto & a : se)
        {
          arrSelects.insert(a);
          invAndIterVars.push_back(a);
          assert (bind::isIntConst(a->right())); // complex indexes like A[i+1] are supposed to be rewritten in Horn.hpp

          arrAccessVars.insert(a->right());
          if (find(invAndIterVars.begin(), invAndIterVars.end(),
                   a->right()) == invAndIterVars.end())
            invAndIterVars.push_back (a->right());

          if (find(invAndIterVarsAll.begin(), invAndIterVarsAll.end(),
                   a->right()) == invAndIterVarsAll.end())
            invAndIterVarsAll.push_back(a->right());
        }

        ExprSet arrCandsTmp;
        getConj(convertToGEandGT(dsj), arrCandsTmp);
        for (auto & a : arrCandsTmp) arrCands.insert(normalizeDisj(a, invAndIterVars));
      }

      if (arrCands.size() == 0) return;

      for (auto & e : tmp)
      {
        ExprSet rangeTmp;
        getConj(convertToGEandGT(e), rangeTmp);
        for (auto & a : rangeTmp) arrIterRanges.insert(normalizeDisj(a, invAndIterVarsAll));
      }
    }

    void addSeedHlp(Expr tmpl, ExprVector& vars, ExprSet& actualVars)
    {
      ExprSet dsjs;
      ExprSet newDsjs;
      getDisj(tmpl, dsjs);
      for (auto & dsj : dsjs)
      {
        ExprSet vrs;
        expr::filter (dsj, bind::IsConst(), std::inserter (vrs, vrs.begin ()));
        bool found = true;

        for (auto & a : vrs)
        {
          if (std::find(std::begin(vars), std::end (vars), a)
              == std::end(vars)) { found = false; break; }
        }
        if (found) newDsjs.insert(dsj);
      }

      if (newDsjs.size() == 0) return;

      ExprVector invVarsCstm;
      for (auto & a : invVars) invVarsCstm.push_back(a.second);

      tmpl = disjoin (newDsjs, m_efac);

      for (auto &v : actualVars)
      {
        int index = getVarIndex(v, vars);
        if (index >= 0)
        {
          tmpl = replaceAll(tmpl, v, invVars[index]);
        }
      }

      tmpl = findNonlinAndRewrite(tmpl, invVarsCstm, extraVars);

      for (auto &a : extraVars) invVarsCstm.push_back(a.second);
      tmpl = normalizeDisj(tmpl, invVarsCstm);

      if (!isOpX<FALSE> (tmpl) && !isOpX<TRUE> (tmpl))
      {
        // get int constants from the normalized candidate
        ExprSet intConstsE;
        expr::filter (tmpl, bind::IsHardIntConst(), std::inserter (intConstsE, intConstsE.begin ()));
        for (auto &a : intConstsE) intConsts.insert(lexical_cast<int>(a));
        if (getLinCombCoefs(tmpl, intCoefs)) candidates.insert(tmpl);
      }
    }

    void addSeed(Expr term)
    {
      ExprSet actualVars;

      expr::filter (term, bind::IsConst(), std::inserter (actualVars, actualVars.begin ()));

      term = rewriteMultAdd(term);

      bool locals = false;
      if (actualVars.size() == 0 || isTautology(term)) return;
            
      // split each term to two seeds (for srcVars and dstVars)

      if (hr.srcRelation == invRel)
      {
        addSeedHlp(term, hr.srcVars, actualVars);
      }

      if (hr.dstRelation == invRel)
      {
        addSeedHlp(term, hr.dstVars, actualVars);
      }
    }

    void obtainSeeds(Expr term)
    {
      if (bind::isBoolConst(term))
      {
        addSeed(term);
      }
      else if (isOpX<NEG>(term))
      {
        Expr negged = term->last();
        if (bind::isBoolConst(negged))
          addSeed(term);
        else
          obtainSeeds(negged);
      }
      else if (isOpX<OR>(term))
      {
        if (containsOp<AND>(term))
        {
          Expr term2 = convertToGEandGT(rewriteOrAnd(term));
          obtainSeeds(term2);
        }
        else
        {
          Expr simplified = simplifyArithmDisjunctions(term);
          if (isOpX<TRUE>(simplified))
          {
            for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it)
              addSeed(*it);
          }
          else
          {
            Expr term2 = convertToGEandGT(simplified);
            addSeed(term2);
          }
        }
      }
      else if (isOpX<AND>(term))
      {
        for (int i = 0; i < term->arity(); i++)
        {
          obtainSeeds(term->arg(i));
        }
      }
      else if (isOpX<IMPL>(term))
      {
        Expr term2 = mk<OR>(mkNeg(term->left()), term->right());
        obtainSeeds(term2);
      }
      else if (isOpX<GT>(term) || isOpX<GEQ>(term))
      {
        addSeed(term);      // get rid of ITEs first
      }
      else if (isOp<ComparissonOp>(term))
      {
        obtainSeeds(convertToGEandGT(term));
      }
    }

    void coreProcess(Expr e)
    {
      e = rewriteBoolEq(e);
      e = moveInsideITE(e);
      e = unfoldITE(e);
      e = convertToGEandGT(e);
      e = rewriteNegAnd(e);
      obtainSeeds(e);
    }

    void analizeExtras(ExprSet& extra)
    {
      for (auto &cnj : extra)
        coreProcess(propagateEqualities(cnj));
    }

    void analizeExtras(Expr extra)
    {
      coreProcess(propagateEqualities(extra));
    }

    void analizeCode()
    {
      if (false) // printing only
      {
        outs() << "Analize CHC: " << *hr.srcRelation << " -> " << *hr.dstRelation << ":\n";
        outs() << "src vars: ";
        for (int i = 0; i < hr.srcVars.size(); i++) outs() << *hr.srcVars[i] << ", ";
        outs() << "\n";
        outs() << "dst vars: ";
        for (int i = 0; i < hr.dstVars.size(); i++) outs() << *hr.dstVars[i] << ", ";
        outs() << "\n";
        outs() << "local vars: ";
        for (auto & a : hr.locVars) outs() << *a << ", ";
        outs() << "\n";
        outs() << "body: " << *hr.body << "\n\n";
      }

      Expr body = hr.body;

      // black magic to get rid of irrelevant variables
      ExprSet quantified;
      for (auto &v : hr.locVars) quantified.insert(v);
      if (hr.srcRelation != invRel) for (auto &v : hr.srcVars) quantified.insert(v);
      if (hr.dstRelation != invRel) for (auto &v : hr.dstVars) quantified.insert(v);

      if (hr.srcRelation == invRel)
        for (int i = 0; i < hr.srcVars.size(); i++)
          if (invVars[i] == NULL) quantified.insert(hr.srcVars[i]);

      if (hr.dstRelation == invRel)
        for (int i = 0; i < hr.dstVars.size(); i++)
          if (invVars[i] == NULL) quantified.insert(hr.dstVars[i]);

      if (quantified.size() > 0)
      {
        AeValSolver ae(mk<TRUE>(m_efac), hr.body, quantified);
        if (ae.solve())
        {
          Expr bodyTmp = ae.getValidSubset();
          if (bodyTmp != NULL)
          {
            body = bodyTmp;
          }
        }
      }

      // get seeds and normalize
      ExprSet conds;
      retrieveConds(body, conds);
      for (auto & a : conds) obtainSeeds(a);

      // for the query: add a negation of the entire non-recursive part:
      if (hr.isQuery)
      {
        Expr massaged = propagateEqualities(body);
        coreProcess(mkNeg(massaged));
        getSelectTmpl(mkNeg(hr.body));
      }
      else if (hr.isFact)
      {
        coreProcess(propagateEqualities(body));
      }
      else
      {
        // hr.isInductive
        Expr e = unfoldITE(body);
        ExprSet deltas; // some magic here for enhancing the grammar
        retrieveDeltas(e, hr.srcVars, hr.dstVars, deltas);
        for (auto & a : deltas)
        {
          obtainSeeds(a);
        }
        e = overapproxTransitions(e, hr.srcVars, hr.dstVars);
        e = simplifyBool(e);
        e = rewriteBoolEq(e);
        e = convertToGEandGT(e);
        e = rewriteNegAnd(e);
        obtainSeeds(e);
      }
    }
  };
}

#endif
