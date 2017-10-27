#ifndef CODESAMPLER__HPP__
#define CODESAMPLER__HPP__

#include "ae/AeValSolver.hpp"
#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  class CodeSampler
  {
    public:

    ExprSet candidates;

    set<int> intConsts;
    set<int> intCoefs;

    HornRuleExt& hr;
    Expr invRel;
    ExprVector invVars;
    ExprMap& extraVars;

    ExprFactory &m_efac;

    CodeSampler(HornRuleExt& r, Expr& d, ExprVector& v, ExprMap& e) :
      hr(r), invRel(d), invVars(v), extraVars(e), m_efac(d->getFactory()) {};

    void addSampleHlp(Expr tmpl, ExprVector& vars, ExprSet& actualVars)
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
              == std::end(vars)) {found = false; break; }
        }
        if (found) newDsjs.insert(dsj);
      }

      if (newDsjs.size() == 0) return;

      tmpl = disjoin (newDsjs, m_efac);
      tmpl = findNonlinAndRewrite(tmpl, vars, invVars, extraVars);

      ExprVector invVarsCstm = invVars;
      for (auto &v : actualVars)
      {
        int index = getVarIndex(v, vars);
        if (index >= 0)
        {
          tmpl = replaceAll(tmpl, v, invVars[index]);
        }
      }

      for (auto &a : extraVars) invVarsCstm.push_back(a.second);

      try
      {
        tmpl = normalizeDisj(tmpl, invVarsCstm);

        if (!isOpX<FALSE> (tmpl) && !isOpX<TRUE> (tmpl))
        {
          candidates.insert(tmpl);

          // get int constants from the normalized candidate
          ExprSet intConstsE;
          expr::filter (tmpl, bind::IsHardIntConst(), std::inserter (intConstsE, intConstsE.begin ()));

          for (auto &a : intConstsE) intConsts.insert(lexical_cast<int>(a));
          getLinCombCoefs(tmpl, intCoefs);
        }
      } catch (const boost::bad_lexical_cast& e) { /*TBD*/ }
    }

    void addSample(Expr term)
    {
      ExprSet actualVars;
      ExprSet subsetInvVars;
      
      expr::filter (term, bind::IsConst(), std::inserter (actualVars, actualVars.begin ()));
      
      term = rewriteMultAdd(term);

      bool locals = false;
      if (actualVars.size() == 0 || isTautology(term)) return;
            
      // split each term to two samples (for srcVars and dstVars)

      if (hr.srcRelation == invRel)
      {
        addSampleHlp(term, hr.srcVars, actualVars);
      }
      
      if (hr.dstRelation == invRel)
      {
        addSampleHlp(term, hr.dstVars, actualVars);
      }
    }
    
    void populateArityAndTemplates(Expr term)
    {
      if (isOpX<NEG>(term))
      {
        addSample(mkNeg(term->last()));             // massage the negated formula a bit
        populateArityAndTemplates(term->last());
      }
      else if (isOpX<OR>(term))
      {
        if (containsOp<AND>(term))
        {
          Expr term2 = convertToGEandGT(rewriteOrAnd(term));
          populateArityAndTemplates(term2);
        }
        else
        {
          Expr term2 = convertToGEandGT(simplifyArithmDisjunctions(term));
          addSample(term2);        // add any disjunct as a sample;
        }
      }
      else if (isOpX<AND>(term))
      {
        for (int i = 0; i < term->arity(); i++)
        {
          populateArityAndTemplates(term->arg(i));
        }
      }
      else if (isOpX<IMPL>(term))
      {
        Expr term2 = mk<OR>(mkNeg(term->left()), term->right());
        populateArityAndTemplates(term2);
      }
      else if (isOpX<GT>(term) || isOpX<GEQ>(term))
      {
        addSample(term);      // get rid of ITEs first
      }
      else if (isOp<ComparissonOp>(term))
      {
        populateArityAndTemplates(convertToGEandGT(term));
      }
    }

    void coreProcess(Expr e)
    {
      e = moveInsideITE(e);
      e = unfoldITE(e);
      e = convertToGEandGT(e);
      populateArityAndTemplates(e);
    }

    void analyzeExtras(ExprSet& extra)
    {
      for (auto &cnj : extra) coreProcess(cnj);
    }

    void analyzeCode()
    {
      if (false) // printing only
      {
        outs() << "\nAnalize CHC:\n";
        outs() << "src vars: ";
        for (int i = 0; i < hr.srcVars.size(); i++) outs() << "[" << *invVars[i] << "] = " << *hr.srcVars[i] << ", ";
        outs() << "\n";
        outs() << "dst vars: ";
        for (int i = 0; i < hr.dstVars.size(); i++) outs() << "[" << *invVars[i] << "] = " << *hr.dstVars[i] << ", ";
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

      if (quantified.size() > 0)
      {
        AeValSolver ae(mk<TRUE>(m_efac), hr.body, quantified);
        if (ae.solve())
        {
          Expr bodyTmp = ae.getValidSubset();
          if (bodyTmp != NULL) body = bodyTmp;
        }
      }

      // get samples and normalize
      ExprSet conds;
      retrieveConds(body, conds);
      for (auto & a : conds) populateArityAndTemplates(a);

      // for the query: add a negation of the entire non-recursive part:
      if (hr.isQuery)
      {
        Expr massaged = propagateEqualities(body);
        coreProcess(mkNeg(massaged));
      }
      else if (hr.isFact)
      {
        coreProcess(body);
      }
      else
      {
        // hr.isInductive
        Expr e = unfoldITE(body);

        ExprSet deltas; // some magic here for enhancing the grammar
        retrieveDeltas(e, hr.srcVars, hr.dstVars, deltas);
        for (auto & a : deltas)
        {
          populateArityAndTemplates(a);
        }

        e = overapproxTransitions(e, hr.srcVars, hr.dstVars);

        e = simplifyBool(e);
        e = convertToGEandGT(e);
        populateArityAndTemplates(e);
      }
    }
  };
}

#endif
