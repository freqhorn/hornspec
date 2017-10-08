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
    
    Expr zero;
    ExprFactory &m_efac;
    
    CodeSampler(HornRuleExt& r, Expr& d, ExprVector& v, ExprMap& e) :
      hr(r), invRel(d), invVars(v), extraVars(e), m_efac(d->getFactory())
    {
      // add some "universal" constants
      intConsts.insert(0);
      intConsts.insert(1);
      intConsts.insert(-1);

      // aux Expr const
      zero = mkTerm (mpz_class (0), m_efac);
    };
    
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
    }
    
    void processTransition(Expr tmpl, ExprVector& srcVars, ExprVector& dstVars, ExprSet& actualVars)
    {
      if (containsOp<IDIV>(tmpl) || containsOp<DIV>(tmpl) ||
          containsOp<MOD>(tmpl) || containsOp<MULT>(tmpl)) return; // GF: to optimize

      int found = false;
      // very simple check if there are some srcVars and dstVars in the tmpl
      
      for (auto &v0 : srcVars)
      {
        for (auto &v1 : actualVars)
        {
          if (v0 == v1)
          {
            found = true;
            break;
          }
        }
      }
      
      if (! found) return;
      
      found = false;
      for (auto &v0 : dstVars)
      {
        for (auto &v1 : actualVars)
        {
          if (v0 == v1)
          {
            found = true;
            break;
          }
        }
      }
      
      if (! found) return;
      
      for (auto &v : actualVars)
      {
        int index1 = getVarIndex(v, srcVars);
        int index2 = getVarIndex(v, dstVars);
        if (index1 == -1 && index2 == -1) return;
      }
      
      ExprVector vars;
      for (auto &v : actualVars) vars.push_back(v);

      ExprSet intCoefsE;
      expr::filter (normalizeDisj(tmpl, vars), bind::IsHardIntConst(), std::inserter (intCoefsE, intCoefsE.begin ()));
      
      for (auto &a : intCoefsE)
      {
        intCoefs.insert(lexical_cast<int>(a));
      }
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

      if (hr.dstRelation == hr.srcRelation)
      {
        processTransition(term, hr.srcVars, hr.dstVars, actualVars);
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
        outs() << "body: " << *hr.body << "\n\n";
      }
      
      intCoefs.insert(1);
      intConsts.insert(0);

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
      // for the query: add a negation of the entire non-recursive part:
      if (hr.isQuery)
      {
        Expr massaged = propagateEqualities(body);
        massaged = unfoldITE(mkNeg(massaged));
        massaged = convertToGEandGT(massaged);
        populateArityAndTemplates(massaged);
      }
      else
      {
        // for others: the entire non-recursive part
        ExprSet lin;
        getConj(body, lin);
        for (auto &cnj : lin)
        {
          // GF: todo: make sure all constants in the code are Ints (otherwise, z3 could be unpredictable)
          Expr massaged = unfoldITE(cnj);
          massaged = convertToGEandGT(massaged);
          populateArityAndTemplates(massaged);
        }
      }
    }
  };
}

#endif
