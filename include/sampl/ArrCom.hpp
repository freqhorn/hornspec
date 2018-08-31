#ifndef ARRCOM__HPP__
#define ARRCOM__HPP__

#include "deep/Distribution.hpp"
#include "ae/ExprSimpl.hpp"
#include "LinCom.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  class ARRfactory
  {
    private:

    ExprFactory &m_efac;
    ExprVector vars;
    ExprVector forall_args;
    LAfactory preFac;
    LAfactory postFac;
    Expr pre;

    public:

    ARRfactory(ExprFactory &_efac, bool _false) :
        m_efac(_efac), preFac(_efac, false), postFac(_efac, false) {};

    void addVar(Expr var)
    {
      vars.push_back(var); // currently, not used. TODO: at least some sanity checks later
    }

    void initializeLAfactory (LAfactory& lf, ExprSet& cands, ExprVector& intVars, int eps)
    {
      set<int> arrConsts;
      set<int> arrCoefs;

      for (auto & a : cands)
      {
        if (getLinCombCoefs(a, arrCoefs))
        {
          getLinCombConsts(a, arrConsts);
        }
      }

      for (auto & a : intVars) lf.addVar(a);
      for (auto & a : arrConsts) lf.addConst(a);
      for (auto & a : arrCoefs) lf.addIntCoef(a);

      lf.initialize();
      set<int> orArities;
      orArities.insert(1);                     // hardcode for now
      lf.initDensities(orArities);

      for (auto & a : cands)
      {
        LAdisj b;
        lf.exprToLAdisj(a, b);
        lf.calculateStatistics(b, 1, 0, 0);    // hardcode for now
      }
      lf.stabilizeDensities(1, eps, 1);        // hardcode for now
    }

    void initialize(ExprVector& intVars, ExprSet& arrCands, ExprSet& arrSelects, ExprSet& arrRange)
    {
      for (auto & a : arrSelects)
      {
        postFac.addVar(a);
        if (find(preFac.getVars().begin(),
            preFac.getVars().end(), a->right()) == preFac.getVars().end())
        {
          postFac.addVar(a->right());
          preFac.addVar(a->right());
          forall_args.push_back(a->right()->left());
        }
      }

      pre = mk<TRUE>(m_efac);
      for (auto & a : arrRange)
      {
        if (!emptyIntersect(a, preFac.getVars()))
          pre = mk<AND>(pre, a);
      }

      initializeLAfactory(preFac, arrRange, intVars, 1);
      initializeLAfactory(postFac, arrCands, intVars, 0);
    }
    
    Expr guessTerm ()
    {
      LAdisj expr1;
      LAdisj expr2;
      // GF: fixed guesses, currently
      // TODO: 1) pruning based on dependencies of pre and expr1,
      //       2) pruning based on dependencies of expr1 and expr2,
      //       3) conjunctive and disjunctive expr1 and expr2
      if (preFac.guessTerm(expr1, 1) && postFac.guessTerm(expr2, 1))
      {
        ExprVector args = forall_args;
        args.push_back(mk<IMPL>(mk<AND>(pre, preFac.toExpr(expr1)), postFac.toExpr(expr2)));
        Expr forallExpr = mknary<FORALL> (args);
        return forallExpr;
      }
      else
      {
        return NULL;
      }
    }

    Expr guessSimplTerm ()
    {
      LAdisj expr2;
      if (postFac.guessTerm(expr2, 1))
      {
        ExprVector args = forall_args;
        args.push_back(mk<IMPL>(pre, postFac.toExpr(expr2)));
        Expr forallExpr = mknary<FORALL> (args);
        return forallExpr;
      }
      else
      {
        return NULL;
      }
    }
  };
}


#endif
