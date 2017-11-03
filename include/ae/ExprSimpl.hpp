#ifndef EXPRSIMPL__HPP__
#define EXPRSIMPL__HPP__
#include <assert.h>

#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{
  template<typename Range> static Expr conjoin(Range& conjs, ExprFactory &efac){
    return
    (conjs.size() == 0) ? mk<TRUE>(efac) :
    (conjs.size() == 1) ? *conjs.begin() :
    mknary<AND>(conjs);
  }

  template<typename Range> static Expr disjoin(Range& disjs, ExprFactory &efac){
    return
    (disjs.size() == 0) ? mk<FALSE>(efac) :
    (disjs.size() == 1) ? *disjs.begin() :
    mknary<OR>(disjs);
  }

  template<typename Range> static Expr mkplus(Range& terms, ExprFactory &efac){
    return
    (terms.size() == 0) ? mkTerm (mpz_class (0), efac) :
    (terms.size() == 1) ? *terms.begin() :
    mknary<PLUS>(terms);
  }

  template<typename Range> static Expr mkmult(Range& terms, ExprFactory &efac){
    return
    (terms.size() == 0) ? mkTerm (mpz_class (1), efac) :
    (terms.size() == 1) ? *terms.begin() :
    mknary<MULT>(terms);
  }

  template<typename Range1, typename Range2> static bool emptyIntersect(Range1& av, Range2& bv){
    for (auto &var1: av){
      for (auto &var2: bv) if (var1 == var2) return false;
    }
    return true;
  }

  template<typename Range> static bool emptyIntersect(Expr a, Range& bv){
    ExprVector av;
    filter (a, bind::IsConst (), inserter(av, av.begin()));
    return emptyIntersect(av, bv);
  }

  inline static bool emptyIntersect(Expr a, Expr b){
    ExprVector bv;
    filter (b, bind::IsConst (), inserter(bv, bv.begin()));
    return emptyIntersect(a, bv);
  }

  inline static void getConj (Expr a, ExprSet &conjs)
  {
    if (isOpX<TRUE>(a)) return;
    if (isOpX<FALSE>(a)){
      conjs.clear();
      return;
    } else if (isOpX<AND>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getConj(a->arg(i), conjs);
      }
    } else {
      conjs.insert(a);
    }
  }

  inline static void getDisj (Expr a, ExprSet &disjs)
  {
    if (isOpX<FALSE>(a)) return;
    if (isOpX<TRUE>(a)){
      disjs.clear();
      return;
    } else if (isOpX<OR>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getDisj(a->arg(i), disjs);
      }
    } else {
      disjs.insert(a);
    }
  }

  /**
   * Represent Expr as multiplication
   */
  inline static Expr mult(Expr e){
    if (isOpX<MULT>(e)){
      return e;
    } else {
      return mk<MULT>(e, mkTerm (mpz_class (1), e->getFactory()));
    }
  }
  
  /**
   * Represent Zero as multiplication
   */
  inline static Expr multZero(Expr e, Expr multiplier){
    if (lexical_cast<string>(e) == "0")
      return mk<MULT>(multiplier, e);
    else return e;
  }
  
  /**
   * Rewrites distributivity rule:
   * a*b + a*c -> a*(b + c)
   * (assume, all common multipliers might be only in the first place)
   */
  inline static Expr exprDistributor(Expr e){
    if (e->arity () == 0) return e;
    Expr multiplier = mult(e->arg(0));
    ExprSet newE;
    newE.insert(multiplier->right());
    multiplier = multiplier->left();
    
    for (unsigned i = 1; i < e->arity (); i++){
      Expr a = mult(e->arg(i));
      if (isOpX<MULT>(a)){
        if (a->left() == multiplier){
          newE.insert(a->right());
        } else {
          return e;
        }
      } else {
        return e;
      }
    }
    if (isOpX<PLUS>(e)){
      return mk<MULT>(multiplier, mknary<PLUS>(newE));
    }
    return e;
  }
  
  /**
   * Self explanatory
   */
  inline static bool isConstOrItsAdditiveInverse(Expr e, Expr var){
    if (e == var) {
      return true;
    }
    if (isOpX<MULT>(e)){
      if (lexical_cast<string>(e->left()) == "-1" && e->right() == var){
        return true;
      }
    }
    
    return false;
  }
  
  /**
   * Self explanatory
   */
  inline static Expr additiveInverse(Expr e){

    if (isOpX<UN_MINUS>(e)){
      return e->left();
    }
    else if (isOpX<MPQ>(e)){
      string val = lexical_cast<string>(e);
      int delim = val.find("/");
      int val1 = stoi(val.substr(0, delim));
      int val2 = stoi(val.substr(delim + 1));
      if (delim < 0) {
        return mkTerm (mpq_class (-val1), e->getFactory());
      } else {
        string inv_val = to_string(-val1) + "/" + to_string(val2);
        return mkTerm (mpq_class (inv_val), e->getFactory());
      }
    }
    else if (isOpX<MPZ>(e)){
      int val = lexical_cast<int>(e);
      return mkTerm (mpz_class (-val), e->getFactory());
    }
    else if (isOpX<MULT>(e)){
      if (lexical_cast<string>(e->left()) == "-1"){
        return e->right();
      } else if (e->arity() == 2) {
        Expr c = additiveInverse(e->left());
        return mk<MULT>(c, e->right());
      }
    }
    return mk<MULT>(mkTerm (mpq_class (-1), e->getFactory()), e);
  }
  
  /**
   * Commutativity in Addition
   */
  inline static Expr exprSorted(Expr e){
    Expr res = e;
    if (isOpX<PLUS>(e)) {
      ExprSet expClauses;
      for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it){
        expClauses.insert(*it);
      }
      res = mknary<PLUS>(expClauses);
    }
    
    if (isOpX<MULT>(e)) {
      if (lexical_cast<string>(e->left())  == "-1"){
        Expr l = e->right();
        
        if (isOpX<PLUS>(l)) {
          ExprSet expClauses;
          for (auto it = l->args_begin(), end = l->args_end(); it != end; ++it){
            expClauses.insert(additiveInverse(*it));
          }
          res = mknary<PLUS>(expClauses);
        }
      }
    }
    
    return res;
  }
  
  /**
   * Helper used in ineqReverter
   */
  template <typename T> static Expr rewriteHelperN(Expr e){
    assert(e->arity() == 2);
    
    if (!isOpX<UN_MINUS>(e->left()) &&
        !(isOpX<MULT>(e->left())))
    {
      if (lexical_cast<string>(e->left()->left()) == "-1")  return e;
    }

    return mk<T>(additiveInverse(e->left()), additiveInverse(exprDistributor(e->right())));
  }
  
  /**
   *  Helper used in ineqMover
   */
  template <typename T> static Expr rewriteHelperM(Expr e, Expr var){
    Expr l = e->left();
    Expr r = e->right();
    ExprVector lhs;  // expressions containing var
    ExprVector rhs;  // the rest of e
    
    // first, parse l;
    
    if (isOpX<PLUS>(l)){
      for (unsigned i = 0; i < l->arity (); i++){
        Expr a = l->arg(i);
        if (isConstOrItsAdditiveInverse(a, var)){
          lhs.push_back(a);
        } else {
          rhs.push_back(additiveInverse(a));
        }
      }
    } else if (isOpX<MINUS>(l)){
      if (isConstOrItsAdditiveInverse(l->left(), var)){
        lhs.push_back(l->left());
      } else {
        rhs.push_back(additiveInverse(l->left()));
      }
      if (isConstOrItsAdditiveInverse(l->right(), var)){
        lhs.push_back(additiveInverse(l->right()));
      } else {
        rhs.push_back(l);
      }
    } else {
      if (isConstOrItsAdditiveInverse(l, var)){
        lhs.push_back(l);
      } else if (lexical_cast<string>(l) != "0"){
        rhs.push_back(additiveInverse(l));
      }
    }
    
    // second, parse r;
    
    if (isOpX<PLUS>(r)){
      for (unsigned i = 0; i < r->arity (); i++){
        Expr a = r->arg(i);
        if (isConstOrItsAdditiveInverse(a, var)){
          lhs.push_back(additiveInverse(a));
        } else {
          rhs.push_back(a);
        }
      }
    } else if (isOpX<MINUS>(r)){
      if (isConstOrItsAdditiveInverse(r->left(), var)){
        lhs.push_back(additiveInverse(r->left()));
      } else {
        rhs.push_back(r->left());
      }
      if (isConstOrItsAdditiveInverse(r->right(), var)){
        lhs.push_back(r->right());
      } else {
        rhs.push_back(r->right());
      }
    } else {
      if (isConstOrItsAdditiveInverse(r, var)){
        lhs.push_back(additiveInverse(r));
      } else if (lexical_cast<string>(r) != "0"){
        rhs.push_back(r);
      }
    }
    
    // third, combine results;
    
    int coef = 0;
    for (auto &a : lhs)
    {
      if (a == var) coef++;
      if (a == additiveInverse(var)) coef--;
    }

    r = mkplus(rhs, e->getFactory());

    if (coef == 0){
      l = mkTerm (mpz_class (0), e->getFactory());
    } else if (coef == 1){
      l = var;
    } else {
      l = mk<MULT>(mkTerm (mpz_class (coef), e->getFactory()), var);
    }

    return mk<T>(l,r);
  }
  
  /**
   * Helper used in exprMover
   */
  template <typename T> static Expr rewriteHelperE(Expr e, Expr var){
    //todo: debug: clean = false -> shared_ptr.hpp:418: Assertion `px != 0' failed
    assert(e->arity() == 2);
    Expr l = e->left();
    Expr r = e->right();
    if (r == var) {
      l = exprSorted(l);
      return mk<T>(r, l);
    }
    
    if (isOpX<MULT>(r)){
      if (r->left() == var || r->right() == var){
        l = exprSorted(l);
        return mk<T>(r, l);
      }
    }
    return e;
  }
  
  /**
   *  Merge adjacent inequalities
   *  (a <= b && a >= b) -> (a == b)
   */
  inline static void ineqMerger(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<LEQ>(e)){
        for (auto &e2: expClauses){
          if (isOpX<GEQ>(e2)){
            if (e->left() == e2->left()){
              Expr e1r = exprSorted(e->right());
              Expr e2r = exprSorted(e2->right());
              if ( e1r == e2r ){
                if (clean){
                  expClauses.erase(e);
                  expClauses.erase(e2);
                }
                expClauses.insert(mk<EQ>(e->left(), e1r));
              }
            }
          }
        }
      }
    }
  }
  
  /**
   *  Merge adjacent inequalities
   *  (a <= b && b <= a) -> (a == b)
   */
  template <typename T> static void ineqMergerSwap(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<T>(e)){
        for (auto &e2: expClauses){
          if (isOpX<T>(e2)){
            if (e->left() == e2->right() && e->right() == e2->left()){
              if (clean){
                expClauses.erase(e);
                expClauses.erase(e2);
              }
              expClauses.insert(mk<EQ>(e->left(), e->right()));
            }
          }
        }
      }
    }
  }
  
  /**
   *  Merge adjacent inequalities
   *  (a <= 0 && -a <= 0) -> (a == 0)
   *  (a >= 0 && -a >= 0) -> (a == 0)
   */
  template <typename T> static void ineqMergerSwapMinus(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<T>(e)){
        for (auto &e2: expClauses){
          if (isOpX<T>(e2)){
            if (e->right() == e2->right() && e2->right() == mkTerm (mpz_class (0), e2->getFactory())){
              Expr l1 = exprSorted(additiveInverse(e->left()));
              Expr l2 = exprSorted(e2->left());
              if (l1 == l2){
                if (clean){
                  expClauses.erase(e);
                  expClauses.erase(e2);
                }
                expClauses.insert(mk<EQ>(e->left(), e->right()));
              }
            }
          }
        }
      }
    }
  }
  
  /**
   *  Trivial simplifier:
   *  (-1*a <= -1*b) -> (a >= b)
   *  (-1*a >= -1*b) -> (a <= b)
   *  (-1*a == -1*b) -> (a == b)
   */
  inline static Expr ineqReverter(Expr e){
      if (isOpX<LEQ>(e)){
        return rewriteHelperN<GEQ>(e);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperN<LEQ>(e);
      } else if (isOpX<LT>(e)){
        return rewriteHelperN<GT>(e);
      } else if (isOpX<GT>(e)){
        return rewriteHelperN<LT>(e);
      } else if (isOpX<EQ>(e)){
        return rewriteHelperN<EQ>(e);
      } else if (isOpX<NEQ>(e)){
        return rewriteHelperN<NEQ>(e);
      }
    return e;
  }
  
  inline static Expr ineqNegReverter(Expr a){
    if (isOpX<NEG>(a)){
      Expr e = a->arg(0);
      if (isOpX<LEQ>(e)){
        return mk<GT>(e->arg(0), e->arg(1));
      } else if (isOpX<GEQ>(e)){
        return mk<LT>(e->arg(0), e->arg(1));
      } else if (isOpX<LT>(e)){
        return mk<GEQ>(e->arg(0), e->arg(1));
      } else if (isOpX<GT>(e)){
        return mk<LEQ>(e->arg(0), e->arg(1));
      } else if (isOpX<NEQ>(e)){
        return mk<EQ>(e->arg(0), e->arg(1));
      } else if (isOpX<EQ>(e)){
        return mk<NEQ>(e->arg(0), e->arg(1));
      }
    }
    return a;
  }
  
  /**
   *  Transform the inequalities by the following rules:
   *  (a + .. + var + .. + b <= c ) -> (var <= -1*a + .. + -1*b + c)
   *  (a + .. + -1*var + .. + b <= c) -> (-1*var <= -1*a + .. + -1*b + c )
   *  (a <= b + .. + var + .. + c) -> (-1*var <= (-1)*a + b + .. + c)
   *  (a <= b + .. + (-1)*var + .. + c) -> (var <= (-1)*a + b + .. + c)
   *
   *  same for >=
   */
  inline static Expr ineqMover(Expr e, Expr var){
      if (isOpX<LEQ>(e)){
        return rewriteHelperM<LEQ>(e, var);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperM<GEQ>(e, var);
      } else if (isOpX<LT>(e)){
        return rewriteHelperM<LT>(e, var);
      } else if (isOpX<GT>(e)){
        return rewriteHelperM<GT>(e, var);
      } else if (isOpX<EQ>(e)){
        return rewriteHelperM<EQ>(e, var);
      } else if (isOpX<NEQ>(e)){
        return rewriteHelperM<NEQ>(e, var);
      }
    return e;
  }
  
  /**
   *  Move "var" to the left hand side of expression:
   *  (a <= var) -> (var >= b)
   *  (a >= var) -> (var <= b)
   *  (a == var) -> (var == b)
   */
  inline static Expr exprMover(Expr e, Expr var){
      if (isOpX<LEQ>(e)){
        return rewriteHelperE<GEQ>(e, var);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperE<LEQ>(e, var);
      } if (isOpX<EQ>(e)){
        return rewriteHelperE<EQ>(e, var);
      } if (isOpX<NEG>(e)){
        return mk<NEG>(exprMover(e->arg(0), var));
      }
    return e;
  }
  
  /**
   *
   */
  inline static Expr eqDiffMover(Expr e){
    if(isOpX<EQ>(e)){
      if (isOpX<MINUS>(e->left()) && e->left()->arity() == 2 && lexical_cast<string>(e->right()) == "0"){
        return mk<EQ>(e->left()->left(), e->left()->right());
      }
    }
    return e;
  }
  
  /**
   * Search for an equality
   */
  inline static bool equalitySearch(ExprSet& expClauses, Expr var){
    for (auto &e: expClauses){
      if (isOpX<EQ>(e)){
        Expr l = e->left();
        Expr r = e->right();
        if (l == var || r == var){
          ExprSet singleton;
          singleton.insert(e);
          expClauses = singleton;
          return true;
        }
      }
    }
    return false;
  }
  
  /**
   * Simplifier Wrapper
   */
  inline static Expr ineqSimplifier(Expr v, Expr exp){
    ExprSet substsMap;
    if (isOpX<AND>(exp)){
      for (ENode::args_iterator it = exp->args_begin(), end = exp->args_end();
           it != end; ++it){
        Expr cl = *it;
        cl = exprMover(*it, v);
        cl = ineqMover(cl, v);
        cl = ineqReverter (cl);
        substsMap.insert(cl);
      }
      
      ineqMerger(substsMap);
      equalitySearch(substsMap, v);
      return conjoin(substsMap, v->getFactory());
      
    }
    return exp;
  }
  
  
  template<typename T>
  struct RW
  {
    std::shared_ptr<T> _r;
    
    RW (std::shared_ptr<T> r) : _r(r) {}
    RW (T *r) : _r (r) {}
    
    
    VisitAction operator() (Expr exp)
    {
      // -- apply the rewriter
      if (exp->arity() == 0)
        // -- do not descend into non-boolean operators
        return VisitAction::skipKids ();
      
      return VisitAction::changeDoKidsRewrite (exp, _r);
      
    }
  };
  
  inline static Expr simplifiedPlus (Expr exp, Expr to_skip){
    ExprVector args;
    Expr ret;
    bool f = false;
    
    for (ENode::args_iterator it = exp->args_begin(),
         end = exp->args_end(); it != end; ++it){
      if (*it == to_skip) f = true;
      else args.push_back (*it);
    }

    if (f == false)
    {
      args.push_back(additiveInverse(to_skip));
    }
    
    if (args.size() == 1) {
      ret = args[0];
    }
    
    else if (args.size() == 2){
      if (isOpX<UN_MINUS>(args[0]) && !isOpX<UN_MINUS>(args[1]))
        ret = mk<MINUS>(args[1], args[0]->left());
      else if (!isOpX<UN_MINUS>(args[0]) && isOpX<UN_MINUS>(args[1]))
        ret = mk<MINUS>(args[0], args[1]->left());
      
      else ret = mknary<PLUS>(args);
      
    } else {
      ret = mknary<PLUS>(args);
    }
    return ret;
  }
  
  // return a - b
  inline static Expr simplifiedMinus (Expr a, Expr b){
    Expr ret = mk<MINUS>(a, b);
    
    if (a == b) {
      ret = mkTerm (mpz_class (0), a->getFactory());
    } else
      
      if (isOpX<PLUS>(a)){
        return simplifiedPlus(a, b);
      } else
        
        if (isOpX<PLUS>(b)){
          Expr res = simplifiedPlus(b, a);
          return mk<UN_MINUS>(res);
        } else
          
          if (isOpX<MINUS>(a)){
            if (a->left() == b) ret = mk<UN_MINUS>(a->right());
          } else
            
            if (isOpX<MINUS>(b)){
              if (a == b->right()) ret = mk<UN_MINUS>(b->left());
            } else
              
              if (isOpX<UN_MINUS>(b)) {
                if (b->left() == mkTerm (mpz_class (0), a->getFactory())) {
                  ret = a;
                } else {
                  ret = mk<PLUS>(a,b->left());
                }
              } else
                
                if (mkTerm (mpz_class (-1), a->getFactory()) == b) {
                  ret = simplifiedPlus(a, mkTerm (mpz_class (1), a->getFactory()));
                } else
                  
                  if (b == mkTerm (mpz_class (0), a->getFactory())) {
                    ret = a;
                  } else
                    
                    if (a == mkTerm (mpz_class (0), a->getFactory())){
                      if (isOpX<UN_MINUS>(b)){
                        ret = b->left();
                      }
                      else {
                        ret = mk<UN_MINUS>(b);
                      }
                    }
    
    return ret;
  }
  
  struct SimplifyArithmExpr
  {
    ExprFactory &efac;
    
    Expr zero;
    Expr one;
    Expr minus_one;
    
    SimplifyArithmExpr (ExprFactory& _efac):
    efac(_efac)
    {
      zero = mkTerm (mpz_class (0), efac);
      one = mkTerm (mpz_class (1), efac);
      minus_one = mkTerm (mpz_class (1), efac);
    };
    
    Expr operator() (Expr exp)
    {
      if (isOpX<PLUS>(exp))
      {
        return simplifiedPlus(exp, zero);
      }
      
      if (isOpX<MINUS>(exp) && exp->arity() == 2)
      {
        return simplifiedMinus(exp->left(), exp->right());
      }
      
      if (isOpX<MULT>(exp))
      {
        if (exp->left() == zero) return zero;
        if (exp->right() == zero) return zero;
        if (exp->left() == one) return exp->right();
        if (exp->right() == one) return exp->left();
        if (exp->left() == minus_one) return mk<UN_MINUS>(exp->right());
        if (exp->right() == minus_one) return mk<UN_MINUS>(exp->left());
      }
      
      if (isOpX<UN_MINUS>(exp))
      {
        Expr uneg = exp->left();
        if (uneg == zero) return zero;
        if (uneg == minus_one) return one;
        if (isOpX<UN_MINUS>(uneg)) return uneg->left();
        if (isOpX<PLUS>(uneg)){
          Expr unegl = uneg->left();
          Expr unegr = uneg->right();
          if (isOpX<UN_MINUS>(unegl)) return mk<MINUS>(unegl->left(), unegr);
          if (isOpX<UN_MINUS>(unegr)) return mk<MINUS>(unegr->left(), unegl);
        }
      }
      
      if (isOpX<MINUS>(exp))
      {
        if (isOpX<UN_MINUS>(exp->right())) return mk<PLUS>(exp->left(), exp->right()->left());
      }
      return exp;
    }
  };
  
  struct SimplifyBoolExpr
  {
    ExprFactory &efac;
    
    SimplifyBoolExpr (ExprFactory& _efac) : efac(_efac){};
    
    Expr operator() (Expr exp)
    {
      // GF: to enhance
      
      if (isOpX<IMPL>(exp))
      {
        if (isOpX<TRUE>(exp->right()))
          return mk<TRUE>(efac);

        if (isOpX<FALSE>(exp->right()))
          return mk<NEG>(exp->left());
        
        return (mk<OR>(
                 mk<NEG>(exp->left()),
                 exp->right()));
      }

      if (isOpX<OR>(exp)){
        ExprSet dsjs;
        getDisj(exp, dsjs);
        for (auto & a : dsjs){
          if (isOpX<EQ>(a) && a->left() == a->right()) return mk<TRUE>(efac);
        }
        return disjoin (dsjs, exp->getFactory());
      }

      if (isOpX<AND>(exp)){
        ExprSet cnjs;
        getConj(exp, cnjs);
        return conjoin (cnjs, exp->getFactory());
      }

      return exp;
    }
  };

  inline static Expr simplifyArithm (Expr exp)
  {
    RW<SimplifyArithmExpr> rw(new SimplifyArithmExpr(exp->getFactory()));
    return dagVisit (rw, exp);
  }
  
  inline static Expr simplifyBool (Expr exp)
  {
    RW<SimplifyBoolExpr> rw(new SimplifyBoolExpr(exp->getFactory()));
    return dagVisit (rw, exp);
  }
  
  inline static ExprSet minusSets(ExprSet& v1, ExprSet& v2){
    ExprSet v3;
    bool res;
    for (auto &var1: v1){
      res = true;
      for (auto &var2: v2){
        if (var1 == var2) { res = false; break;}
      }
      if (res) v3.insert(var1);
    }
    return v3;
  }

  inline static bool isNumericConst(Expr e)
  {
    return isOpX<MPZ>(e) || isOpX<MPQ>(e);
  }
  
  template<typename Range> static int getVarIndex(Expr var, Range& vec)
  {
    int i = 0;
    for (auto &e: vec)
    {
      if (var == e) return i;
      i++;
    }
    return -1;
  }
  
  static void getAddTerm (Expr a, ExprVector &terms); // declaration only
  
  inline static Expr arithmInverse(Expr e)
  {
    bool success = true;
    if (isOpX<MULT>(e))
    {
      int coef = 1;
      Expr var = NULL;
      for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
      {
        if (isNumericConst(*it))
        {
          coef *= lexical_cast<int>(*it);
        }
        else if (bind::isIntConst(*it) && var == NULL)
        {
          var = *it;
        }
        else
        {
          success = false;
        }
      }
      if (success && coef != 0) return mk<MULT>(mkTerm (mpz_class (-coef), e->getFactory()), e->right());
      
      if (coef == 0) return mkTerm (mpz_class (0), e->getFactory());
    }
    else if (isOpX<PLUS>(e))
    {
      ExprVector terms;
      for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
      {
        getAddTerm(arithmInverse(*it), terms);
      }
      return mknary<PLUS>(terms);
    }
    else if (isOpX<MINUS>(e))
    {
      ExprVector terms;
      getAddTerm(arithmInverse(*e->args_begin ()), terms);
      auto it = e->args_begin () + 1;
      for (auto end = e->args_end (); it != end; ++it)
      {
        getAddTerm(*it, terms);
      }
      return mknary<PLUS>(terms);
    }
    else if (isOpX<UN_MINUS>(e))
    {
      return e->left();
    }
    else if (isNumericConst(e))
    {
      return mkTerm (mpz_class (-lexical_cast<int>(e)), e->getFactory());
    }
    return mk<MULT>(mkTerm (mpz_class (-1), e->getFactory()), e);
  }
  
  inline static void getAddTerm (Expr a, ExprVector &terms) // implementation (mutually recursive)
  {
    if (isOpX<PLUS>(a))
    {
      for (auto it = a->args_begin (), end = a->args_end (); it != end; ++it)
      {
        getAddTerm(*it, terms);
      }
    }
    else if (isOpX<MINUS>(a))
    {
      auto it = a->args_begin ();
      auto end = a->args_end ();
      getAddTerm(*it, terms);
//      outs () <<"   [   " << *(*it) << "\n";
      ++it;
      for (; it != end; ++it)
      {
//        outs () << *mk<UN_MINUS>(*it) << "   ]   \n";
        getAddTerm(arithmInverse(*it), terms);
      }
    }
    else
    {
      terms.push_back(a);
    }
  }
  
  struct AddMultDistr
  {
    AddMultDistr () {};
    
    Expr operator() (Expr exp)
    {
      if (isOpX<MULT>(exp))
      {
        Expr lhs = exp->left();
        Expr rhs = exp->right();
        
        ExprVector alllhs;
        getAddTerm(lhs, alllhs);
        
        ExprVector allrhs;
        getAddTerm(rhs, allrhs);
        
        ExprVector unf;
        for (auto &a : alllhs)
        {
          for (auto &b : allrhs)
          {
            unf.push_back(mk<MULT>(a, b));
          }
        }
        return mkplus(unf, exp->getFactory());
      }
      
      return exp;
    }
  };
  
  inline static Expr rewriteMultAdd (Expr exp)
  {
    RW<AddMultDistr> mu(new AddMultDistr());
    return dagVisit (mu, exp);
  }
  
  struct FindNonlinAndRewrite
  {
    ExprVector& vars;
    ExprVector& vars2;
    ExprMap& extraVars;
    
    FindNonlinAndRewrite (ExprVector& _vars, ExprVector& _vars2, ExprMap& _extraVars) :
      vars(_vars), vars2(_vars2), extraVars(_extraVars) {};
    
    Expr operator() (Expr t)
    {
      if (isOpX<MULT>(t))
      {
        ExprVector varsForMult;
        Expr multedConsts;
        for (unsigned j = 0; j < t->arity(); j++)
        {
          Expr q = t->arg(j);
          if (bind::isIntConst(q))
          {
            int ind = getVarIndex(q, vars);
            if (ind == -1) return t;
            varsForMult.push_back(vars2[ind]);
          }
          else
          {
            // GF: to ensure that it is indeed const
            multedConsts = (multedConsts == NULL) ? q : mk<MULT>(multedConsts, q);
          }
        }
        if (varsForMult.size() > 1)
        {
          Expr multedVars = mknary<MULT>(varsForMult);
          if (extraVars[multedVars] == NULL)
          {
            Expr new_name = mkTerm<string> ("__e__" + to_string(extraVars.size()), t->getFactory());
            Expr var = bind::intConst(new_name);
            extraVars[multedVars] = var;
          }
          return (multedConsts == NULL) ? extraVars[multedVars] : mk<MULT>(multedConsts, extraVars[multedVars]);
        }
      }
      else if (isOpX<MOD>(t) || isOpX<IDIV>(t) || isOpX<DIV>(t))
      {
        int indl = getVarIndex(t->left(), vars);
        int indr = getVarIndex(t->right(), vars);

        Expr key = t;
        if (indl >= 0) key = replaceAll(key, t->left(), vars2[indl]);
        if (indr >= 0) key = replaceAll(key, t->right(), vars2[indr]);

        if (extraVars[key] == NULL)
        {
          Expr new_name = mkTerm<string> ("__e__" + to_string(extraVars.size()), t->getFactory());
          Expr var = bind::intConst(new_name);
          extraVars[key] = var;
        }
        return extraVars[key];
      }
      return t;
    }
  };

  inline static Expr findNonlinAndRewrite (Expr exp, ExprVector& vars, ExprVector& vars2, ExprMap& extraVars)
  {
    RW<FindNonlinAndRewrite> mu(new FindNonlinAndRewrite(vars, vars2, extraVars));
    return dagVisit (mu, exp);
  }

  struct FindNonlin : public std::unary_function<Expr, VisitAction>
  {
    bool found;

    FindNonlin () : found (false) {}

    VisitAction operator() (Expr exp)
    {
      if (found)
      {
        found = true;
        return VisitAction::skipKids ();
      }
      else if (isOpX<MULT>(exp) || isOpX<MOD>(exp) || isOpX<DIV>(exp) || isOpX<IDIV>(exp))
      {
        int v = 0;
        for (unsigned j = 0; j < exp->arity(); j++)
        {
          Expr q = exp->arg(j);
          if (bind::isIntConst(q)) v++;     // GF: a simple counter, to extend
        }

        if (v > 1)
        {
          found = true;
          return VisitAction::skipKids ();
        }
      }
      return VisitAction::doKids ();
    }
  };

  inline bool findNonlin (Expr e1)
  {
    FindNonlin fn;
    dagVisit (fn, e1);
    return fn.found;
  }
  
  inline Expr convertToGEandGT(Expr term)
  {   
    if (isOpX<LT>(term)) return mk<GT>(term->right(), term->left());
    
    if (isOpX<LEQ>(term)) return mk<GEQ>(term->right(), term->left());
    
    if (isOpX<EQ>(term)) return mk<AND>(
                  mk<GEQ>(term->left(), term->right()),
                  mk<GEQ>(term->right(), term->left()));
    
    if (isOpX<NEQ>(term)) return mk<OR>(
                  mk<GT>(term->left(), term->right()),
                  mk<GT>(term->right(), term->left()));
    
    if (isOpX<NEG>(term))
    {
      return mk<NEG>(convertToGEandGT(term->last()));
    }
    
    if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(convertToGEandGT(term->arg(i)));
      }
      
      return isOpX<AND>(term) ? conjoin (args, term->getFactory()) :
                  disjoin (args, term->getFactory());
      
    }
    return term;
  }
  
  inline static Expr simplifiedAnd (Expr a, Expr b){
    ExprSet conjs;
    getConj(a, conjs);
    getConj(b, conjs);
    return
    (conjs.size() == 0) ? mk<TRUE>(a->getFactory()) :
    (conjs.size() == 1) ? *conjs.begin() :
    mknary<AND>(conjs);
  }

  inline int intersectSize(ExprVector& a, ExprVector& b){
    ExprSet c;
    for (auto &var: a)
      if (find(b.begin(), b.end(), var) != b.end()) c.insert(var);
    return c.size();
  }

  inline static Expr simplifyArithmDisjunctions(Expr term);

  inline static void productAnd (ExprSet& as, ExprSet& bs, ExprSet& ps)
  {
    for (auto &a : as)
    {
      for (auto &b : bs)
      {
        Expr orredExpr = simplifyArithmDisjunctions(mk<OR>(a, b));
        if (!isOpX<TRUE>(orredExpr))
          ps.insert(orredExpr);
      }
    }
  }

  // ab \/ cde \/ f =>
  //                    (a \/ c \/ f) /\ (a \/ d \/ f) /\ (a \/ e \/ f) /\
  //                    (b \/ c \/ f) /\ (b \/ d \/ f) /\ (b \/ e \/ f)
  inline static Expr rewriteOrAnd(Expr exp)
  {
    ExprSet disjs;
    getDisj(exp, disjs);
    if (disjs.size() == 1) return exp;
    
    vector<ExprSet> dconjs;
    for (auto &a : disjs)
    {
      ExprSet conjs;
      getConj(a, conjs);
      dconjs.push_back(conjs);
    }
    
    ExprSet older;
    productAnd(dconjs[0], dconjs[1], older);
    
    ExprSet newer = older;
    for (int i = 2; i < disjs.size(); i++)
    {
      newer.clear();
      productAnd(dconjs[i], older, newer);
      older = newer;
    }
    return conjoin (newer, exp->getFactory());
  }

  inline static Expr cloneVar(Expr var, Expr new_name) // ... and give a new_name to the clone
  {
    if (bind::isIntConst(var))
      return bind::intConst(new_name);
    else if (bind::isRealConst(var))
      return bind::realConst(new_name);
    else if (bind::isBoolConst(var))
      return bind::boolConst(new_name);

    else return NULL;
  }

  // not very pretty method, but..
  inline static Expr reBuildCmp(Expr term, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(term))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(term))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(term))
    {
      return mk<LEQ>(lhs, rhs);
    }
    if (isOpX<GEQ>(term))
    {
      return mk<GEQ>(lhs, rhs);
    }
    if (isOpX<LT>(term))
    {
      return mk<LT>(lhs, rhs);
    }
    assert(isOpX<GT>(term));
    return mk<GT>(lhs, rhs);
  }
  
  inline static Expr reBuildNegCmp(Expr term, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(term))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(term))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(term))
    {
      return mk<GT>(lhs, rhs);
    }
    if (isOpX<GEQ>(term))
    {
      return mk<LT>(lhs, rhs);
    }
    if (isOpX<LT>(term))
    {
      return mk<GEQ>(lhs, rhs);
    }
    assert(isOpX<GT>(term));
    return mk<LEQ>(lhs, rhs);
  }
  
  // not very pretty method, but..
  inline static bool evaluateCmpConsts(Expr term, int a, int b)
  {
    if (isOpX<EQ>(term))
    {
      return (a == b);
    }
    if (isOpX<NEQ>(term))
    {
      return (a != b);
    }
    if (isOpX<LEQ>(term))
    {
      return (a <= b);
    }
    if (isOpX<GEQ>(term))
    {
      return (a >= b);
    }
    if (isOpX<LT>(term))
    {
      return (a < b);
    }
    assert(isOpX<GT>(term));
    return (a > b);
  }
  
  inline static Expr mkNeg(Expr term)
  {
    if (isOpX<NEG>(term))
    {
      return term->arg(0);
    }
    else if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(mkNeg(term->arg(i)));
      }
      return isOpX<AND>(term) ? disjoin(args, term->getFactory()) :
                                conjoin (args, term->getFactory());
    }
    else if (isOp<ComparissonOp>(term))
    {
      return reBuildNegCmp(term, term->arg(0), term->arg(1));
    }
    return mk<NEG>(term);
  }

  inline static Expr unfoldITE(Expr term)
  {
    if (isOpX<ITE>(term))
    {
      Expr iteCond = unfoldITE (term->arg(0));
      Expr iteC1 = unfoldITE (term->arg(1));
      Expr iteC2 = unfoldITE (term->arg(2));
      
      return mk<OR>( mk<AND>(iteCond, iteC1),
                    mk<AND>(mkNeg(iteCond), iteC2));
    }
    else if (isOpX<NEG>(term))
    {
      return mkNeg(unfoldITE(term->last()));
    }
    else if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(unfoldITE(term->arg(i)));
      }
      return isOpX<AND>(term) ? conjoin (args, term->getFactory()) :
                                disjoin (args, term->getFactory());
    }
    else if (isOp<ComparissonOp>(term))
    {
      Expr lhs = term->arg(0);
      Expr rhs = term->arg(1);
      
      if (isOpX<ITE>(rhs))
      {
        
        Expr iteCond = unfoldITE (rhs->arg(0));
        Expr iteC1 = rhs->arg(1);
        Expr iteC2 = rhs->arg(2);
        
        Expr newCmp1 = unfoldITE (reBuildCmp(term, lhs, iteC1));
        Expr newCmp2 = unfoldITE (reBuildCmp(term, lhs, iteC2));
        
        Expr transformed = mk<OR>( mk<AND>(iteCond, newCmp1),
                                  mk<AND>(mkNeg(iteCond), newCmp2));
        
        //          outs () << "     [1b] ---> " << *term << "\n";
        //          outs () << "     [1e] ---> " << *transformed << "\n\n";
        return transformed;
        
      }
      else if (isOpX<ITE>(lhs))
      {
        // GF: symmetric case to the one above
        
        Expr iteCond = unfoldITE (lhs->arg(0));
        Expr iteC1 = lhs->arg(1);
        Expr iteC2 = lhs->arg(2);
        
        Expr newCmp1 = unfoldITE (reBuildCmp(term, iteC1, rhs));
        Expr newCmp2 = unfoldITE (reBuildCmp(term, iteC2, rhs));
        
        Expr transformed = mk<OR>( mk<AND>(iteCond, newCmp1),
                                  mk<AND>(mkNeg(iteCond), newCmp2));
        
        //          outs () << "    [2b] ---> " << *term << "\n";
        //          outs () << "    [2e] ---> " << *transformed << "\n\n";
        return transformed;
      }
      else if (isOpX<PLUS>(rhs))
      {
        bool found = false;
        Expr iteArg;
        ExprVector newArgs;
        for (auto it = rhs->args_begin(), end = rhs->args_end(); it != end; ++it)
        {
          // make sure that only one ITE is found
          
          if (!found && isOpX<ITE>(*it))
          {
            found = true;
            iteArg = *it;
          }
          else
          {
            newArgs.push_back(*it);
          }
        }
        if (found)
        {
          Expr iteCond = unfoldITE (iteArg->arg(0));
          Expr iteC1 = iteArg->arg(1);
          Expr iteC2 = iteArg->arg(2);
          
          newArgs.push_back(iteC1);
          Expr e1 = unfoldITE (reBuildCmp(term, lhs, mknary<PLUS>(newArgs))); // GF: "unfoldITE" gives error...
          
          newArgs.pop_back();
          newArgs.push_back(iteC2);
          Expr e2 = unfoldITE (reBuildCmp(term, lhs, mknary<PLUS>(newArgs)));
          
          Expr transformed = mk<OR>(mk<AND>(iteCond, e1),
                                    mk<AND>(mkNeg(iteCond),e2));
          
          //            outs () << "    [3b] ---> " << *term << "\n";
          //            outs () << "    [3e] ---> " << *transformed << "\n\n";
          
          return transformed;
        }
      }
      else if (isOpX<PLUS>(lhs))
      {
        // symmetric to the above case
        bool found = false;
        Expr iteArg;
        ExprVector newArgs;
        for (auto it = lhs->args_begin(), end = lhs->args_end(); it != end; ++it)
        {
          if (!found && isOpX<ITE>(*it))
          {
            found = true;
            iteArg = *it;
          }
          else
          {
            newArgs.push_back(*it);
          }
        }
        
        if (found)
        {
          Expr iteCond = unfoldITE (iteArg->arg(0));
          Expr iteC1 = iteArg->arg(1);
          Expr iteC2 = iteArg->arg(2);
          
          newArgs.push_back(iteC1);
          Expr e1 = unfoldITE (reBuildCmp(term, mknary<PLUS>(newArgs), rhs));
          
          newArgs.pop_back();
          newArgs.push_back(iteC2);
          Expr e2 = unfoldITE (reBuildCmp(term, mknary<PLUS>(newArgs), rhs));
          
          Expr transformed = mk<OR>(mk<AND>(iteCond,e1),
                                    mk<AND>(mkNeg(iteCond),e2));
          
          //            outs () << "    [4b] ---> " << *term << "\n";
          //            outs () << "    [4e] ---> " << *transformed << "\n\n";
          
          return transformed;
        }
      }
    }
    
    return term;
  }
  
  struct MoveInsideITEr
  {
    MoveInsideITEr () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<MOD>(exp))
      {
        Expr ite = exp->arg(0);
        if (isOpX<ITE>(ite))
        {
          return mk<ITE>(ite->arg(0),
                         mk<MOD>(ite->arg(1), exp->arg(1)),
                         mk<MOD>(ite->arg(2), exp->arg(1)));
        }
      }
      if (isOpX<MULT>(exp))
      {
        ExprVector args;
        Expr ite;
        for (auto it = exp->args_begin(), end = exp->args_end(); it != end; ++it)
        {
          if (isOpX<ITE>(*it))
          {
            if (ite != NULL) return exp;
            ite = *it;
          }
          else
          {
            args.push_back(*it);
          }
        }

        if (ite == NULL) return exp;

        Expr multiplier = mkmult (args, exp->getFactory());
        return mk<ITE>(ite->arg(0),
                       mk<MULT>(multiplier, ite->arg(1)),
                       mk<MULT>(multiplier, ite->arg(2)));
      }

      return exp;
    }
  };

  inline static Expr moveInsideITE (Expr exp)
  {
    RW<MoveInsideITEr> a(new MoveInsideITEr());
    return dagVisit (a, exp);
  }

  struct NegAndRewriter
  {
    NegAndRewriter () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<NEG>(exp) && isOpX<AND>(exp->arg(0)))
      {
        ExprSet cnjs;
        getConj(exp->arg(0), cnjs);
        ExprSet neggedCnjs;
        for (auto & c : cnjs) neggedCnjs.insert(mkNeg(c));
        return disjoin(neggedCnjs, exp->getFactory());
      }
      return exp;
    }
  };

  inline static Expr rewriteNegAnd (Expr exp)
  {
    RW<NegAndRewriter> a(new NegAndRewriter());
    return dagVisit (a, exp);
  }

  // very simple check if tautology (SMT-based check is expensive)
  inline static bool isTautology(Expr term)
  {
    if (isOpX<EQ>(term))
      if (term->arg(0) == term->arg(1)) return true;

    if (isOp<ComparissonOp>(term))
      if (isNumericConst(term->arg(0)) && isNumericConst(term->arg(1)))
        return evaluateCmpConsts(term,
                                 lexical_cast<int>(term->arg(0)), lexical_cast<int>(term->arg(1)));

    ExprSet cnjs;
    getConj(term, cnjs);
    if (cnjs.size() < 2) return false;

    bool res = true;
    for (auto &a : cnjs) res &= isTautology(a);

    return res;
  }

  inline static bool isLinearCombination(Expr term)
  {
    // an approximation of..
    if (isNumericConst(term)) {
      return false;
    }
    else if (bind::isIntConst(term)) {
      return true;
    }
    else if (isOpX<MULT>(term)) {
      bool res = false;
      for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it){
        res = res || isLinearCombination(*it);
      }
      return res;
    }
    else if (isOpX<PLUS>(term) || isOpX<MINUS>(term) || isOpX<UN_MINUS>(term)) {
      bool res = true;
      for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it){
        res = res && isLinearCombination(*it);
      }
      return res;
    }
    return false;
  }

  inline static Expr simplifyArithmDisjunctions(Expr term)
  {
    // a simple simplifier; to be enhanced

    ExprSet dsjs;
    getDisj(term, dsjs);
    if (dsjs.size() < 2) return term;

    ExprSet vars;

    // search for a var, const*var or whatever exists in any disjunct
    for (auto & d : dsjs) {
      if (isOpX<TRUE>(d)) return d;

      if (!isOp<ComparissonOp>(d)) continue;

      Expr lhs = d->arg(0);
      Expr rhs = d->arg(1);
      if (isLinearCombination(lhs)) vars.insert(lhs);
      if (isLinearCombination(rhs)) vars.insert(rhs);
    }

    if (vars.size() == 0) return term;

    for (auto &var : vars) {

      int cur_min_gt = INT_MAX; // maintain several vars
      int cur_min_ge = INT_MAX; // to avoid introducing new constants
      int cur_max_lt = INT_MIN;
      int cur_max_le = INT_MIN;

      for (auto it = dsjs.begin(); it != dsjs.end(); ) {
        auto d = *it;

        if (!isOp<ComparissonOp>(d)) { ++it; continue; }

        Expr rewritten = ineqMover(d, var);

        if (isNumericConst(rewritten->arg(0)) &&
            isNumericConst(rewritten->arg(1))) {

          if (evaluateCmpConsts(rewritten, lexical_cast<int>(rewritten->arg(0)),
                                           lexical_cast<int>(rewritten->arg(1)))){
            return mk<TRUE>(d->getFactory());
          } else {
            dsjs.erase(it++);
            continue;
          }
        }

        if (rewritten->arg(0) != var) {
          rewritten = ineqReverter(rewritten);
          if (rewritten->arg(0) != var) { ++it; continue; }
        }

        if (!isNumericConst(rewritten->arg(1))) { ++it; continue; }

        int c = lexical_cast<int>(rewritten->arg(1));

        if (isOpX<LEQ>(rewritten)) { cur_max_le = max(cur_max_le, c); }
        if (isOpX<GEQ>(rewritten)) { cur_min_ge = min(cur_min_ge, c); }
        if (isOpX<LT>(rewritten))  { cur_max_lt = max(cur_max_lt, c); }
        if (isOpX<GT>(rewritten))  { cur_min_gt = min(cur_min_gt, c); }

        if (max(cur_max_le+1, cur_max_lt) > min(cur_min_ge-1,cur_min_gt))
          return mk<TRUE>(term->getFactory());

        dsjs.erase(it++);
      }

      if (cur_min_ge != INT_MAX) {
        Expr minExpr = mk<GEQ>(var, mkTerm (mpz_class (cur_min_ge), term->getFactory()));
        dsjs.insert(minExpr);
      }
      if (cur_min_gt != INT_MAX) {
        Expr minExpr = mk<GT>(var, mkTerm (mpz_class (cur_min_gt), term->getFactory()));
        dsjs.insert(minExpr);
      }
      if (cur_max_le != INT_MIN) {
        Expr maxExpr = mk<LEQ>(var, mkTerm (mpz_class (cur_max_le), term->getFactory()));
        dsjs.insert(maxExpr);
      }
      if (cur_max_lt != INT_MIN) {
        Expr maxExpr = mk<LT>(var, mkTerm (mpz_class (cur_max_lt), term->getFactory()));
        dsjs.insert(maxExpr);
      }
    }

    return disjoin(dsjs, term->getFactory());
  }

  inline static Expr normalizeAtom(Expr term, ExprVector& intVars)
  {
    if (isOp<ComparissonOp>(term))
    {
      Expr lhs = term->left();
      Expr rhs = term->right();
      
      ExprVector all;
      ExprVector allrhs;
      
      getAddTerm(lhs, all);
      getAddTerm(rhs, allrhs);
      for (auto & a : allrhs)
      {
        all.push_back(arithmInverse(a));
      }
      
      ExprSet newlhs;
      
      for (auto &v : intVars)
      {
        int coef = 0;
        for (auto it = all.begin(); it != all.end();)
        {
          string s1 = lexical_cast<string>(v);
          string s2 = lexical_cast<string>(*it);
          
          if(s1 == s2)
          {
            coef++;
            it = all.erase(it);
          }
          else if (isOpX<UN_MINUS>(*it))
          {
            string s3 = lexical_cast<string>((*it)->left());
            if (s1 == s3)
            {
              coef--;
              it = all.erase(it);
            }
            else
            {
              ++it;
            }
          }
          else if (isOpX<MULT>(*it))
          {
            string s3 = lexical_cast<string>((*it)->left());
            string s4 = lexical_cast<string>((*it)->right());
            
            if (s1 == s3)
            {
              coef += lexical_cast<int>((*it)->right());
              it = all.erase(it);
            }
            else if (s1 == s4)
            {
              coef += lexical_cast<int>((*it)->left());
              it = all.erase(it);
            }
            else
            {
              ++it;
            }
          }
          else
          {
            ++it;
          }
        }
        if (coef != 0) newlhs.insert(mk<MULT>(mkTerm (mpz_class (coef), term->getFactory()), v));
      }
      
      bool success = true;
      int intconst = 0;
      
      for (auto &e : all)
      {
        if (isNumericConst(e))
        {
          intconst += lexical_cast<int>(e);
        }
        else if (isOpX<MULT>(e))
        {
          // GF: sometimes it fails (no idea why)
          int thisTerm = 1;
          for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
            thisTerm *= lexical_cast<int>(*it);
          
          intconst += thisTerm;
        }
        else
        {
          success = false;
        }
      }
      
      if (success && newlhs.size() == 0)
      {
        return (evaluateCmpConsts(term, 0, -intconst)) ? mk<TRUE>(term->getFactory()) :
                                                         mk<FALSE>(term->getFactory());
      }
      
      if (success)
      {
        Expr pl = (newlhs.size() == 1) ? *newlhs.begin(): mknary<PLUS>(newlhs);
        Expr c = mkTerm (mpz_class (-intconst), term->getFactory());
        return reBuildCmp(term, pl, c);
      }
    }
    return term;
  }
  
  inline static Expr normalizeDisj(Expr exp, ExprVector& intVars)
  {
    ExprSet disjs;
    ExprSet newDisjs;
    getDisj(exp, disjs);
    for (auto &d : disjs)
    {
      Expr norm = normalizeAtom(d, intVars);
      if ( isOpX<TRUE> (norm)) return norm;
      if (!isOpX<FALSE>(norm)) newDisjs.insert(norm);
    }
    return disjoin(newDisjs, exp->getFactory());
  }
  
  inline static void getLinCombCoefs(Expr ex, set<int>& intCoefs)
  {
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        getLinCombCoefs(*it, intCoefs);
      }
    else if (isOp<ComparissonOp>(ex)) // assuming the lin.combination is on the left side
    {
      Expr lhs = ex->left();
      if (isOpX<PLUS>(lhs))
      {
        for (auto it = lhs->args_begin (), end = lhs->args_end (); it != end; ++it)
        {
          if (isOpX<MULT>(*it))           // else, it is 1, and we will add it anyway;
          {
            intCoefs.insert(lexical_cast<int> ((*it)->left()));
          }
        }
      }
      else
      {
        if (isOpX<MULT>(lhs))
        {
          intCoefs.insert(lexical_cast<int> (lhs->left()));
        }
      }
    }
  }

  inline static void getLinCombConsts(Expr ex, set<int>& intConsts)
  {
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
        getLinCombConsts(*it, intConsts);
      }
    else if (isOp<ComparissonOp>(ex)) // assuming the lin.combination is on the left side
    {
      intConsts.insert(lexical_cast<int> (ex->right()));
    }
  }

  inline static bool isSymmetric (Expr exp)
  {
    return isOpX<EQ>(exp);
  }

  struct TransitionOverapprox
  {
    ExprVector& srcVars;
    ExprVector& dstVars;

    TransitionOverapprox (ExprVector& _srcVars, ExprVector& _dstVars):
    srcVars(_srcVars), dstVars(_dstVars) {};

    Expr operator() (Expr exp)
    {
      if (isOp<ComparissonOp>(exp) && !containsOp<ITE>(exp))
      {
        ExprVector av;
        filter (exp, bind::IsConst (), inserter(av, av.begin()));
        if (!emptyIntersect(av, srcVars) && !emptyIntersect(av, dstVars))
        return mk<TRUE>(exp->getFactory());
      }

      return exp;
    }
  };

  struct BoolEqRewriter
  {
    BoolEqRewriter () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<EQ>(exp))
      {
        Expr lhs = exp->left();
        Expr rhs = exp->right();
        if (bind::isBoolConst(lhs) || bind::isBoolConst(rhs) ||
            isOpX<NEG>(lhs) || isOpX<NEG>(rhs))
        {
          return mk<AND>(mk<OR>(mkNeg(lhs), rhs),
                         mk<OR>(lhs, mkNeg(rhs)));
        }
        return exp;
      }
      return exp;
    }
  };

  struct CondRetriever : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& conds;

    CondRetriever (ExprSet& _conds) :  conds(_conds) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<ITE>(exp))
      {
        conds.insert(exp->arg(0));
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  struct DeltaRetriever : public std::unary_function<Expr, VisitAction>
  {
    ExprVector& srcVars;
    ExprVector& dstVars;
    ExprSet& deltas;

    DeltaRetriever (ExprVector& _srcVars, ExprVector& _dstVars, ExprSet& _deltas):
    srcVars(_srcVars), dstVars(_dstVars), deltas(_deltas) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<EQ>(exp))
      {
        ExprVector av;
        filter (exp, bind::IsConst (), inserter(av, av.begin()));
        if (av.size() != 2) return VisitAction::skipKids ();;
        for (int i = 0; i < srcVars.size(); i++)
        {
          if ((av[0] == srcVars[i] && av[1] == dstVars[i]) ||
              (av[1] == srcVars[i] && av[0] == dstVars[i]))
          {
            set<int> coefs;
            try
            {
              exp = normalizeAtom(exp, av);
              getLinCombCoefs(exp, coefs);
            }
            catch (const boost::bad_lexical_cast& e) { continue; }

            bool success = true;
            for (auto i : coefs) success = success && (i == -1 || i == 1);
            if (success)
            {
              Expr cExpr = exp->right();
              int c = abs(lexical_cast<int>(cExpr));
              if (c > 1)
              {
                Expr cand = mk<GEQ>(mk<MOD>(srcVars[i],
                                        mkTerm (mpz_class (c), exp->getFactory())),
                                        mkTerm (mpz_class (0), exp->getFactory()));
                deltas.insert(cand);
              }
            }
          }
        }
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  inline Expr rewriteBoolEq (Expr exp)
  {
    RW<BoolEqRewriter> tr(new BoolEqRewriter());
    return dagVisit (tr, exp);
  }

  inline void retrieveDeltas (Expr exp, ExprVector& srcVars, ExprVector& dstVars, ExprSet& deltas)
  {
    DeltaRetriever dr (srcVars, dstVars, deltas);
    dagVisit (dr, exp);
  }

  inline void retrieveConds (Expr exp, ExprSet& conds)
  {
    CondRetriever dr (conds);
    dagVisit (dr, exp);
  }

  inline static Expr overapproxTransitions (Expr exp, ExprVector& srcVars, ExprVector& dstVars)
  {
    RW<TransitionOverapprox> rw(new TransitionOverapprox(srcVars, dstVars));
    return dagVisit (rw, exp);
  }

  template <typename T> static void computeTransitiveClosure(ExprSet& r, ExprSet& tr)
  {
    for (auto &a : r)
    {
      if (isOpX<T>(a))
      {
        for (auto &b : tr)
        {
          if (isOpX<T>(b))
          {
            if (a->left() == b->right()) tr.insert(mk<T>(b->left(), a->right()));
            if (b->left() == a->right()) tr.insert(mk<T>(a->left(), b->right()));
            
            if (isSymmetric(a))
            {
              if (a->left()  == b->left())  tr.insert(mk<T>(a->right(), b->right()));
              if (a->right() == b->right()) tr.insert(mk<T>(a->left(),  b->left()));
            }
          }
        }
      }
      tr.insert(a);
    }
  }

  struct TransClAdder
  {
    TransClAdder () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<AND>(exp))
      {
        ExprSet cnjs;
        ExprSet trCnjs;
        getConj(exp, cnjs);
        computeTransitiveClosure<EQ>(cnjs, trCnjs);
        computeTransitiveClosure<LEQ>(cnjs, trCnjs);
        computeTransitiveClosure<GEQ>(cnjs, trCnjs);
        computeTransitiveClosure<LT>(cnjs, trCnjs);
        computeTransitiveClosure<GT>(cnjs, trCnjs);
        return conjoin(trCnjs, exp->getFactory());
      }

      return exp;
    }
  };
  
  inline static Expr enhanceWithMoreClauses (Expr exp)
  {
    RW<TransClAdder> tr(new TransClAdder());
    return dagVisit (tr, exp);
  }
  
  inline static Expr propagateEqualities (Expr exp)
  {
    ExprSet cnjs;
    ExprSet newCnjs;
    ExprSet eqs;
    ExprSet trEqs;
    
    getConj(exp, cnjs);
    
    for (auto &a : cnjs) if (isOpX<EQ>(a)) eqs.insert(a);
    if (eqs.size() == 0) return exp;
    
    computeTransitiveClosure<EQ>(eqs, trEqs);
    
    for (auto &a : cnjs)
    {
      if (isOpX<EQ>(a))
      {
        newCnjs.insert(a);
      }
      else
      {
        Expr neg = mkNeg(a);
        for (auto &b : trEqs)
        {
          Expr repl1 = replaceAll(neg, b->left(), b->right());
          Expr repl2 = replaceAll(neg, b->right(), b->left());
          bool eq1 = (repl1 == neg);
          bool eq2 = (repl2 == neg);
          bool eq3 = (repl2 == repl1);
          
          if (eq1 && eq2 && eq3) newCnjs.insert(a);
          else if (eq1) newCnjs.insert (mk<NEG> (mk<AND>(neg, repl2)));
          else if (eq2) newCnjs.insert (mk<NEG> (mk<AND>(neg, repl1)));
          else newCnjs.insert(mk<NEG> (mk<AND>(neg, mk<AND>(repl1, repl2))));
        }
      }
    }
    
    return conjoin(newCnjs, exp->getFactory());
  }
}

#endif
