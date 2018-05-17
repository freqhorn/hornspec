#ifndef HORN__HPP__
#define HORN__HPP__

#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  inline bool rewriteHelperConsts(Expr& body, Expr v1, Expr v2)
  {
    if (isOpX<MPZ>(v1))
    {
      body = mk<AND>(body, mk<EQ>(v1, v2));
      return true;
    }
    else if (isOpX<TRUE>(v1))
    {
      body = mk<AND>(body, v2);
      return true;
    }
    else if (isOpX<FALSE>(v1))
    {
      body = mk<AND>(body, mk<NEG>(v2));
      return true;
    }
    //else.. TODO: simplifications like "1 + 2" and support for other sorts like Reals and Bools
    return false;
  }

  inline void rewriteHelperDupls(Expr& body, Expr _v1, Expr _v2, Expr v1, Expr v2)
  {
    if (_v1 == _v2) body = mk<AND>(body, mk<EQ>(v1, v2));
    //else.. TODO: mine more complex relationships, like "_v1 + 1 = _v2"
  }

  struct HornRuleExt
  {
    ExprVector srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    Expr body;
    Expr head;

    Expr srcRelation;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;

    void assignVarsAndRewrite (ExprVector& _srcVars, ExprVector& invVarsSrc,
                               ExprVector& _dstVars, ExprVector& invVarsDst)
    {
      for (int i = 0; i < _srcVars.size(); i++)
      {
        srcVars.push_back(invVarsSrc[i]);

        // find constants
        if (rewriteHelperConsts(body, _srcVars[i], srcVars[i])) continue;

        body = replaceAll(body, _srcVars[i], srcVars[i]);
        for (int j = 0; j < i; j++) // find duplicates among srcVars
        {
          rewriteHelperDupls(body, _srcVars[i], _srcVars[j], srcVars[i], srcVars[j]);
        }
      }

      for (int i = 0; i < _dstVars.size(); i++)
      {
        // primed copy of var:
        Expr new_name = mkTerm<string> (lexical_cast<string>(invVarsDst[i]) + "'", body->getFactory());
        Expr var = cloneVar(invVarsDst[i], new_name);
        dstVars.push_back(var);

        // find constants
        if (rewriteHelperConsts(body, _dstVars[i], dstVars[i])) continue;

        body = replaceAll(body, _dstVars[i], dstVars[i]);
        for (int j = 0; j < i; j++) // find duplicates among dstVars
        {
          rewriteHelperDupls(body, _dstVars[i], _dstVars[j], dstVars[i], dstVars[j]);
        }
        for (int j = 0; j < _srcVars.size(); j++) // find duplicates between srcVars and dstVars
        {
          rewriteHelperDupls(body, _dstVars[i], _srcVars[j], dstVars[i], srcVars[j]);
        }
      }
    }
  };

  class CHCs
  {
    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    Expr failDecl;
    vector<HornRuleExt> chcs;
    vector<HornRuleExt*> wtoCHCs;
    ExprVector wtoDecls;
    ExprSet decls;
    map<Expr, ExprVector> invVars;
    map<Expr, vector<int>> outgs;

    CHCs(ExprFactory &efac, EZ3 &z3) : m_efac(efac), m_z3(z3)  {};

    void preprocess (Expr term, ExprVector& srcVars, ExprVector& relations, Expr &srcRelation, ExprSet& lin)
    {
      if (isOpX<AND>(term))
      {
        for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it)
        {
          preprocess(*it, srcVars, relations, srcRelation, lin);
        }
      }
      else
      {
        if (bind::isBoolConst(term))
        {
          lin.insert(term);
        }
        if (isOpX<FAPP>(term))
        {
          if (term->arity() > 0)
          {
            if (isOpX<FDECL>(term->arg(0)))
            {
              for (auto &rel: relations)
              {
                if (rel == term->arg(0))
                {
                  srcRelation = rel->arg(0);
                  for (auto it = term->args_begin()+1, end = term->args_end(); it != end; ++it)
                    srcVars.push_back(*it);
                }
              }
            }
          }
        }
        else
        {
          lin.insert(term);
        }
      }
    }

    void parse(string smt, string varname = " $_")
    {
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);

      for (auto &a : fp.m_rels)
      {
        if (a->arity() == 2)
        {
          failDecl = a->arg(0);
        }
        else if (invVars[a->arg(0)].size() == 0)
        {
          decls.insert(a);
          for (int i = 1; i < a->arity()-1; i++)
          {
            Expr new_name = mkTerm<string> (varname + to_string(i - 1), m_efac);
            Expr var;
            if (isOpX<INT_TY> (a->arg(i)))
              var = bind::intConst(new_name);
            else if (isOpX<REAL_TY> (a->arg(i)))
              var = bind::realConst(new_name);
            else if (isOpX<BOOL_TY> (a->arg(i)))
              var = bind::boolConst(new_name);

            invVars[a->arg(0)].push_back(var);
          }
        }
      }

      for (auto &r: fp.m_rules)
      {
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();

        hr.srcRelation = mk<TRUE>(m_efac);
        Expr rule = r;
        ExprVector args;

        if (isOpX<FORALL>(r))
        {
          rule = r->last();

          for (int i = 0; i < r->arity() - 1; i++)
          {
            Expr var = r->arg(i);
            Expr name = bind::name (r->arg(i));
            Expr new_name = mkTerm<string> (lexical_cast<string> (name.get()), m_efac);
            Expr var_new = bind::fapp(bind::rename(var, new_name));
            args.push_back(var_new);
          }

          ExprVector actual_vars;
          expr::filter (rule, bind::IsVar(), std::inserter (actual_vars, actual_vars.begin ()));
          assert(actual_vars.size() == args.size());

          ExprVector repl_vars;
          for (int i = 0; i < actual_vars.size(); i++)
          {
            string a1 = lexical_cast<string>(bind::name(actual_vars[i]));
            int ind = args.size() - 1 - atoi(a1.substr(1).c_str());
            repl_vars.push_back(args[ind]);
          }
          rule = replaceAll(rule, actual_vars, repl_vars);
        }

        if (!isOpX<IMPL>(rule)) rule = mk<IMPL>(mk<TRUE>(m_efac), rule);

        Expr body = rule->arg(0);
        Expr head = rule->arg(1);

        hr.head = head->arg(0);
        hr.dstRelation = head->arg(0)->arg(0);

        ExprVector origSrcSymbs;
        ExprSet lin;

        preprocess(body, origSrcSymbs, fp.m_rels, hr.srcRelation, lin);
        hr.isFact = isOpX<TRUE>(hr.srcRelation);
        hr.isQuery = (hr.dstRelation == failDecl);
        hr.isInductive = (hr.srcRelation == hr.dstRelation);

        ExprVector allOrigSymbs = origSrcSymbs;
        ExprVector origDstSymbs;

        if (!hr.isQuery)
        {
          for (auto it = head->args_begin()+1, end = head->args_end(); it != end; ++it)
            origDstSymbs.push_back(*it);
        }

        allOrigSymbs.insert(allOrigSymbs.end(), origDstSymbs.begin(), origDstSymbs.end());

        Expr bodyPre = conjoin(lin, m_efac);
        simplBoolReplCnj(allOrigSymbs, lin);
        hr.body = conjoin(lin, m_efac);

        outgs[hr.srcRelation].push_back(chcs.size()-1);

        hr.assignVarsAndRewrite (origSrcSymbs, invVars[hr.srcRelation],
                                 origDstSymbs, invVars[hr.dstRelation]);

        for (auto &a: args)
        {
          bool found = false;
          for (auto &b : origDstSymbs)
          {
            if (a == b) found = true;
          }
          if (! found)
          {
            for (auto &b : origSrcSymbs)
            {
              if (a == b) found = true;
            }
          }
          if (!found)
          {
            hr.locVars.push_back(a);
          }
        }
      }

      wtoSort();
    }

    void addRule (HornRuleExt* r)
    {
      chcs.push_back(*r);
      Expr srcRel = r->srcRelation;
      if (!isOpX<TRUE>(srcRel))
      {
        if (invVars[srcRel].size() == 0)
        {
          addDecl(srcRel, r->srcVars);
        }
      }
      outgs[srcRel].push_back(chcs.size()-1);
    }

    void addDecl(Expr rel, ExprVector& args)
    {
      ExprVector types;
      for (auto &var: args) {
        types.push_back (bind::typeOf (var));
      }
      types.push_back (mk<BOOL_TY> (m_efac));

      decls.insert(bind::fdecl (rel, types));
      for (auto & v : args)
      {
        invVars[rel].push_back(v);
      }
    }

    void addFailDecl(Expr decl)
    {
      failDecl = decl;
    }

    Expr getPrecondition (Expr decl)
    {
      HornRuleExt* hr;
      for (auto &a : chcs) if (a.srcRelation == decl->left() && a.dstRelation == decl->left()) hr = &a;

      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(hr->body, cnjs);
      for (auto &a : cnjs)
      {
        if (emptyIntersect(a, hr->dstVars) && emptyIntersect(a, hr->locVars)) newCnjs.insert(a);
      }
      return conjoin(newCnjs, m_efac);
    }

    void wtoSort()
    {
      if (wtoCHCs.size() > 0)
      {
        outs () << "Already sorted\n";
        return;
      }

      int r1 = 0;
      for (auto & hr : chcs)
        if (hr.isInductive)
        {
          wtoDecls.push_back(hr.srcRelation);
          wtoCHCs.push_back(&hr);
        }
      int r2 = wtoDecls.size();

      while (r1 != r2)
      {
        for (int i = r1; i < r2; i++)
        {
          auto dcl = wtoDecls[i];
          for (auto &hr : chcs)
          {
            if (find(wtoCHCs.begin(), wtoCHCs.end(), &hr) != wtoCHCs.end()) continue;

            if (hr.srcRelation == dcl)
            {
              wtoDecls.push_back(hr.dstRelation);
              wtoCHCs.push_back(&hr);
            }
            else if (hr.dstRelation == dcl)
            {
              wtoDecls.push_back(hr.srcRelation);
              wtoCHCs.push_back(&hr);
            }
          }
        }
        r1 = r2;
        r2 = wtoDecls.size();
      }
      assert(wtoCHCs.size() == chcs.size());

      // filter wtoDecls
      for (auto it = wtoDecls.begin(); it != wtoDecls.end();)
      {
        if (*it == failDecl || isOpX<TRUE>(*it)) it = wtoDecls.erase(it);
        else ++it;
      }
    }

    // Transformations

    void mergeIterations(Expr decl, int num)
    {
      HornRuleExt* hr;
      for (auto &a : chcs) if (a.srcRelation == decl->left() && a.dstRelation == decl->left()) hr = &a;
      Expr pre = getPrecondition(decl);
      ExprSet newCnjs;
      newCnjs.insert(mk<NEG>(pre));
      for (int i = 0; i < hr->srcVars.size(); i++)
      {
        newCnjs.insert(mk<EQ>(hr->dstVars[i], hr->srcVars[i]));
      }
      Expr body2 = conjoin(newCnjs, m_efac);

      // adaping the code from BndExpl.hpp
      ExprVector ssa;
      ExprVector bindVars1;
      ExprVector bindVars2;
      ExprVector newLocals;
      int bindVar_index = 0;
      int locVar_index = 0;

      for (int c = 0; c < num; c++)
      {
        Expr body = hr->body;
        bindVars2.clear();
        if (c != 0)
        {
          body = replaceAll(mk<OR>(body, body2), hr->srcVars, bindVars1);
          for (int i = 0; i < hr->locVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__loc_var_" + to_string(locVar_index++), m_efac);
            Expr var = cloneVar(hr->locVars[i], new_name);
            body = replaceAll(body, hr->locVars[i], var);
            newLocals.push_back(var);
          }
        }

        if (c != num-1)
        {
          for (int i = 0; i < hr->dstVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(bindVar_index++), m_efac);
            bindVars2.push_back(cloneVar(hr->dstVars[i], new_name));
            body = replaceAll(body, hr->dstVars[i], bindVars2[i]);
            newLocals.push_back(bindVars2[i]);
          }
        }
        ssa.push_back(body);
        bindVars1 = bindVars2;
      }
      hr->body = conjoin(ssa, m_efac);
      hr->locVars.insert(hr->locVars.end(), newLocals.begin(), newLocals.end());
    }

    void slice (Expr decl, ExprSet& vars)
    {
      HornRuleExt* hr;
      for (auto &a : chcs) if (a.srcRelation == decl->left() && a.dstRelation == decl->left()) hr = &a;
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(hr->body, cnjs);
      map <Expr, ExprSet> deps;

      for (auto &a : cnjs)
      {
        ExprSet cnj_vars;
        ExprSet cnj_vars_cmpl;
        expr::filter (a, bind::IsConst(), std::inserter (cnj_vars, cnj_vars.begin ()));
        for (auto & a : cnj_vars)
        {
          int index = getVarIndex(a, hr->srcVars);
          if (index >= 0)
          {
            cnj_vars_cmpl.insert(hr->dstVars[index]);
            continue;
          }
          index = getVarIndex(a, hr->dstVars);
          if (index >= 0)
          {
            cnj_vars_cmpl.insert(hr->srcVars[index]);
          }
        }
        cnj_vars.insert(cnj_vars_cmpl.begin(), cnj_vars_cmpl.end());
        deps[a] = cnj_vars;
      }

      while (vars.size() > 0)
      {
        for (auto vit = vars.begin(); vit != vars.end(); )
        {
          for (auto cit = cnjs.begin(); cit != cnjs.end(); )
          {
            ExprSet& d = deps[*cit];
            if (find(d.begin(), d.end(), *vit) != d.end())
            {
              newCnjs.insert(*cit);
              cit = cnjs.erase(cit);
              vars.insert(d.begin(), d.end());
            }
            else
            {
              ++cit;
            }
          }
          vit = vars.erase (vit);
        }
      }
      hr->body = conjoin(newCnjs, m_efac);
    }

    bool checkWithSpacer()
    {
      bool success = false;

      // fixed-point object
      ZFixedPoint<EZ3> fp (m_z3);
      ZParams<EZ3> params (m_z3);
      params.set (":engine", "spacer");
      params.set (":xform.slice", false);
      params.set (":pdr.utvpi", false);
      params.set (":use_heavy_mev", true);
      params.set (":xform.inline-linear", false);
      params.set (":xform.inline-eager", false);
      params.set (":xform.inline-eager", false);

      fp.set (params);

      fp.registerRelation (bind::boolConstDecl(failDecl));

      for (auto & dcl : decls) fp.registerRelation (dcl);
      Expr errApp;

      for (auto & r : chcs)
      {
        ExprSet allVars;
        allVars.insert(r.srcVars.begin(), r.srcVars.end());
        allVars.insert(r.dstVars.begin(), r.dstVars.end());
        allVars.insert(r.locVars.begin(), r.locVars.end());

        if (!r.isQuery)
        {
          for (auto & dcl : decls)
          {
            if (dcl->left() == r.dstRelation)
            {
              r.head = bind::fapp (dcl, r.dstVars);
              break;
            }
          }
        }
        else
        {
          r.head = bind::fapp(bind::boolConstDecl(failDecl));
          errApp = r.head;
        }

        Expr pre;
        if (!r.isFact)
        {
          for (auto & dcl : decls)
          {
            if (dcl->left() == r.srcRelation)
            {
              pre = bind::fapp (dcl, r.srcVars);
              break;
            }
          }
        }
        else
        {
          pre = mk<TRUE>(m_efac);
        }

        fp.addRule(allVars, boolop::limp (mk<AND>(pre, r.body), r.head));
      }
      try {
        success = !fp.query(errApp);
      } catch (z3::exception &e){
        char str[3000];
        strncpy(str, e.msg(), 300);
        outs() << "Z3 ex: " << str << "...\n";
        exit(55);
      }
      return success;
    }

    void print()
    {
      outs() << "CHCs:\n";
      for (auto &hr: chcs){
        if (hr.isFact) outs() << "  INIT:\n";
        if (hr.isInductive) outs() << "  TRANSITION RELATION:\n";
        if (hr.isQuery) outs() << "  BAD:\n";

        outs () << "    " << * hr.srcRelation;
        if (hr.srcVars.size() > 0)
        {
          outs () << " (";
          for(auto &a: hr.srcVars) outs() << *a << ", ";
          outs () << "\b\b)";
        }
        outs () << " -> " << * hr.dstRelation;

        if (hr.dstVars.size() > 0)
        {
          outs () << " (";
          for(auto &a: hr.dstVars) outs() << *a << ", ";
          outs () << "\b\b)";
        }
        outs() << "\n    body: " << * hr.body << "\n";
      }
    }
  };
}


#endif
