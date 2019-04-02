#include "util/rational.h"
#include "spacer_context.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "ast/ast.h"
#include "ast/rewriter/expr_safe_replace.h"

typedef std::pair<expr*,expr*> bound;
typedef std::map<unsigned,bound> vars_bound;
namespace spacer {
  struct under_approx
  {
    ast_manager &m;
    arith_util m_arith;
  public :
    under_approx (ast_manager& manager):m(manager),m_arith(m){}
    expr* getLHS(expr * e)
    {
      SASSERT(is_app(e));
      return getLHS(to_app(e));
    }
    expr* getLHS(app * e)
    {
      SASSERT(m_arith.is_arith_expr(e));
      return e->get_arg(0);
    }
    expr* getRHS(expr * e)
    {
      SASSERT(is_app(e));
      return getRHS(to_app(e));
    }
    expr* getRHS(app * e)
    {
      SASSERT(m_arith.is_arith_expr(e));
      return e->get_arg(1);
    }
    // propagates negation
    // (not (<= a 5)) == (> a 5)
    void get_negated_child(app * e,app_ref& result)
    {
      SASSERT(m.is_not(e));
      SASSERT(is_arith(e));
      app* e_child = to_app(e->get_arg(0));
      expr* term = getLHS(e_child);
      expr* constant = getRHS(e_child);
      SASSERT(is_uninterp_const(term) || m_arith.is_arith_expr(term));
      SASSERT(m_arith.is_numeral(constant));
        if(m_arith.is_le(e_child))
            result=m_arith.mk_gt(term,constant);
        else if(m_arith.is_lt(e_child))
          result=m_arith.mk_ge(term,constant);
        else if(m_arith.is_ge(e_child))
          result=m_arith.mk_lt(term,constant);
        else if(m_arith.is_gt(e_child))
          result=m_arith.mk_le(term,constant);
        else
          SASSERT(false);
     }
    //identifies whether e is an arithmetic expression or the negation of one
    bool is_arith(app* e)
    {
      if(m.is_not(e))
        {
          expr * e_child = e->get_arg(0);
          if(is_app(e_child))
            return is_arith(to_app(e_child));
          else
            return false;
        }
      return m_arith.is_arith_expr(e);
    }
    // normalizes expression to be a le with variables on the lhs and numeral on the rhs
    // works only on integar arithmetic
    void normalize_le(app* e, app_ref& result)
    {
    //works only for integers. Need to assert that as well
    SASSERT(m_arith.is_arith_expr(e));
    expr* lhs=getLHS(e);
    expr* rhs=getRHS(e);
    app* minus_one = m_arith.mk_int(-1);
    if(m_arith.is_lt(e))
      result= m_arith.mk_le(lhs,m_arith.mk_add(rhs,minus_one));
    else if(m_arith.is_ge(e))
      result = m_arith.mk_le(m_arith.mk_mul(lhs,minus_one),m_arith.mk_mul(rhs,minus_one));
    else if(m_arith.is_gt(e))
      result = m_arith.mk_le(m_arith.mk_mul(lhs,minus_one),m_arith.mk_add(m_arith.mk_mul(rhs,minus_one),minus_one));
    else
      {
        SASSERT(m_arith.is_le(e));
        result= m_arith.mk_le(lhs,rhs);
      }
    }
    //stores all unique uninterpreted constans in exp in vars
    void get_uninterp_const(expr_ref_vector exp,expr_ref_vector& vars)
    {
      for(expr* e : exp)
        {
          SASSERT(is_app(e));
          get_uninterp_const(to_app(e),vars);
        }
    }
    // stores all unique uninterpreted constants in exp in vars
    void get_uninterp_const(app* exp, expr_ref_vector& vars)
    {
      for(expr* e: *exp)
        {
          if(is_uninterp_const(e) && !vars.contains(e))
            vars.push_back(e);
          else if(is_app(e))
            get_uninterp_const(to_app(e),vars);
        }
    }
    /*
      computes the coeff of var in l. Returns false if var not in l
      assumes that there is only occurrence of var in l
      should be of the form -1*(ax+by+..) or (ax+by+...)
      assumes that the coeff is initialized to an appropriate value
    */
    bool get_coeff(app* l,expr* const var,rational & coeff)
    {
      //If its an uninterpreted constant, the coeff is not going to change
      if(is_uninterp_const(l))
        return l->get_id()==var->get_id();
      if(m_arith.is_numeral(l))
        return false;
      SASSERT(m_arith.is_arith_expr(l));
      SASSERT(m_arith.is_add(l) || m_arith.is_mul(l));
      if(m_arith.is_mul(l))
        {
          if(m_arith.is_numeral(l->get_arg(0)))
            {
              SASSERT(is_app(l->get_arg(1)));
              if( get_coeff(to_app(l->get_arg(1)),var,coeff))
                {
                  rational temp;
                  m_arith.is_numeral(l->get_arg(0),temp);
                  coeff=coeff*temp;
                  return true;
                }
              return false;
            }
          else
            {
              SASSERT(m_arith.is_numeral(l->get_arg(1)));
              SASSERT(is_app(l->get_arg(0)));
              if(get_coeff(to_app(l->get_arg(0)),var,coeff))
                {
                  rational temp;
                  m_arith.is_numeral(l->get_arg(1),temp);
                  coeff=coeff*temp;
                  return true;
                }
              return false;
            }
        }
      for(expr * e : *l)
        {
          if(e->get_id() == var->get_id())
          return true;
          else if(is_app(e) && (to_app(e))->get_num_args()>1)
            {
              if(get_coeff(to_app(e),var,coeff))
                return true;
            }
        }
      return false;
    }
    //computes a lower or upper bound for uninterpreted constant var
    //if var not in l, returns no bounds
    bound ua_variable(model_ref model,app_ref l,expr* var,std::map<expr*,expr*> *sub = nullptr)
    {
      rational coeff(1);
      expr * lhs = getLHS(l);
      //lhs is in the sum of products form (ax + by)
      SASSERT(is_app(lhs));
      get_coeff(to_app(lhs),var,coeff);
      SASSERT(coeff.is_int());
      expr_ref bnd(m);
      if(sub)
        {
          std::map<expr*,expr*>::iterator itr = sub->find(var);
          SASSERT(itr!=sub->end());
          bnd = (*model)(itr->second);
        }
      else
        bnd = (*model)(&(*var));
      SASSERT(m_arith.is_numeral(bnd));
      TRACE("under_approximate_verb", tout<<"bound is "<<mk_pp(bnd,m)<<"\n";);

      TRACE("under_approximate_verb", tout<<"coefficient found "<<mk_pp(var,m)<<" in literal "<<mk_pp(l,m)<< " is "<< coeff<<"\n";);
      if(coeff.is_pos())
        return bound(nullptr,bnd);
      else if(coeff.is_neg())
        return bound(bnd,nullptr);
      else
        SASSERT(coeff.is_zero());
      return bound(nullptr,nullptr);
    }
    // true if numeral(a) < numeral(b)
    bool is_less_than(expr* a , expr* b)
    {
      SASSERT(a!=nullptr);
      SASSERT(b!=nullptr);
      rational a_rat,b_rat;
      m_arith.is_numeral(a,a_rat);
      m_arith.is_numeral(b,b_rat);
      SASSERT(a_rat.is_int());
      SASSERT(b_rat.is_int());
      return a_rat<b_rat;
    }
    //computes bounds u_v on each variable v in l
    // phi ==> ( &u_v ==> l)
    vars_bound ua_literal(model_ref model,app_ref l,expr_ref_vector phi,std::map<expr*,expr*> *sub = nullptr)
    {
      expr_ref_vector variables(m);
      get_uninterp_const(l,variables);
      //TODO : compute the orthogonal projection
      model_ref ortho_project = model;
      vars_bound v;
      for (expr* e : variables)
        {
          verbose_stream()<< mk_pp(e,m)<<" id before "<<e->get_id()<<"\n";
          v[e->get_id()] = ua_variable(ortho_project,l,e,sub);
          verbose_stream()<<"\n id after "<<e->get_id()<<"\n";
          TRACE("under_approximate_verb", tout<<"bounds for "<<mk_pp(e,m)<<" is "<<mk_pp(v[e->get_id()].first,m) <<" and "<< mk_pp(v[e->get_id()].second,m)<<"\n";);

        }
      return v;
    }
    // under approximate proof obligation n using literals of dim 1
    // returns nullptr if pob is not in LA
    pob* under_approximate(pob&n, model_ref model)
    {
      expr * e = to_app(n.post());
      app_ref e_app(m);
      SASSERT(is_app(e));
      expr_ref_vector ua_pob(m);
      if(m.is_not(to_app(e)))
        {
          get_negated_child(to_app(e),e_app);
        }
      else
        {
          e_app = to_app(e);
        }
      expr_ref_vector e_and(m);
      flatten_and(e_app,e_and);
      for(unsigned i =0 ; i < e_and.size();i++)
        {
          expr* temp = e_and.get(i);
          if(!(is_app(temp) && is_arith(to_app(temp))))
            return nullptr;
        }
      /* if(e_and.size()==1) */
      /*   { */
      /*     expr_ref_vector e_grp(m); */
      /*     for(expr* sub_term : *to_app(e_and.get(0))) */
      /*       { */
      /*         if(!m_arith.is_numeral(sub_term)) */
      /*           e_grp.push_back(sub_term); */
      /*       } */
      /*     group(e_and,e_grp,model); */
      /*   } */
      vars_bound v;
      ua_formula(e_and,model,v);
      //construct pob
      expr_ref_vector variables(m);
      get_uninterp_const(e_app,variables);
      for(expr* variable : variables)
        {
          if(v.find(variable->get_id()) !=v.end())
            {
              if(v[variable->get_id()].first != nullptr)
                {
                  expr* lb = v[variable->get_id()].first;
                  ua_pob.push_back(m_arith.mk_ge(variable,lb));
                }
              if(v[variable->get_id()].second != nullptr)
                {
                  expr* ub = v[variable->get_id()].second;
                  ua_pob.push_back(m_arith.mk_le(variable,ub));
                }
            }
        }
      TRACE("under_approximate", tout<< "produced an arithmetic pob: "<< mk_pp(mk_and(ua_pob),m)<<"\n";);
      return n.pt().mk_pob(&n,n.level(),n.depth(),mk_and(ua_pob),n.get_binding());
    }
    //computes bounds on each variable in e_and. If the variable is a substitution for a term, the bound on the variable is a bound on the term.
    void ua_formula(expr_ref_vector e_and,model_ref model,vars_bound& v,std::map<expr*,expr*>*sub = nullptr)
    {
      for(unsigned i =0 ; i < e_and.size();i++)
        {
          expr* temp = e_and.get(i);
          SASSERT(is_app(temp) && is_arith(to_app(temp)));
          app_ref rewrite(m);
          if(m.is_not(to_app(temp)))
            get_negated_child(to_app(temp),rewrite);
          else
            rewrite=to_app(temp);
          app_ref normalized_expr(m);
          normalize_le(rewrite,normalized_expr);
          TRACE("under_approximate", tout<< "literal is "<< mk_pp(temp,m)<<" normalized literal is " << mk_pp(normalized_expr,m)<< " LHS is "<< mk_pp(getLHS(normalized_expr),m)<<" RHS is " << mk_pp(getRHS(normalized_expr),m) <<"\n";);

          expr_ref_vector phi(m);
          for(unsigned j=0;j<e_and.size();j++)
            if(j!=i)
              phi.push_back(&(*(e_and.get(j))));
          if(phi.size()==0)
            phi.push_back(m.mk_true());
          vars_bound t= ua_literal(model,normalized_expr,phi,sub);
          vars_bound::iterator itr = t.begin();
          while(itr != t.end())
            {
              if(v.find(itr->first) != v.end())
                {
                  if((v[itr->first].first == nullptr )|| (itr->second.first != nullptr && is_less_than(v[itr->first].first,itr->second.first)))
                    v[itr->first].first = itr->second.first;
                  if((v[itr->first].second == nullptr) || (itr->second.second != nullptr && is_less_than(itr->second.second,v[itr->first].second)))
                    v[itr->first].second = itr->second.second;
                }
              else
                {
                  v[itr->first] = itr->second;
                }
              itr++;
            }
        }
   }
    bool is_disjoint(app* g1, app* g2)
    {
      expr_ref_vector v1(m),v2(m);
      get_uninterp_const(g1,v1);
      get_uninterp_const(g2,v2);
      for(expr* p : v1)
        for(expr* q : v2)
          if(p->get_id() == q->get_id())
            return false;
      return true;
    }
    bool is_disjoint(expr_ref_vector group)
    {
      for(unsigned i = 0 ; i < group.size() ; i++)
          for(unsigned j = i+1; j < group.size() ;j++)
            {
              SASSERT(is_app(group.get(i)));
              SASSERT(is_app(group.get(j)));
              if(!is_disjoint(to_app(group.get(i)),to_app(group.get(j))))
                return false;
            }
      return true;
    }
    //takes as input a conjunction of literals expr, a satisfying assignment m
    //and a set of disjoint groups
    expr_ref_vector group(expr_ref_vector pob,expr_ref_vector groups,model_ref model)
    {
      TRACE("under_approximate", tout<< "grouping an arithmetic pob : "; for(expr * e : pob) tout<<mk_pp(e,m)<<" ";tout<<"\n"; );
      TRACE("under_approximate", tout<< "groups are : "; for(expr * e : groups) tout<<mk_pp(e,m)<<" ";tout<<"\n"; );
      expr_ref pob_sub(m);
      SASSERT(is_sop(pob));
      SASSERT(is_disjoint(groups));
      SASSERT(can_group(pob,groups));
      //TODO ensure union of groups has all the variables
      expr_safe_replace s(m);
      expr_ref_vector vars(m);
      std::map<expr*,expr*> sub;
      get_uninterp_const(pob,vars);
      for(expr* group : groups)
        {
          /* SASSERT(is_sub_expr(group,pob)); */
          expr_ref eval_ref = (*model)(&(*group));
          SASSERT(m_arith.is_numeral(eval_ref));
          expr_ref fresh_const(m);
          fresh_const = m.mk_fresh_const("sub_temp",m_arith.mk_int());
          s.insert(group,fresh_const);
          sub[fresh_const.get()]=group;
        }
      s(mk_and(pob),pob_sub);
      TRACE("under_approximate", tout<< "substituted pob : "<<mk_pp(pob_sub,m)<<"\n"; );
      vars_bound v;
      expr_ref_vector pob_sub_vec(m);
      flatten_and(pob_sub,pob_sub_vec);
      ua_formula(pob_sub_vec,model,v,&sub);
      expr_ref_vector ua_pob(m);
      for(std::pair<expr*,expr*> var_expr : sub)
        {
          unsigned id = var_expr.first->get_id();
          if(v.find(id) !=v.end())
            {
                if(v[id].first != nullptr)
                {
                  ua_pob.push_back(m_arith.mk_ge(var_expr.second,v[id].first));
                }
              if(v[id].second != nullptr)
                {
                  tout<<" sub term"<<mk_pp(var_expr.second,m);
                  tout<<" bound "<<mk_pp(v[id].second,m);
                  ua_pob.push_back(m_arith.mk_le(var_expr.second,v[id].second));
                }
            }
        }
      TRACE("under_approximate", tout<< "split pob : "<<mk_pp(mk_and(ua_pob),m)<<"\n"; );
      return ua_pob;
    }
    // checks whether c \in g
    bool contains(expr_ref_vector g,expr* c)
    {
      for(expr* e : g)
        if(c->get_id()==e->get_id())
                return true;
      return false;
    }
    //get that subexpression containing only uinterpreted constants in g
    /* expr* get_term(expr* e,expr_ref_vector g) */
    /* { */
    /*   SASSERT(is_sop(e)); */
    /*   expr_ref sub_term(m); */
    /*   app* lhs = to_app(getLHS(e)); */
    /*   for(expr* child : *lhs) */
    /*     { */
    /*       if(m_arith.is_mul(child)) */
    /*         { */
    /*           expr* arg1 = to_app(child)->get_arg(0); */
    /*           expr* arg2 = to_app(child)->get_arg(1); */
    /*           if(contains(g,arg1) || contains(g,arg2)) */
    /*             sub_term.push_back(child); */
    /*         } */
    /*       else if(is_uninterp_const(child) && contains(g,child)) */
    /*         sub_term.push_back(child); */
    /*     } */
    /*   return m_arith.mk_add(sub_term.size(),*sub_term); */
    /* } */
    bool is_constant(expr* e)
    {
      return is_uninterp_const(e) || m_arith.is_numeral(e) ;
    }
    bool is_sop(expr_ref_vector e)
    {
      for(expr* e_child : e)
        if(!is_sop(e_child))
          return false;
      return true;
    }
    //checks whether arithmetic expression e is a sum of products
    //assumes that all the terms are on the lhs and the rhs is just a numeral
    bool is_sop(expr* e)
    {
      //constants are special cases since they don't have children
      if(is_constant(e))
        return true;
      if(!m_arith.is_arith_expr(e))
        return false;
      expr* lhs = getLHS(e);
      //skipping the check for numeral RHS since it can be a product of numerals.
      //TODO simplify RHS
      /* SASSERT(m_arith.is_numeral(getRHS(e))); */
      //cannot have a top level operand other than plus
      if(!m_arith.is_add(lhs) && !is_constant(lhs))
        {
          if(m_arith.is_mul(lhs))
            {
              // all arguments for the product should be constants. 
              for(expr* term_child : *to_app(lhs))
                if(!is_constant(term_child))
                  return false;
            }
          else{
            return false;
          }
        }
      //all terms inside have to be either a constant or a product of constants
      SASSERT(is_app(lhs));
      for(expr* term : *to_app(lhs))
        {
          if(m_arith.is_mul(term))
            {
              // all arguments for the product should be constants. 
              for(expr* term_child : *to_app(term))
                if(!is_constant(term_child))
                  return false;
            }
          else if(! is_constant(term))
            return false;
        }
      return true;
    }
    void mk_sop(expr* orig_exp, expr* result)
    {
      //TODO use th rewriter som
      /* SASSERT(!is_sop(orig_exp)); */
      /* SASSERT(m_arith.is_arith_expr(orig_expr)); */
      /* expr * lhs = getLHS(orig_expr); */
      /* SASSERT(m_arith.is_numeral(getRHS(orig_expr))); */
      /* if(m_arith.is_mul(lhs)) */
      /*   { */
      /*   } */
      return;
    }
    //returns true when each expression in group is either a sub expr of any of
    //the literals in exp or not in any of the literals of exp
    bool can_group(expr_ref_vector exp,expr_ref_vector group)
    {
      //assuming exp is an and of its arguments.
      for(expr* temp : group)
        {
          if(!can_group(exp,temp))
            return false;
        }
      return true;
    }
    bool can_group(expr_ref_vector exp,expr* sub_expr)
    {
      return true;
    }
};
}
