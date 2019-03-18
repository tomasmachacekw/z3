#include "util/rational.h"
#include "spacer_context.h"
#include "tactic/core/ctx_simplify_tactic.h"

typedef std::pair<expr*,expr*> bound;
typedef std::map<unsigned,bound> vars_bound;
namespace spacer {
  struct under_approx
  {
    ast_manager &m;
    arith_util m_arith;
  public :
    under_approx (ast_manager& manager):m(manager),m_arith(m){}
    expr* getLHS(app * e)
    {
      SASSERT(m_arith.is_arith_expr(e));
      return e->get_arg(0);
    }
    expr* getRHS(app * e)
    {
      SASSERT(m_arith.is_arith_expr(e));
      return e->get_arg(1);
    }
    // propagates negation
    // (not (<= a b)) == (> a b)
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
    bound ua_variable(model_ref model,app_ref l,expr_ref_vector phi,expr* var)
    {
      rational coeff(1);
      expr * lhs = getLHS(l);
      //lhs is in the sum of products form (ax + by)
      SASSERT(is_app(lhs));
      get_coeff(to_app(lhs),var,coeff);
      SASSERT(coeff.is_int());
      expr_ref bnd = (*model)(&(*var));
      SASSERT(m_arith.is_numeral(bnd));
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
      rational a_rat,b_rat;
      m_arith.is_numeral(a,a_rat);
      m_arith.is_numeral(b,b_rat);
      SASSERT(a_rat.is_int());
      SASSERT(b_rat.is_int());
      return a_rat<b_rat;
    }
    //computes bounds u_v on each variable v in l
    // phi ==> ( &u_v ==> l)
    vars_bound ua_literal(model_ref model,app_ref l,expr_ref_vector phi)
    {
      expr_ref_vector variables(m);
      get_uninterp_const(l,variables);
      //TODO : compute the orthogonal projection
      model_ref ortho_project = model;
      vars_bound v;
      for (expr* e : variables)
        {
          v[e->get_id()] = ua_variable(ortho_project,l,phi,e);
        }
      return v;
    }
    // under approximate proof obligation n using literals of dim 1
    // returns nullptr if pob is not in LA
    pob* ua_formula(pob& n,model_ref model)
    {
      vars_bound v;
      arith_util m_arith(m);
      app * e = to_app(n.post());
      SASSERT(is_app(e));
      expr_ref_vector ua_pob(m);

      for(unsigned i =0 ; i < e->get_num_args();i++)
        {
          expr* temp = e->get_arg(i);
          if(!(is_app(temp) && is_arith(to_app(temp))))
            return nullptr;
          app_ref rewrite(m);
          if(m.is_not(to_app(temp)))
            get_negated_child(to_app(temp),rewrite);
          else
            rewrite=to_app(temp);
          app_ref normalized_expr(m);
          normalize_le(rewrite,normalized_expr);
          TRACE("under_approximate", tout<< "literal is "<< mk_pp(temp,m)<<" normalized literal is " << mk_pp(normalized_expr,m)<< " LHS is "<< mk_pp(getLHS(normalized_expr),m)<<" RHS is " << mk_pp(getRHS(normalized_expr),m) <<"\n";);

          expr_ref_vector phi(m);
          for(unsigned j=0;j<e->get_num_args();j++)
            if(j!=i)
              phi.push_back(&(*(e->get_arg(j))));

          vars_bound t= ua_literal(model,normalized_expr,phi);
          vars_bound::iterator itr = t.begin();
          while(itr != t.end())
            {
              if(v.find(itr->first) != v.end())
                {
                  if(itr->second.first != nullptr && is_less_than(v[itr->first].first,itr->second.first))
                    v[itr->first].first = itr->second.first;
                  if(itr->second.second != nullptr && is_less_than(itr->second.second,v[itr->first].second))
                    v[itr->first].second = itr->second.second;
                }
              else
                {
                  v[itr->first] = itr->second;
                }
              itr++;
            }
        }
      //construct pob
      expr_ref_vector variables(m);
      get_uninterp_const(e,variables);
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
    TRACE("under_approx", tout<< "produced an arithmetic pob: "<< mk_pp(mk_and(ua_pob),m)<<"\n";);
    return n.pt().mk_pob(&n,n.level(),n.depth(),mk_and(ua_pob),n.get_binding());
    }
  };
}
