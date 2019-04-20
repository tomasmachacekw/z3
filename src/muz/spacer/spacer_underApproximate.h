#include "util/rational.h"
#include "spacer_context.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "ast/ast.h"
#include "ast/rewriter/expr_safe_replace.h"

typedef obj_map<expr,expr*> expr_expr_map;
namespace spacer {
    class under_approx {
        ast_manager &m;
        arith_util m_arith;

        //reference to all bounds that were made
        expr_ref_vector m_refs;
    public :
        under_approx (ast_manager& manager): m(manager), m_arith(m), m_refs(m) {}

        expr* getLHS(expr * e) {
            SASSERT(is_app(e));
            return getLHS(to_app(e));
        }
        expr* getLHS(app * e) {
            SASSERT(m_arith.is_arith_expr(e));
            return e->get_arg(0);
        }
        expr* getRHS(expr * e) {
            SASSERT(is_app(e));
            return getRHS(to_app(e));
        }
        expr* getRHS(app * e) {
            SASSERT(m_arith.is_arith_expr(e));
            return e->get_arg(1);
        }

        // propagates negation
        // (not (<= a 5)) == (> a 5)
        void push_not(app * e, app_ref& result)
        {
            SASSERT(m.is_not(e));
            SASSERT(is_arith(e));
            app* arg = to_app(e->get_arg(0));
            expr* term = getLHS(arg);
            expr* constant = getRHS(arg);
            SASSERT(is_uninterp_const(term) || m_arith.is_arith_expr(term));
            SASSERT(m_arith.is_numeral (constant));
            if (m_arith.is_le(arg))
                result = m_arith.mk_gt(term, constant);
            else if (m_arith.is_lt(arg))
                result = m_arith.mk_ge(term, constant);
            else if(m_arith.is_ge(arg))
                result=m_arith.mk_lt(term, constant);
            else if(m_arith.is_gt(arg))
                result=m_arith.mk_le(term, constant);
            else
                SASSERT(false);
        }

        /// returns true if e is an arithmetic expression
        bool is_arith(expr* e) {
            // XXX handle equality

            expr *arg;
            if (!is_app(e)) return false;
            return m.is_not(e, arg) ? is_arith(arg) : m_arith.is_arith_expr(e);
        }

        // normalizes expression to be a le with variables on the lhs and numeral on the rhs
        // works only on integar arithmetic
        void normalize_le(app* e, app_ref& result)
        {
            //works only for integers. Need to assert that as well
            SASSERT(m_arith.is_arith_expr(e));
            expr* lhs = getLHS(e);
            expr* rhs = getRHS(e);
            app* minus_one = m_arith.mk_int(-1);
            if(m_arith.is_lt(e))
                result = m_arith.mk_le(lhs, m_arith.mk_add (rhs, minus_one));
            else if(m_arith.is_ge(e))
                result = m_arith.mk_le(m_arith.mk_mul(lhs, minus_one), m_arith.mk_mul(rhs, minus_one));
            else if(m_arith.is_gt(e))
                result = m_arith.mk_le(m_arith.mk_mul(lhs,minus_one), m_arith.mk_add(m_arith.mk_mul(rhs, minus_one), minus_one));
            else
                {
                    SASSERT(m_arith.is_le(e));
                    result = m_arith.mk_le (lhs, rhs);
                }

            // simplify result. XXX should ensure that result is constructed simplified
            expr_ref res(m);
            res = result;
            th_rewriter rw(result.get_manager());
            rw(res);
            result = to_app(res.get());
        }

       /*
          computes the coeff of var in l. Returns false if var not in l
          assumes that there is only occurrence of var in l
          should be of the form -1*(ax+by+..) or (ax+by+...)
          assumes that the coeff is initialized to an appropriate value
        */
        bool get_coeff(app* l, const expr* var, rational & coeff)
        {
            // XXX coeff might be uninitialized when true is returned!

            //If its an uninterpreted constant, the coeff is not going to change
            if (is_uninterp_const(l)) return l == var;
            if (m_arith.is_numeral(l)) return false;

            SASSERT(m_arith.is_arith_expr(l));
            SASSERT(m_arith.is_add(l) || m_arith.is_mul(l));
            if (m_arith.is_mul(l)) {
                if (m_arith.is_numeral(l->get_arg(0))) {
                    SASSERT(is_app(l->get_arg(1)));
                    if (get_coeff(to_app(l->get_arg(1)), var, coeff)) {
                        rational n;
                        m_arith.is_numeral(l->get_arg(0), n);
                        coeff = coeff * n;
                        return true;
                    }
                    return false;
                }
                else {
                    SASSERT(m_arith.is_numeral(l->get_arg(1)));
                    SASSERT(is_app(l->get_arg(0)));
                    if (get_coeff(to_app(l->get_arg(0)), var, coeff)) {
                            rational n;
                            m_arith.is_numeral(l->get_arg(1), n);
                            coeff = coeff * n;
                            return true;
                        }
                    return false;
                }
            }

            // !is_mul(l)
            for(expr * e : *l) {
                if (e == var) return true;
                else if (is_app(e) && (to_app(e))->get_num_args() > 1) {
                    // XXX comment why recursion is bounded and why caching is not needed
                    if (get_coeff(to_app(e), var, coeff))
                        return true;
                }
            }
            return false;
        }

        //returns whether l increases(1), decreases(-1) or doesn't change(0) with var
        int ua_variable(app_ref l, expr* var) {
            rational coeff(1);
            expr * lhs = getLHS(l);
            //lhs is in the sum of products form (ax + by)
            SASSERT(is_app(lhs));
            get_coeff(to_app(lhs), var, coeff);
            SASSERT(coeff.is_int());

            TRACE("under_approximate_verb",
                  tout << "coefficient found " << mk_pp(var,m)
                  << " in literal " << l << " is " << coeff << "\n";);
            if(coeff.is_pos())
                return 1;
            else if(coeff.is_neg())
                return -1;
            else
                SASSERT(coeff.is_zero());
            return 0;
        }
        // true if numeral(a) < numeral(b)
        bool is_less_than(expr* a , expr* b)
        {
            SASSERT(a);
            SASSERT(b);
            rational a_rat, b_rat;
            m_arith.is_numeral(a, a_rat);
            m_arith.is_numeral(b, b_rat);
            SASSERT(a_rat.is_int ());
            SASSERT(b_rat.is_int ());
            return a_rat < b_rat;
        }
        //computes bounds u_v on each variable v in l
        // phi ==> ( &u_v ==> l)
        void ua_literal (model_ref model, app_ref l, expr_ref_vector phi,
                         expr_expr_map& lb, expr_expr_map& ub,
                         expr_expr_map* sub = nullptr)
        {
            SASSERT(lb.size() == 0);
            SASSERT(ub.size() == 0);
            expr_ref_vector variables(m);
            get_uninterp_consts (l, variables);

            //TODO : compute the orthogonal projection
            for (expr* e : variables) {
                    int change = ua_variable(l, e);
                    expr_ref bnd(m);
                    if(sub)
                        bnd = (*model)((*sub)[e]);
                    else
                        bnd = (*model)(e);
                    SASSERT(m_arith.is_numeral(bnd));

                    //save reference since the map won't do it
                    m_refs.push_back(bnd);
                    if(change == 1) {
                        ub.insert(e, bnd.get());
                        TRACE("under_approximate_verb", tout << "upper bounds for " << mk_pp(e,m) << " is " << mk_pp(ub[e],m) << "\n";);
                    }
                    else if ( change == -1) {
                        lb.insert (e, bnd.get());
                        TRACE("under_approximate_verb", tout << "lower bounds for " << mk_pp(e,m) << " is " << mk_pp(lb[e],m) << "\n";);
                    }
                }
        }
        // under approximate proof obligation n using literals of dim 1
        // returns nullptr if pob is not in LA
        pob* under_approximate(pob& n, model_ref model) {
            expr * e = to_app(n.post());
            app_ref e_app(m);
            SASSERT(is_app(e));

            expr_ref_vector ua_pob(m);
            if(m.is_not(to_app(e))) {
                    push_not(to_app(e), e_app);
            }
            else {
                e_app = to_app(e);
            }
            expr_ref_vector e_and(m);
            flatten_and(e_app, e_and);
            for(unsigned i =0; i < e_and.size(); i++) {
                expr* temp = e_and.get(i);
                if(!(is_app(temp) && is_arith(to_app(temp))))
                    return nullptr;
            }
            //temp hack for testing.
            if(e_and.size() == 1) {
                expr_ref_vector e_grp(m);
                for(expr* sub_term : *to_app(e_and.get(0))) {
                    if(!m_arith.is_numeral(sub_term))
                        if(m_arith.is_add(sub_term))
                            for(expr* arg : *to_app(sub_term))
                                e_grp.push_back(arg);
                }
                group(e_and,e_grp,model,ua_pob);
            }
            else {
                expr_expr_map lb,ub;
                ua_formula(e_and, model, lb, ub);
                //construct pob
                expr_ref_vector variables(m);
                get_uninterp_consts(e_app, variables);
                for(expr* variable : variables) {
                    if(lb.contains(variable))
                        ua_pob.push_back(m_arith.mk_ge(variable, lb[variable]));
                    if(ub.contains(variable))
                        ua_pob.push_back(m_arith.mk_le(variable, ub[variable]));
                }
            }
            TRACE("under_approximate", tout<< "produced an arithmetic pob: "<< mk_pp(mk_and(ua_pob),m)<<"\n";);
            pob* new_pob = n.pt().mk_pob(&n, n.level(), n.depth(), mk_and(ua_pob), n.get_binding());
            m_refs.reset();
            return new_pob;
        }
        //computes bounds on each variable in e_and. If the variable is a substitution for a term, the bound on the variable is a bound on the term.
        void ua_formula(expr_ref_vector e_and,model_ref model,expr_expr_map& lb,expr_expr_map& ub,expr_expr_map* sub = nullptr) {
            SASSERT(ub.size()==0);
            SASSERT(lb.size()==0);
            for(unsigned i =0 ; i < e_and.size();i++) {
                expr* temp = e_and.get(i);
                SASSERT(is_app(temp) && is_arith(to_app(temp)));
                app_ref rewrite(m);
                if(m.is_not(to_app(temp)))
                    push_not(to_app(temp),rewrite);
                else
                    rewrite=to_app(temp);
                app_ref normalized_expr(m);
                normalize_le(rewrite,normalized_expr);
                TRACE("under_approximate", tout<< "literal is "<< mk_pp(temp,m)<<" normalized literal is " << mk_pp(normalized_expr,m)<< " LHS is "<< mk_pp(getLHS(normalized_expr),m)<<" RHS is " << mk_pp(getRHS(normalized_expr),m) <<"\n";);

                expr_ref_vector phi(m);
                for(unsigned j=0;j<e_and.size();j++) {
                    if(j!=i) phi.push_back(&(*(e_and.get(j))));
                }

                if(phi.size() == 0) phi.push_back(m.mk_true());
                expr_expr_map t_lb,t_ub;
                ua_literal(model,normalized_expr,phi,t_lb,t_ub,sub);
                expr_expr_map::iterator itr = t_lb.begin();
                while(itr != t_lb.end()) {
                    expr* const var = itr->m_key;
                    lb.insert_if_not_there(var,itr->m_value);
                    if(is_less_than(lb[var],itr->m_value))
                        lb[var]=itr->m_value;
                    itr++;
                }
                itr = t_ub.begin();
                while(itr != t_ub.end()) {
                    expr* const var = itr->m_key;
                    ub.insert_if_not_there(var,itr->m_value);
                    if(is_less_than(itr->m_value,ub[var]))
                        ub[var]=itr->m_value;
                    itr++;
                }
            }
        }
        bool is_disjoint(app* g1, app* g2) {
            expr_ref_vector v1(m),v2(m);
            get_uninterp_consts(g1, v1);
            get_uninterp_consts(g2, v2);
            for(expr* p : v1) {
                for(expr* q : v2) {
                    if(p->get_id() == q->get_id())
                        return false;
                }
            }
            return true;
        }
        bool is_disjoint(expr_ref_vector group) {
            for(unsigned i = 0 ; i < group.size() ; i++) {
                for(unsigned j = i+1; j < group.size() ;j++) {
                        SASSERT(is_app(group.get(i)));
                        SASSERT(is_app(group.get(j)));
                        if(!is_disjoint(to_app(group.get(i)),to_app(group.get(j))))
                            return false;
                    }
            }
            return true;
        }
        //takes as input a conjunction of literals expr, a satisfying assignment m
        //and a set of disjoint groups
        void group(expr_ref_vector pob,expr_ref_vector groups,model_ref model,expr_ref_vector& ua_pob) {
            TRACE("under_approximate", tout<< "grouping an arithmetic pob : "; for(expr * e : pob) tout<<mk_pp(e,m)<<" ";tout<<"\n"; );
            TRACE("under_approximate", tout<< "groups are : "; for(expr * e : groups) tout<<mk_pp(e,m)<<" ";tout<<"\n"; );
            expr_ref pob_sub(m);
            SASSERT(is_sop(pob));
            SASSERT(is_disjoint(groups));
            SASSERT(can_group(pob,groups));
            //TODO ensure union of groups has all the variables
            expr_safe_replace s(m);
            expr_ref_vector variables(m);
            expr_expr_map sub;
            expr_ref_vector fresh_consts(m);
            for(expr* group : groups) {
                /* SASSERT(is_sub_expr(group,pob)); */
                expr_ref eval_ref = (*model)(&(*group));
                SASSERT(m_arith.is_numeral(eval_ref));
                fresh_consts.push_back(m.mk_fresh_const("sub_temp",m_arith.mk_int()));
                s.insert(group,fresh_consts.back());
                sub.insert(fresh_consts.back(),group);
            }
            s(mk_and(pob),pob_sub);
            TRACE("under_approximate", tout<< "substituted pob : "<<mk_pp(pob_sub,m)<<"\n"; );
            expr_expr_map lb,ub;
            expr_ref_vector pob_sub_vec(m);
            flatten_and(pob_sub,pob_sub_vec);
            ua_formula(pob_sub_vec,model,lb,ub,&sub);
            get_uninterp_consts(pob_sub,variables);
            for(expr* variable : variables) {
                if(lb.contains(variable))
                    ua_pob.push_back(m_arith.mk_ge(sub[variable],lb[variable]));
                if(ub.contains(variable))
                    ua_pob.push_back(m_arith.mk_le(sub[variable],ub[variable]));
            }
            fresh_consts.reset();
            TRACE("under_approximate", tout<< "split pob : "<<mk_pp(mk_and(ua_pob),m)<<"\n"; );
        }
        // checks whether c \in g
        bool contains(expr_ref_vector g, expr* c) {return g.contains(c);}

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
        bool is_constant(expr* e) {return is_uninterp_const(e) || m_arith.is_numeral(e) ;}
        bool is_sop(expr_ref_vector e) {
            for(expr* e_child : e)
                if(!is_sop(e_child))
                    return false;
            return true;
        }
        //checks whether arithmetic expression e is a sum of products
        //assumes that all the terms are on the lhs and the rhs is just a numeral
        bool is_sop(expr* e) {
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
            if(!m_arith.is_add(lhs) && !is_constant(lhs)) {
                if (!m_arith.is_mul(lhs)) return false;
                // all arguments for the product should be constants. 
                for(expr* term_child : *to_app(lhs))
                    if(!is_constant(term_child))
                        return false;
            }
            //all terms inside have to be either a constant or a product of constants
            SASSERT(is_app(lhs));
            for(expr* term : *to_app(lhs)) {
                if(m_arith.is_mul(term)) {
                    // all arguments for the product should be constants. 
                    for(expr* term_child : *to_app(term)) {
                        if(!is_constant(term_child))
                            return false;
                    }
                }
                else if(!is_constant(term))
                    return false;
            }
            return true;
        }
        //returns true when each expression in group is either a sub expr of any of
        //the literals in exp or not in any of the literals of exp
        bool can_group(expr_ref_vector exp, expr_ref_vector group)
        {
            //assuming exp is an and of its arguments.
            for(expr* temp : group) {
                if(!can_group(exp,temp))
                    return false;
            }
            return true;
        }
        bool can_group(expr_ref_vector exp,expr* sub_expr) {
            return true;
        }
    };
}
