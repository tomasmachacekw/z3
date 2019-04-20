#include "spacer_underApproximate.h"
namespace spacer {
// propagates negation
// (not (<= a 5)) == (> a 5)
void under_approx::push_not(app *e, app_ref &result) {
    SASSERT(m.is_not(e));
    SASSERT(is_arith(e));
    app *arg = to_app(e->get_arg(0));
    expr *term = getLHS(arg);
    expr *constant = getRHS(arg);
    SASSERT(is_uninterp_const(term) || m_arith.is_arith_expr(term));
    SASSERT(m_arith.is_numeral(constant));
    if (m_arith.is_le(arg))
        result = m_arith.mk_gt(term, constant);
    else if (m_arith.is_lt(arg))
        result = m_arith.mk_ge(term, constant);
    else if (m_arith.is_ge(arg))
        result = m_arith.mk_lt(term, constant);
    else if (m_arith.is_gt(arg))
        result = m_arith.mk_le(term, constant);
    else
        SASSERT(false);
}

// normalizes expression to be a le with variables on the lhs and numeral on
// the rhs works only on integar arithmetic
void under_approx::normalize_le(app *e, app_ref &result) {
    // works only for integers. Need to assert that as well
    SASSERT(m_arith.is_arith_expr(e));
    expr *lhs = getLHS(e);
    expr *rhs = getRHS(e);
    app *minus_one = m_arith.mk_int(-1);
    if (m_arith.is_lt(e))
        result = m_arith.mk_le(lhs, m_arith.mk_add(rhs, minus_one));
    else if (m_arith.is_ge(e))
        result = m_arith.mk_le(m_arith.mk_mul(lhs, minus_one),
                               m_arith.mk_mul(rhs, minus_one));
    else if (m_arith.is_gt(e))
        result = m_arith.mk_le(
            m_arith.mk_mul(lhs, minus_one),
            m_arith.mk_add(m_arith.mk_mul(rhs, minus_one), minus_one));
    else {
        SASSERT(m_arith.is_le(e));
        result = m_arith.mk_le(lhs, rhs);
    }

    // simplify result. XXX should ensure that result is constructed
    // simplified
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
bool under_approx::get_coeff(app *l, const expr *var, rational &coeff) {
    // XXX coeff might be uninitialized when true is returned!

    // If its an uninterpreted constant, the coeff is not going to change
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
        } else {
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
    for (expr *e : *l) {
        if (e == var)
            return true;
        else if (is_app(e) && (to_app(e))->get_num_args() > 1) {
            // XXX comment why recursion is bounded and why caching is not
            // needed
            if (get_coeff(to_app(e), var, coeff)) return true;
        }
    }
    return false;
}

// returns whether l increases(1), decreases(-1) or doesn't change(0) with
// var
int under_approx::ua_variable(app_ref l, expr *u_const) {
    rational coeff(1);
    expr *lhs = getLHS(l);
    // lhs is in the sum of products form (ax + by)
    SASSERT(is_app(lhs));
    get_coeff(to_app(lhs), u_const, coeff);
    SASSERT(coeff.is_int());

    TRACE("under_approximate_verb", tout << "coefficient found "
                                         << mk_pp(u_const, m) << " in literal "
                                         << l << " is " << coeff << "\n";);
    if (coeff.is_pos())
        return 1;
    else if (coeff.is_neg())
        return -1;
    else
        SASSERT(coeff.is_zero());
    return 0;
}

// true if numeral(a) < numeral(b)
bool under_approx::is_less_than(expr const *a, expr const *b) {
    SASSERT(a);
    SASSERT(b);
    rational a_rat, b_rat;
    m_arith.is_numeral(a, a_rat);
    m_arith.is_numeral(b, b_rat);
    SASSERT(a_rat.is_int());
    SASSERT(b_rat.is_int());
    return a_rat < b_rat;
}

// computes bounds u_v on each variable v in l
// phi ==> ( &u_v ==> l)
void under_approx::ua_literal(model_ref model, app_ref l, expr_ref_vector phi,
                              expr_expr_map &lb, expr_expr_map &ub,
                              expr_expr_map *sub) {
    expr_ref bnd(m);
    SASSERT(lb.size() == 0);
    SASSERT(ub.size() == 0);

    expr_ref_vector u_consts(m);
    get_uninterp_consts(l, u_consts);

    // TODO : compute the orthogonal projection
    for (expr *u_const : u_consts) {
        // compute variation of l with u_const
        int change = ua_variable(l, u_const);
        if (sub)
            bnd = (*model)((*sub)[u_const]);
        else
            bnd = (*model)(u_const);
        SASSERT(m_arith.is_numeral(bnd));

        // save reference since the map won't do it
        m_refs.push_back(bnd);

        if (change == 1) {
            ub.insert(u_const, bnd.get());
            TRACE("under_approximate_verb",
                  tout << "upper bounds for " << mk_pp(u_const, m) << " is "
                       << mk_pp(ub[u_const], m) << "\n";);
        } else if (change == -1) {
            lb.insert(u_const, bnd.get());
            TRACE("under_approximate_verb",
                  tout << "lower bounds for " << mk_pp(u_const, m) << " is "
                       << mk_pp(lb[u_const], m) << "\n";);
        }
    }
}

// under approximate proof obligation n using literals of dim 1
// returns nullptr if pob is not in LA
pob *under_approx::under_approximate(pob &n, model_ref model) {
    expr *pob_exp = to_app(n.post());
    expr_ref_vector u_consts(m);
    get_uninterp_consts(pob_exp, u_consts);
    expr_ref_vector ua_pob(m);
    expr_ref_vector conj(m);

    SASSERT(is_app(pob_exp));
    flatten_and(pob_exp, conj);

    // if the literals are not in LA, return nullptr
    for (auto e : conj)
        if (!(is_app(e) && is_arith(to_app(e)))) return nullptr;

    expr_expr_map lb, ub;

    // compute bounds
    ua_formula(conj, model, lb, ub);

    // create under approximation
    for (expr *u_const : u_consts) {
        if (lb.contains(u_const))
            ua_pob.push_back(m_arith.mk_ge(u_const, lb[u_const]));
        if (ub.contains(u_const))
            ua_pob.push_back(m_arith.mk_le(u_const, ub[u_const]));
    }

    TRACE("under_approximate", tout << "produced an arithmetic pob: "
                                    << mk_pp(mk_and(ua_pob), m) << "\n";);
    pob *new_pob = n.pt().mk_pob(&n, n.level(), n.depth(), mk_and(ua_pob),
                                 n.get_binding());
    m_refs.reset();
    return new_pob;
}

// computes bounds on each uninterp_const in e_and. If the uninterp_const is
// a an alias for a term, the bound on the uninterp_const is a bound on the
// term.
void under_approx::ua_formula(expr_ref_vector conj, model_ref model,
                              expr_expr_map &lb, expr_expr_map &ub,
                              expr_expr_map *sub) {
    SASSERT(ub.size() == 0);
    SASSERT(lb.size() == 0);
    for (expr *lit : conj) {
        SASSERT(is_app(lit) && is_arith(to_app(lit)));

        // normalize temp. Rewrite to be of <= form
        app_ref rewrite(m);
        if (m.is_not(to_app(lit)))
            push_not(to_app(lit), rewrite);
        else
            rewrite = to_app(lit);
        app_ref normalized_lit(m);
        normalize_le(rewrite, normalized_lit);

        TRACE("under_approximate",
              tout << "literal is " << mk_pp(lit, m)
                   << " normalized literal is " << mk_pp(normalized_lit, m)
                   << " LHS is " << mk_pp(getLHS(normalized_lit), m)
                   << " RHS is " << mk_pp(getRHS(normalized_lit), m) << "\n";);

        // conj of all other literals
        expr_ref_vector phi(m);
        for (expr *t : conj) {
            if (t != lit) phi.push_back(t);
        }
        if (phi.size() == 0) phi.push_back(m.mk_true());

        // under approximate the literal
        expr_expr_map t_lb, t_ub;
        ua_literal(model, normalized_lit, phi, t_lb, t_ub, sub);

        // strengthen bounds
        expr_expr_map::iterator itr = t_lb.begin();
        while (itr != t_lb.end()) {
            expr *const var = itr->m_key;
            lb.insert_if_not_there(var, itr->m_value);
            if (is_less_than(lb[var], itr->m_value)) lb[var] = itr->m_value;
            itr++;
        }
        itr = t_ub.begin();
        while (itr != t_ub.end()) {
            expr *const var = itr->m_key;
            ub.insert_if_not_there(var, itr->m_value);
            if (is_less_than(itr->m_value, ub[var])) ub[var] = itr->m_value;
            itr++;
        }
    }
}
} // namespace spacer
