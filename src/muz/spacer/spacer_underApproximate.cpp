#include "spacer_underApproximate.h"
namespace spacer {
// propagates negation
// (not (<= a 5)) == (> a 5)
void under_approx::push_not(expr_ref &res) {
    expr *e = res.get();
    expr *e1, *e2;
    if (m_arith.is_le(e, e1, e2)) {
        res = m_arith.mk_gt(e1, e2);
    }
    else if  (m_arith.is_lt(e, e1, e2)) {
        res = m_arith.mk_ge(e1, e2);
    }
    else if (m_arith.is_ge(e, e1, e2)) {
        res = m_arith.mk_lt(e1, e2);
    }
    else if (m_arith.is_gt(e, e1, e2)) {
        res = m_arith.mk_le(e1, e2);
    }
    else {
        push_not(res);
    }
}

// normalizes expression to be a le with variables on the lhs and numeral on
// the rhs works only on integar arithmetic
void under_approx::normalize_le(expr *e, expr_ref &res) {
    // XXX this is probably not the right thing to do.
    // XXX Need to examine how it is used
    // works only for integers. Need to assert that as well
    SASSERT(m_arith.is_arith_expr(e));
    app *minus_one = m_arith.mk_int(-1);
    expr *e1, *e2;
    if (m_arith.is_lt(e, e1, e2))
        res = m_arith.mk_le(e1, m_arith.mk_add(e2, minus_one));
    else if (m_arith.is_ge(e, e1, e2))
        res = m_arith.mk_le(m_arith.mk_mul(e1, minus_one),
                            m_arith.mk_mul(e2, minus_one));
    else if (m_arith.is_gt(e, e1, e2))
        res = m_arith.mk_le(
            m_arith.mk_mul(e1, minus_one),
            m_arith.mk_add(m_arith.mk_mul(e2, minus_one), minus_one));
    else {
        SASSERT(m_arith.is_le(e));
        res = e;
    }

    // simplify result.
    // XXX should ensure that result is constructed simplified
    // XXX This might rewrite expressions back to their normal form undoing the
    // above
    // th_rewriter rw(res.get_manager());
    // rw(res);
}

/*
   computes the coeff of var in l. Returns false if var not in l
   assumes that there is only occurrence of var in l
   should be of the form -1*(ax+by+..) or (ax+by+...)
   assumes that the coeff is initialized to an appropriate value
 */
bool under_approx::get_coeff(expr *l, const expr *var, rational &coeff) {
    // XXX coeff might be uninitialized when true is returned!

    // If its an uninterpreted constant, the coeff is not going to change
    if (is_uninterp_const(l)) return l == var;

    if (!is_app(l)) return false;
    if (!m_arith.is_arith_expr(l)) return false;
    if (m_arith.is_numeral(l)) return false;

    SASSERT(m_arith.is_arith_expr(l));
    SASSERT(m_arith.is_add(l) || m_arith.is_mul(l));
    expr *e1, *e2;
    if (m_arith.is_mul(l, e1, e2)) {
        // expect linear multiplication
        if (!m_arith.is_numeral(e1) && !m_arith.is_numeral(e2)) return false;
        // expect first argument to be numeric
        if (!m_arith.is_numeral(e1)) std::swap(e1, e2);
        if (get_coeff(e2, var, coeff)) {
            rational n;
            m_arith.is_numeral(e1, n);
            coeff = coeff * n;
            return true;
        }
        return false;
    }

    // !is_mul(l)
    for (expr *e : *to_app(l)) {
        if (e == var)
            return true;
        else if (is_app(e) && (to_app(e))->get_num_args() > 1) {
            // XXX comment why recursion is bounded and why caching is not
            // XXX needed
            if (get_coeff(e, var, coeff)) return true;
        }
    }
    return false;
}

// returns whether l increases(1), decreases(-1) or doesn't change(0) with
// var
int under_approx::ua_variable(expr_ref l, expr *u_const) {
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
    // XXX This function hides a problem in the design
    // XXX Upper/lower bounds should be kept as integer constants,
    // XXX and not as expressions
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
void under_approx::ua_literal(model_ref model, expr_ref l, expr_ref_vector &phi,
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
void under_approx::ua_formula(const expr_ref_vector &conj, model_ref model,
                               expr_expr_map &lb, expr_expr_map &ub,
                               expr_expr_map *sub) {
    SASSERT(ub.size() == 0);
    SASSERT(lb.size() == 0);
    for (expr *lit : conj) {
        SASSERT(is_app(lit) && is_arith(to_app(lit)));

        // normalize temp. Rewrite to be of <= form
        expr_ref normalized_lit(m);
        normalized_lit = lit;
        expr *e1;
        if (m.is_not(normalized_lit, e1)) {
            normalized_lit = e1;
            push_not(normalized_lit);
        }
        // XXX instead of normalizing the lit, this code should
        // XXX return (lhs, rhs) such that lhs <= rhs is equivalent to
        // XXX the original literal. There is no need to construct the resulting
        // XXX expression. Furthermore, rhs must be a rational.
        // XXX This will also eliminate the need for push_not()
        normalize_le(normalized_lit, normalized_lit);

        TRACE("under_approximate",
              tout << "literal is " << mk_pp(lit, m)
                   << " normalized literal is " << normalized_lit << " LHS is "
                   << mk_pp(getLHS(normalized_lit), m) << " RHS is "
                   << mk_pp(getRHS(normalized_lit), m) << "\n";);

        // conj of all other literals
        expr_ref_vector phi(m);
        for (expr *t : conj) {
            if (t != lit) phi.push_back(t);
        }
        if (phi.empty()) phi.push_back(m.mk_true());

        // under approximate the literal
        expr_expr_map t_lb, t_ub;
        ua_literal(model, normalized_lit, phi, t_lb, t_ub, sub);

        // strengthen bounds
        for (auto it = t_lb.begin(); it != t_lb.end(); ++it) {
            auto *var = it->m_key;
            lb.insert_if_not_there(var, it->m_value);
            if (is_less_than(lb[var], it->m_value))
                lb[var] = it->m_value;
        }
        for (auto it = t_ub.begin(); it != t_ub.end(); ++it) {
            auto *var = it->m_key;
            ub.insert_if_not_there(var, it->m_value);
            if (is_less_than(it->m_value, ub[var]))
                ub[var] = it->m_value;
        }
   }
}
} // namespace spacer
