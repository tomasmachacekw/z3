#include "spacer_underApproximate.h"
namespace spacer {

bool under_approx::is_arith(expr *e)
{
    // XXX AG: not sure it returns true for arithmetic uninterpreted constants
    expr *arg;
    if (!is_app(e)) return false;
    expr *e1, *e2;
    if (m.is_eq(e, e1, e2)) return m_arith.is_arith_expr(e1);
    return m.is_not(e, arg) ? is_arith(arg) : m_arith.is_arith_expr(e);
}

// under approximate proof obligation n using literals of dim 1
// returns nullptr if pob is not in LA
  bool under_approx::under_approximate(expr *f, model_ref &model, expr_ref_vector &under_approx_vec) {
    SASSERT(is_app(f));

    expr_ref_vector u_consts(m);
    get_uninterp_consts(f, u_consts);

    expr_ref_vector conj(m);
    flatten_and(f, conj);

    // if the literals are not in LA, return nullptr
    for (auto e : conj) {
        if (!is_arith(e)) return false;
    }

    expr_expr_map lb, ub;

    // compute bounds
    under_approx_cube(conj, model, lb, ub);

    // create under approximation
    for (expr *u : u_consts) {
        if (lb.contains(u)) under_approx_vec.push_back(m_arith.mk_ge(u, lb[u]));
        if (ub.contains(u)) under_approx_vec.push_back(m_arith.mk_le(u, ub[u]));
    }

    TRACE("under_approximate",
          tout << "produced an under approximation : " << mk_and(under_approx_vec) << "\n";);
    m_refs.reset();
    return ( !under_approx_vec.empty() );
}

bool under_approx::is_le(expr *lit, expr_ref &t, expr_ref &c) {
    expr *e0 = nullptr, *e1 = nullptr, *e2 = nullptr;
    rational n;
    bool is_int = true;
    if (m_arith.is_le(lit, e1, e2) ||
        (m.is_not(lit, e0) && m_arith.is_gt(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n)) {
            t = e1;
            c = e2;
            return true;
        } else {
            // XXX handle if needed
            return false;
        }
    } else if (m_arith.is_lt(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_ge(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n, is_int)) {
            // x < k  ==> x <= (k-1)
            t = e1;
            c = m_arith.mk_numeral(n - 1, is_int);
            return true;
        } else {
            return false;
        }
    } else if (m_arith.is_gt(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_le(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n, is_int)) {
            // x > k ==> -x < -k ==> -x <= -k - 1
            expr_ref minus_one(m);
            minus_one = m_arith.mk_numeral(-1, is_int);
            t = m_arith.mk_mul(minus_one, e1);
            c = m_arith.mk_numeral(-n - 1, is_int);
            return true;
        } else {
            return false;
        }
    } else if (m_arith.is_ge(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_lt(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n, is_int)) {
            // x >= k ==> -x <= -k
            expr_ref minus_one(m);
            minus_one = m_arith.mk_numeral(-1, is_int);
            t = m_arith.mk_mul(minus_one, e1);
            c = m_arith.mk_numeral(-n, is_int);
            return true;
        } else {
            return false;
        }
    }

    return false;
}

  //Expects t to be in sum of products form or -1*(sum of products) form
bool under_approx::find_coeff(expr *t, expr *v, rational &k, bool negated) {
    expr *e1 = nullptr, *e2 = nullptr;
    rational n;

    if (t == v) {
        k = rational(negated ? -1 : 1);
        return true;
    } else if (m_arith.is_add(t)) {
        bool res = false;
        for (expr *e : *to_app(t)) {
            res = find_coeff(e, v, k, negated);
            if (res) return true;
        }
    } else if (m_arith.is_mul(t, e1, e2)) {
        if (m_arith.is_numeral(e2)) std::swap(e1, e2);
        if (e2 == v) {
            bool res = m_arith.is_numeral(e1, k);
            if (res && negated) k = -1 * k;
            return res;
        } else if (m_arith.is_numeral(e1, n) && n == rational(-1)) {
            return find_coeff(e2, v, k, true /*negated*/);
        }
    }
    return false;
}

// returns whether l increases(1), decreases(-1) or doesn't change(0) with
// var
int under_approx::under_approx_var(expr *t, expr *c, expr *d) {
    rational coeff;
    // lhs is in the sum of products form (ax + by)
    VERIFY(find_coeff(t, d, coeff));
    SASSERT(coeff.is_int());

    TRACE("under_approximate_verb", tout << "coefficient of " << mk_pp(d, m)
                                         << " in term " << mk_pp(t, m) << " is "
                                         << coeff << "\n";);
    if (coeff.is_pos())
        return 1;
    else if (coeff.is_neg())
        return -1;
    else {
        SASSERT(coeff.is_zero());
        return 0;
    }
}
// computes bounds u_v on each variable v in l
// bg ==> ( &u_v ==> l)
void under_approx::under_approx_lit(model_ref &model, expr *t, expr *c,
                                    expr_ref_vector &bg, expr_expr_map &lb,
                                    expr_expr_map &ub, expr_expr_map *sub) {
    expr_ref val(m);
    SASSERT(lb.size() == 0);
    SASSERT(ub.size() == 0);

    expr_ref_vector dims(m);
    get_uninterp_consts(t, dims);

    for (expr *d : dims) {
        // compute variation of l along dim d
        int change = under_approx_var(t, c, d);
        val = (*model)(sub ? (*sub)[d] : d);
        SASSERT(m_arith.is_numeral(val));

        // save reference since the map won't do it
        m_refs.push_back(val);

        if (change > 0) {
            ub.insert(d, val.get());
            TRACE("under_approximate_verb", tout << "upper bounds for "
                                                 << mk_pp(d, m) << " is "
                                                 << mk_pp(ub[d], m) << "\n";);
        } else if (change < 0) {
            lb.insert(d, val.get());
            TRACE("under_approximate_verb", tout << "lower bounds for "
                                                 << mk_pp(d, m) << " is "
                                                 << mk_pp(lb[d], m) << "\n";);
        }
    }
}

// computes bounds on each uninterp_const in e_and. If the uninterp_const is
// a an alias for a term, the bound on the uninterp_const is a bound on the
// term.
void under_approx::under_approx_cube(const expr_ref_vector &conj,
                                     model_ref &model, expr_expr_map &lb,
                                     expr_expr_map &ub, expr_expr_map *sub) {
    SASSERT(ub.size() == 0);
    SASSERT(lb.size() == 0);
    expr_ref t(m), c(m);
    for (expr *lit : conj) {
        if (is_le(lit, t, c)) {
            TRACE("under_approximate", tout << "literal is " << mk_pp(lit, m)
                                            << "normalized as: " << mk_pp(t, m)
                                            << " <= " << mk_pp(c, m) << "\n";);

            // conj of all other literals
            expr_ref_vector bg(m);
            for (expr *t : conj) {
                if (t != lit) bg.push_back(t);
            }
            if (bg.empty()) bg.push_back(m.mk_true());

            // under approximate the literal
            expr_expr_map t_lb, t_ub;
            under_approx_lit(model, t, c, bg, t_lb, t_ub, sub);

            // update global bounds
            rational n1, n2;
            for (auto &kv : t_lb) {
                auto &data = lb.insert_if_not_there(kv.m_key, kv.m_value);
                if (m_arith.is_numeral(kv.m_value, n1) &&
                    m_arith.is_numeral(data.m_value, n2) && n2 < n1)
                    lb[kv.m_key] = kv.m_value;
            }
            for (auto &kv : t_ub) {
                auto &data = ub.insert_if_not_there(kv.m_key, kv.m_value);
                if (m_arith.is_numeral(kv.m_value, n1) &&
                    m_arith.is_numeral(data.m_value, n2) && n1 < n2)
                    ub[kv.m_key] = kv.m_value;
            }
        }
    }
}

} // namespace spacer
