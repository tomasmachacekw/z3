#include "spacer_underApproximate.h"
namespace {
// checks whether f is a binary operator or the negation of one
bool is_bin_op(expr *f, expr *&lhs, expr *&rhs, ast_manager &m) {
    if (!is_app(f)) return false;
    expr *e;
    if (m.is_not(f, e)) return is_bin_op(e, lhs, rhs, m);
    app *f_app = to_app(f);
    if (f_app->get_num_args() != 2) return false;
    lhs = f_app->get_arg(0);
    rhs = f_app->get_arg(1);
    return true;
}
} // anonymous namespace

bool under_approx::is_sop(expr *e) {
    if (is_constant(e)) return true;
    if (!m_arith.is_arith_expr(e)) return false;

    expr *e1, *e2;
    // cannot have a top level operand other than plus
    if (!m_arith.is_add(e) && !is_constant(e)) {
        // all arguments for the product should be constants.
        if (!(m_arith.is_mul(e, e1, e2) && is_constant(e1) && is_constant(e2)))
            return false;
    }
    // all terms inside have to be either a constant or a product of
    // constants
    for (expr *term : *to_app(e)) {
        // all arguments for the product should be constants.
        if (!((m_arith.is_mul(term, e1, e2) && is_constant(e1) &&
               is_constant(e2)) ||
              is_constant(term)))
            return false;
    }
    return true;
}
bool under_approx::normalize_to_le(expr *lit, expr_ref &t, expr_ref &c) {
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
            UNREACHABLE();
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
            UNREACHABLE();
            return false;
        }
    } else if (m_arith.is_gt(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_le(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n, is_int)) {
            // x > k ==> -x < -k ==> -x <= -k - 1
            expr_ref minus_one(m);
            minus_one = m_arith.mk_numeral(rational(-1), is_int);
            t = m_arith.mk_mul(minus_one, e1);
            c = m_arith.mk_numeral(-n - 1, is_int);
            return true;
        } else {
            UNREACHABLE();
            return false;
        }
    } else if (m_arith.is_ge(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_lt(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n, is_int)) {
            // x >= k ==> -x <= -k
            expr_ref minus_one(m);
            minus_one = m_arith.mk_numeral(rational(-1), is_int);
            t = m_arith.mk_mul(minus_one, e1);
            c = m_arith.mk_numeral(-n, is_int);
            return true;
        } else {
            UNREACHABLE();
            return false;
        }
    }

    return false;
}
