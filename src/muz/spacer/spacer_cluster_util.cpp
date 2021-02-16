/**++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

    spacer_cluster_util.cpp

Abstract:

   Utility methods for clustering

Author:

    Hari Govind
    Arie Gurfinkel

Notes:

--*/

#include "ast/arith_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/th_rewriter.h"
#include "muz/spacer/spacer_util.h"

namespace {
/// Returns true if \p f is an arithmetic <=, <, >, >=
bool is_arith_ineq(expr *f, expr *&lhs, expr *&rhs, ast_manager &m) {
    arith_util m_arith(m);
    if (!(m_arith.is_arith_expr(f) && to_app(f)->get_num_args() == 2))
        return false;
    return m_arith.is_gt(f, lhs, rhs) || m_arith.is_ge(f, lhs, rhs) ||
           m_arith.is_le(f, lhs, rhs) || m_arith.is_lt(f, lhs, rhs);
}
} // namespace

namespace spacer {
/// Arithmetic term order
struct arith_add_less_proc {
    arith_util &m_arith;

    arith_add_less_proc(arith_util &arith) : m_arith(arith) {}

    bool operator()(expr *e1, expr *e2) const {
        if (e1 == e2) return false;

        ast_lt_proc ast_lt;
        expr *k1 = nullptr, *t1 = nullptr, *k2 = nullptr, *t2 = nullptr;

        // k1*t1 < k2*t2 iff  t1 < t2 or  t1 == t2 && k1 < k2
        // k1 and k2 can be null

        if (!m_arith.is_mul(e1, k1, t1)) { t1 = e1; }
        if (!m_arith.is_mul(e2, k2, t2)) { t2 = e2; }

        SASSERT(t1 && t2);
        if (t1 != t2) return ast_lt(t1, t2);

        //  here: t1 == t2 && k1 != k2
        SASSERT(k1 != k2);

        // check for null
        if (!k1 || !k2) return !k1;
        return ast_lt(k1, k2);
    }
};

struct bool_and_less_proc {
    ast_manager &m;
    arith_util m_arith;
    bool_and_less_proc(ast_manager &mgr, arith_util &arith)
        : m(mgr), m_arith(arith) {}

    bool operator()(expr *e1, expr *e2) const {
        expr *a1 = nullptr, *a2 = nullptr;
        bool is_not1, is_not2;
        if (e1 == e2) return false;

        is_not1 = m.is_not(e1, a1);
        a1 = is_not1 ? a1 : e1;
        is_not2 = m.is_not(e2, a2);
        a2 = is_not2 ? a2 : e2;

        return a1 == a2 ? is_not1 < is_not2 : arith_lt(a1, a2);
    }

    bool arith_lt(expr *e1, expr *e2) const {
        ast_lt_proc ast_lt;
        expr *t1, *k1, *t2, *k2;

        if (e1 == e2) return false;

        if (!(m_arith.is_le(e1, t1, k1) || m_arith.is_lt(e1, t1, k1) ||
              m_arith.is_ge(e1, t1, k1) || m_arith.is_gt(e1, t1, k1))) {
            t1 = e1;
            k1 = nullptr;
        }
        if (!(m_arith.is_le(e2, t2, k2) || m_arith.is_lt(e2, t2, k2) ||
              m_arith.is_ge(e2, t2, k2) || m_arith.is_gt(e2, t2, k2))) {
            t2 = e2;
            k2 = nullptr;
        }

        if (!k1 || !k2) { return k1 == k2 ? ast_lt(t1, t2) : k1 < k2; }

        if (t1 == t2) return ast_lt(k1, k2);

        if (!(is_app(t1) && is_app(t2))) {
            return is_app(t1) == is_app(t2) ? ast_lt(t1, t2)
                                            : is_app(t1) < is_app(t2);
        }

        unsigned d1 = to_app(t1)->get_depth();
        unsigned d2 = to_app(t2)->get_depth();
        if (d1 != d2) return d1 < d2;

        // AG: order by the leading uninterpreted constant
        expr *u1 = nullptr, *u2 = nullptr;

        u1 = get_first_uc(t1);
        u2 = get_first_uc(t2);
        if (!u1 || !u2) { return u1 == u2 ? ast_lt(t1, t2) : u1 < u2; }
        return u1 == u2 ? ast_lt(t1, t2) : ast_lt(u1, u2);
    }

    /// Returns first in left-most traversal uninterpreted constant of \p e
    ///
    /// Returns null when no uninterpreted constant is found.
    /// Recursive, assumes that expression is shallow and recursion is bounded.
    expr *get_first_uc(expr *e) const {
        expr *t, *k;
        if (is_uninterp_const(e))
            return e;
        else if (m_arith.is_add(e)) {
            if (to_app(e)->get_num_args() == 0) return nullptr;
            expr *a1 = to_app(e)->get_arg(0);
            // HG: for 3 + a, returns nullptr
            return get_first_uc(a1);
        } else if (m_arith.is_mul(e, k, t)) {
            return get_first_uc(t);
        }
        return nullptr;
    }
};

// Rewriter for normalize_order()
struct term_ordered_rpp : public default_rewriter_cfg {
    ast_manager &m;
    arith_util m_arith;
    arith_add_less_proc m_add_less;
    bool_and_less_proc m_and_less;

    term_ordered_rpp(ast_manager &man)
        : m(man), m_arith(m), m_add_less(m_arith), m_and_less(m, m_arith) {}

    bool is_add(func_decl const *n) const {
        return is_decl_of(n, m_arith.get_family_id(), OP_ADD);
    }

    br_status reduce_app(func_decl *f, unsigned num, expr *const *args,
                         expr_ref &result, proof_ref &result_pr) {
        br_status st = BR_FAILED;

        if (is_add(f)) {
            ptr_buffer<expr> kids;
            kids.append(num, args);
            std::stable_sort(kids.c_ptr(), kids.c_ptr() + kids.size(),
                             m_add_less);
            result = m_arith.mk_add(num, kids.c_ptr());
            return BR_DONE;
        }

        if (m.is_and(f)) {
            ptr_buffer<expr> kids;
            kids.append(num, args);
            std::stable_sort(kids.c_ptr(), kids.c_ptr() + kids.size(),
                             m_and_less);
            result = m.mk_and(num, kids.c_ptr());
            return BR_DONE;
        }
        return st;
    }
};

// Normalize an arithmetic expression using term order
void normalize_order(expr *e, expr_ref &out) {
    params_ref params;
    // -- arith_rewriter params
    params.set_bool("sort_sums", true);
    // params.set_bool("gcd_rounding", true);
    // params.set_bool("arith_lhs", true);
    // -- poly_rewriter params
    // params.set_bool("som", true);
    // params.set_bool("flat", true);

    // apply theory rewriter
    th_rewriter rw(out.m(), params);
    rw(e, out);

    STRACE("spacer_normalize_order'",
           tout << "OUT Before:" << mk_pp(out, out.m()) << "\n";);
    // apply term ordering
    term_ordered_rpp t_ordered(out.m());
    rewriter_tpl<term_ordered_rpp> t_ordered_rw(out.m(), false, t_ordered);
    t_ordered_rw(out.get(), out);
    STRACE("spacer_normalize_order'",
           tout << "OUT After :" << mk_pp(out, out.m()) << "\n";);
}

/// Under approximate arithmetic inequality
///
/// Returns true if there are \p t and \p c such that (t <= c) ==> lit
/// Supports both Reals and Ints
bool under_approx_using_le(expr *lit, expr_ref &t, expr_ref &c) {
    // t <= c   <==> lit  if lit : Int
    // t <= c    ==> lit  if lit : Real
    ast_manager &m = t.get_manager();
    arith_util m_arith(m);

    expr *e0 = nullptr, *e1 = nullptr, *e2 = nullptr;
    rational n;
    bool is_int = true;
    bool is_not = m.is_not(lit, e0);
    if (!is_not) e0 = lit;

    if (!is_arith_ineq(e0, e1, e2, m)) return false;

    if (!m_arith.is_numeral(e2, n, is_int)) return false;

    t = e1;
    if ((!is_not && m_arith.is_le(e0)) || (is_not && m_arith.is_gt(e0)))
        c = e2;
    else if ((!is_not && m_arith.is_lt(e0)) || (is_not && m_arith.is_ge(e0))) {
        // t < n <== t <= (n-1)
        c = m_arith.mk_numeral(n - 1, is_int);
    } else if ((!is_not && m_arith.is_gt(e0)) ||
               (is_not && m_arith.is_le(e0))) {
        // t > n <== -t <= -n - 1
        mul_by_rat(t, rational::minus_one());
        c = m_arith.mk_numeral(-n - 1, is_int);
    } else if ((!is_not && m_arith.is_ge(e0)) ||
               (is_not && m_arith.is_lt(e0))) {
        // t >= n <== -t <= -n
        mul_by_rat(t, rational::minus_one());
        c = m_arith.mk_numeral(-n, is_int);
    }
    SASSERT(c.get());
    return true;
}

/// Multiply an expression \p fml by a rational \p num
///
/// \p fml should be of sort Int, Real, or BitVec
/// multiplication is simplifying
void mul_by_rat(expr_ref &fml, rational num) {
    if (num.is_one()) return;

    ast_manager &m = fml.get_manager();
    arith_util m_arith(m);
    bv_util m_bv(m);
    expr_ref e(m);
    SASSERT(m_arith.is_int_real(fml) || m_bv.is_bv(fml));
    if (m_arith.is_int_real(fml)) {
        e = m_arith.mk_mul(m_arith.mk_numeral(num, m_arith.is_int(fml)), fml);
    } else if (m_bv.is_bv(fml)) {
        unsigned sz = m_bv.get_bv_size(fml);
        e = m_bv.mk_bv_mul(m_bv.mk_numeral(num, sz), fml);
    }

    // use theory rewriter to simplify
    params_ref params;
    params.set_bool("som", true);
    params.set_bool("flat", true);
    th_rewriter rw(fml.m(), params);
    rw(e, fml);
}

namespace extract_nums_ns {

/// Extract numerals from an expression
struct extract_nums_proc {
    ast_manager &m;
    arith_util m_arith;
    vector<rational> &m_res;
    extract_nums_proc(ast_manager &a_m, vector<rational> &res)
        : m(a_m), m_arith(m), m_res(res) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        rational val;
        if (m_arith.is_numeral(n, val)) m_res.push_back(val);
    }
};
} // namespace extract_nums_ns

/// Extract all numerals from an expression
void extract_nums(expr_ref e, vector<rational> &res) {
    extract_nums_ns::extract_nums_proc proc(e.get_manager(), res);
    // assuming for_each_expr is caching, this is linear in the dag size of e
    for_each_expr(proc, e);
}
} // namespace spacer
template class rewriter_tpl<spacer::term_ordered_rpp>;