/**++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

    spacer_convex_closure.cpp

Abstract:

   Compute convex closure of polyhedra

Author:

    Hari Govind
    Arie Gurfinkel

Notes:

--*/

#include "muz/spacer/spacer_convex_closure.h"

namespace {
bool is_int_matrix(const spacer::spacer_matrix &matrix) {
    rational val;
    for (unsigned i = 0, rows = matrix.num_rows(); i < rows; i++) {
        for (unsigned j = 0, cols = matrix.num_cols(); j < cols; j++)
            if (!matrix.get(i, j).is_int()) return false;
    }
    return true;
}

bool is_sorted(const vector<rational> &data) {
    for (unsigned i = 0; i < data.size() - 1; i++) {
        if (data[i] < data[i + 1]) return false;
    }
    return true;
}

/// Check whether all elements of \p data are congruent modulo \p m
bool congruent_mod(const vector<rational> &data, rational m) {
    SASSERT(data.size() > 0);
    rational p = data[0] % m;
    for (auto k : data)
        if (k % m != p) return false;
    return true;
}

// TODO: is n-ary bvadd supported in Z3 ?
app *mk_bvadd(ast_manager &m, unsigned num, expr *const *args) {
    if (num == 0) return nullptr;
    if (num == 1) {
        if (!is_app(args[0])) return nullptr;
        return to_app(args[0]);
    }
    bv_util bv(m);
    if (num == 2) { return bv.mk_bv_add(args[0], args[1]); }
    return m.mk_app(bv.get_fid(), OP_BADD, num, args);
}
} // namespace

namespace spacer {

void convex_closure::reset(unsigned n_cols) {
    m_kernel.reset();
    m_data.reset(n_cols);
    m_dim_vars.reset();
    m_dim = n_cols;
    m_dim_vars.reserve(m_dim);
    m_nw_vars.reset();
    m_bv_sz = 0;
    m_do_syn_cls = true;
}

void convex_closure::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.global.cc",
              m_st.watch.get_seconds());
    st.update("SPACER cc num dim reduction success", m_st.m_num_reductions);
    st.update("SPACER cc max reduced dim", m_st.m_max_dim);
    m_kernel.collect_statistics(st);
}

// call m_kernel to reduce dimensions of m_data
// return the rank of m_data
unsigned convex_closure::reduce_dim() {
    if (m_dim <= 1) return m_dim;
    bool has_kernel = m_kernel.compute_kernel();
    if (!has_kernel) {
        TRACE("cvx_dbg",
              tout << "No linear dependencies between pattern vars\n";);
        return m_dim;
    }
    const spacer_matrix &ker = m_kernel.get_kernel();

    SASSERT(ker.num_rows() > 0);
    SASSERT(ker.num_rows() <= m_dim);
    SASSERT(ker.num_cols() == m_dim + 1);
    // m_dim - ker.num_rows() is the number of variables that have no linear
    // dependencies
    return m_dim - ker.num_rows();
}

// For row \p row in m_kernel, construct the equality:
//
// row * m_dim_vars = 0
//
// In the equality, exactly one variable from  m_dim_vars is on the lhs
void convex_closure::generate_lin_deps_for_row(const vector<rational> &row,
                                               expr_ref &res) {
    // contains the right hand side of an equality
    expr_ref_buffer rw(m);
    // index of first non zero element in row
    int pv = -1;
    // are we constructing rhs or lhs
    bool rhs = false;
    // coefficient of m_dim_vars[pv]
    rational coeff(1);
    // the elements in row are the coefficients of m_dim_vars
    // some elements should go to the rhs, in which case the signs are
    // changed
    for (unsigned j = 0; j < row.size(); j++) {
        rational val = row.get(j);
        SASSERT(val.is_int());
        if (val.is_zero()) continue;
        if (!rhs) {
            // Cannot re-write the last element
            if (j == row.size() - 1) continue;
            SASSERT(pv == -1);
            pv = j;
            rhs = true;
            // In integer echelon form, the pivot need not be 1
            coeff = val;
        } else {
            expr_ref prod(m);
            if (j != row.size() - 1) {
                prod = m_dim_vars.get(j);
                mul_by_rat(prod, -1 * val * m_lcm);
            } else {
                if (m_arith.is_int(m_dim_vars.get(pv))) {
                    prod = m_arith.mk_int(-1 * val);
                } else if (m_arith.is_real(m_dim_vars.get(pv))) {
                    prod = m_arith.mk_real(-1 * val);
                } else if (m_bv.is_bv(m_dim_vars.get(pv))) {
                    prod = m_bv.mk_numeral(-1 * val, m_bv_sz);
                }
            }
            SASSERT(prod.get());
            rw.push_back(prod);
        }
    }

    // make sure that there is a non-zero entry
    SASSERT(pv != -1);

    if (rw.size() == 0) {
        expr_ref rhs(m);
        if (m_arith.is_int(m_dim_vars.get(pv)))
            rhs = m_arith.mk_int(rational::zero());
        else if (m_arith.is_real(m_dim_vars.get(pv)))
            rhs = m_arith.mk_real(rational::zero());
        else if (m_bv.is_bv(m_dim_vars.get(pv)))
            rhs = m_bv.mk_numeral(rational::zero(), m_bv_sz);
        res = m_arith.mk_eq(m_dim_vars.get(pv), rhs);
        return;
    }

    res = m_is_arith ? m_arith.mk_add(rw.size(), rw.c_ptr())
                     : mk_bvadd(m, rw.size(), rw.c_ptr());
    expr_ref pv_var(m);
    pv_var = m_dim_vars.get(pv);
    mul_by_rat(pv_var, coeff * m_lcm);

    res = m.mk_eq(pv_var, res);
    TRACE("cvx_dbg", tout << "rewrote " << mk_pp(m_dim_vars.get(pv), m)
                          << " into " << res << "\n";);
}

/// Generates linear equalities implied by m_data
///
/// the linear equalities are m_kernel * m_dim_vars = 0 (where * is matrix multiplication)
/// the new equalities are stored in m_dim_vars
/// for each row [0, 1, 0, 1 , 1] in m_kernel, the equality m_lcm*v1 =
/// -1*m_lcm*v3 + -1*1 is constructed and stored at index 1 of m_dim_vars
void convex_closure::generate_lin_deps(expr_ref_vector &res) {
    // assume kernel has been computed already
    const spacer_matrix &ker = m_kernel.get_kernel();
    unsigned n_rows = ker.num_rows();
    SASSERT(n_rows > 0);
    expr_ref lin_dep(m);

    for (unsigned i = n_rows; i > 0; i--) {
        const vector<rational> &row = ker.get_row(i - 1);
        generate_lin_deps_for_row(row, lin_dep);
        res.push_back(lin_dep);
    }
}

/// Construct the equality ((m_nw_vars . m_data[*][i]) = m_dim_vars[i])
///
/// Where . is the dot product,  m_data[*][i] is
/// the ith column of m_data. Add the result to res_vec.
void convex_closure::add_sum_cnstr(unsigned i, expr_ref_vector &res_vec) {
    expr_ref_vector add(m);
    expr_ref mul(m), result_var(m);
    for (unsigned j = 0; j < m_nw_vars.size(); j++) {
        mul = m_nw_vars.get(j);
        mul_by_rat(mul, m_data.get(j, i));
        add.push_back(mul);
    }
    result_var = m_arith.mk_to_real(m_dim_vars.get(i));
    mul_by_rat(result_var, m_lcm);
    if (m_is_arith)
        res_vec.push_back(
            m.mk_eq(m_arith.mk_add(add.size(), add.c_ptr()), result_var));
    else
        res_vec.push_back(
            m.mk_eq(mk_bvadd(m, add.size(), add.c_ptr()), result_var));
}

void convex_closure::syn_cls(expr_ref_vector &res_vec) {
    for (unsigned i = 0; i < m_data.num_rows(); i++) {
        var_ref v(m.mk_var(i + dims(), m_arith.mk_real()), m);
        m_nw_vars.push_back(v);
    }

    expr_ref_vector exprs(m);
    expr_ref e(m);

    //\forall j . m_nw_vars[j] >= 0
    for (auto v : m_nw_vars) {
        e = expr_ref(to_expr(v), m);
        exprs.push_back(e);
        res_vec.push_back(m_arith.mk_ge(e, m_arith.mk_real(rational::zero())));
    }

    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        e = m_dim_vars.get(i);
        if (is_var(e)) add_sum_cnstr(i, res_vec);
    }

    //(\Sum j . m_nw_vars[j]) = 1
    res_vec.push_back(m.mk_eq(m_arith.mk_add(m_nw_vars.size(), exprs.c_ptr()),
                              m_arith.mk_real(rational::one())));
}

// check whether \exists m, d s.t data[i] mod m = d. Returns the largest m and
// corresponding d
// TODO: find the largest divisor, not the smallest.
// TODO: improve efficiency
bool convex_closure::compute_div_constraint(const vector<rational> &data,
                                            rational &m, rational &d) {
    TRACE("cvx_dbg_verb", tout << "computing div constraints for ";
          for (rational r
               : data) tout
          << r << " ";
          tout << "\n";);
    SASSERT(data.size() > 1);
    SASSERT(is_sorted(data));
    m = rational(2);
    // hard cut off to save time
    rational bnd(100);
    for (; m < data[data.size() - 1] && m < bnd; m++) {
        if (congruent_mod(data, m)) break;
    }
    if (m >= data[data.size() - 1]) return false;
    d = data[0] % m;
    // work around for z3::rational::rem returning negative numbers.
    d = (m + d) % m;
    SASSERT(d >= rational::zero());

    TRACE("cvx_dbg_verb", tout << "div constraint generated. cf " << m
                               << " and off " << d << "\n";);
    return true;
}

/// Compute the convex closure of points in m_data
///
/// Returns true if the convex closure is syntactic
bool convex_closure::closure(expr_ref_vector &res_vec) {
    scoped_watch _w_(m_st.watch);
    SASSERT(is_int_matrix(m_data));
    unsigned red_dim = reduce_dim();
    // store dim var before rewrite
    expr_ref var(m);
    var = m_dim_vars.get(0);
    if (red_dim < dims()) {
        m_st.m_num_reductions++;
        generate_lin_deps(res_vec);
        TRACE("cvx_dbg", tout << "Linear equalities true of the matrix "
                              << mk_and(res_vec) << "\n";);
    }

    if (red_dim > m_st.m_max_dim) m_st.m_max_dim = red_dim;
    if (red_dim > 1) {
        // there is no alternative to syntactic convex closure right now
        // syntactic convex closure does not support BV
        if (m_do_syn_cls) {
            SASSERT(m_nw_vars.size() == 0);
            TRACE("subsume", tout << "Computing syntactic convex closure\n";);
            syn_cls(res_vec);
        } else {
            res_vec.reset();
            return false;
        }
        return true;
    }

    // zero dimensional convex closure
    if (red_dim == 0) { return false; }

    SASSERT(red_dim == 1);
    do_one_dim_cls(var, res_vec);
    return false;
}

// construct the formula result_var <= bnd or result_var >= bnd
expr *convex_closure::mk_ineq(expr_ref result_var, rational bnd, bool is_le) {
    if (m_is_arith) {
        if (is_le) return m_arith.mk_le(result_var, m_arith.mk_int(bnd));
        return m_arith.mk_ge(result_var, m_arith.mk_int(bnd));
    }
    // TODO figure out whether we need signed versions or unsigned versions.
    if (is_le) return m_bv.mk_ule(result_var, m_bv.mk_numeral(bnd, m_bv_sz));
    return m_bv.mk_ule(m_bv.mk_numeral(bnd, m_bv_sz), result_var);
}

void convex_closure::do_one_dim_cls(expr_ref var, expr_ref_vector &res_vec) {
    // The convex closure over one dimension is just a bound
    vector<rational> data;
    m_data.get_col(0, data);
    std::sort(
        data.begin(), data.end(),
        [](rational const &x, rational const &y) -> bool { return x > y; });

    expr_ref ub_expr(m), lb_expr(m), result_var(m);
    result_var = var;
    mul_by_rat(result_var, m_lcm);
    ub_expr = mk_ineq(result_var, data[0], true);
    lb_expr = mk_ineq(result_var, data[data.size() - 1], false);

    rational cr, off;
    expr_ref v(m);
    // add div constraints for all variables.
    for (unsigned j = 0; j < m_data.num_cols(); j++) {
        v = m_dim_vars.get(j);
        if (is_var(v) && (m_arith.is_int(v) || m_bv.is_bv(v))) {
            data.reset();
            m_data.get_col(j, data);
            std::sort(data.begin(), data.end(),
                      [](rational const &x, rational const &y) -> bool {
                          return x > y;
                      });
            if (compute_div_constraint(data, cr, off)) {
                result_var = v;
                mul_by_rat(result_var, m_lcm);
                if (m_is_arith)
                    res_vec.push_back(m_arith.mk_eq(
                        m_arith.mk_mod(result_var, m_arith.mk_int(cr)),
                        m_arith.mk_int(off)));
                else
                    res_vec.push_back(
                        m.mk_eq(m_bv.mk_bv_urem(result_var,
                                                m_bv.mk_numeral(cr, m_bv_sz)),
                                m_bv.mk_numeral(off, m_bv_sz)));
            }
        }
    }
    res_vec.push_back(ub_expr);
    res_vec.push_back(lb_expr);
}

} // namespace spacer