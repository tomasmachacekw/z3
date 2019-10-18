#include "muz/spacer/spacer_convex_closure.h"

namespace spacer {
bool convex_closure::is_int_points() const {
    rational val;
    for (unsigned i = 0; i < m_data.num_rows(); i++) {
        for (unsigned j = 0; j < m_data.num_cols(); j++)
            if (!m_data.get(i, j).is_int()) return false;
    }
    return true;
}

unsigned convex_closure::reduce_dim() {
    bool non_null_ker = m_kernel->compute_kernel();
    if (!non_null_ker) {
        TRACE("cvx_dbg",
              tout << "No linear dependencies between pattern vars\n";);
        return m_dim;
    }
    const spacer_matrix &ker(m_kernel->get_kernel());

    SASSERT(ker.num_rows() > 0);
    SASSERT(ker.num_rows() <= m_dim);
    SASSERT(ker.num_cols() == m_dim + 1);
    // m_dim - ker.num_rows() is the number of variables that have no linear
    // dependencies
    return m_dim - ker.num_rows();
}

// for each row [0, 1, 0, 1 , 1], rewrite v1 = -1*v3 + -1*1
void convex_closure::rewrite_lin_deps() {
    const spacer_matrix &ker(m_kernel->get_kernel());
    unsigned n_rows = ker.num_rows();
    SASSERT(n_rows > 0);
    // index of the variable we are going to rewrite
    int pv = -1;
    // contains the right hand side of equality
    expr_ref_vector rw(m);
    // are we constructing rhs or lhs
    bool rhs = false;
    vector<expr *> temp(m_dim_vars);
    // start generating equalities from bottom row
    for (unsigned i = n_rows; i > 0; i--) {

        const vector<rational> &row = ker.get_row(i - 1);
        // reset everything
        rw.reset();
        pv = -1;
        rhs = false;
        rational coeff(1);
        for (unsigned j = 0; j < row.size(); j++) {
            rational val = row.get(j);
            SASSERT(j >= i - 1 || val.is_zero());
            SASSERT(val.is_int());
            if (!val.is_zero()) {
                if (!rhs) {
                    // Cannot re-write the last dim
                    if (j == row.size() - 1) continue;
                    SASSERT(pv == -1);
                    pv = j;
                    rhs = true;
                    // In integer echelon form, the pivot need not be 1
                    if (val != 1) coeff = val;
                } else {
                    expr *prod = m_arith.mk_numeral(-1 * val, true);
                    if (j != row.size() - 1)
                        prod = m_arith.mk_mul(m_dim_vars[j], prod);
                    rw.push_back(prod);
                }
            }
        }

        // make sure that there is a non-zero entry
        SASSERT(pv != -1);

        if(rw.size() == 0) {
            temp[pv] = m_arith.mk_eq(m_dim_vars[pv], m_arith.mk_numeral(rational(0), true));
            continue;
        }

        expr *rw_term = m_arith.mk_add(rw.size(), rw.c_ptr());
        expr *pv_var = m_dim_vars[pv];
        if (coeff != 1) {
            pv_var = m_arith.mk_mul(pv_var, m_arith.mk_numeral(coeff, true));
        }
        rw_term = m.mk_eq(pv_var, rw_term);
        TRACE("cvx_dbg", tout << "rewrote " << mk_pp(m_dim_vars[pv], m)
                              << " into " << mk_pp(rw_term, m) << "\n";);
        temp[pv] = rw_term;
    }
    m_dim_vars.reset();
    m_dim_vars = temp;
}

// returns whether the closure is exact or not (i.e syntactic)
bool convex_closure::closure(expr_ref_vector &res_vec) {

    unsigned red_dim = reduce_dim();
    // Yet to be implemented
    if (red_dim > 1) { NOT_IMPLEMENTED_YET(); }
    // store dim var before rewrite
    expr *var = m_dim_vars[0];
    if (red_dim < dims()) {
        rewrite_lin_deps();
        expr *lhs, *rhs;
        for (expr *v : m_dim_vars) {
            if (m.is_eq(v, lhs, rhs) && lhs != rhs)
                res_vec.push_back(expr_ref(v, m));
        }
    }
    TRACE("cvx_dbg", tout << "Linear equalities true of the matrix "
                          << mk_and(res_vec) << "\n";);
    // zero dimensional convex closure
    if (red_dim == 0) { return true; }

    // The convex closure over one dimension is just a bound
    vector<rational> data;
    m_data.get_col(0, data);
    SASSERT(is_int_points());
    std::sort(
        data.begin(), data.end(),
        [](rational const &x, rational const &y) -> bool { return x > y; });
    expr *ub = m_arith.mk_numeral(data[0], true);
    expr *lb = m_arith.mk_numeral(data[data.size() - 1], true);

    expr *ub_expr = m_arith.mk_le(var, ub);
    expr *lb_expr = m_arith.mk_ge(var, lb);
    // TODO add division constraints.
    res_vec.push_back(ub_expr);
    res_vec.push_back(lb_expr);
    return true;
};
} // namespace spacer
