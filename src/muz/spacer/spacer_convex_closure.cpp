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
    if (m_dim <= 1) { return m_dim; }

    bool non_null_ker = m_kernel->compute_kernel();
    if (!non_null_ker) {
        TRACE("cvx_dbg",
              tout << "No linear dependencies between pattern vars\n";);
        return m_dim;
    }
    return m_kernel->get_kernel().num_cols();
}
// returns whether the closure is exact or not (i.e syntactic)
bool convex_closure::closure(expr_ref &res) {

    unsigned red_dim = reduce_dim();
    // TODO rewrite linear dependencies

    // Yet to be implemented
    if (red_dim != 1) { NOT_IMPLEMENTED_YET(); }

    // The convex closure over one dimension is just a bound
    vector<rational> &data = m_data.get_row(0);
    SASSERT(is_int_points());
    std::sort(
        data.begin(), data.end(),
        [](rational const &x, rational const &y) -> bool { return x < y; });
    expr_ref ub(m_arith.mk_numeral(data[0], true), m);
    expr_ref lb(m_arith.mk_numeral(data[data.size() - 1], true), m);
    expr *var = m_dim_vars[0];
    app *ub_expr = m_arith.mk_le(var, ub.get());
    app *lb_expr = m_arith.mk_ge(var, lb.get());
    // TODO add division constraints.
    res = m.mk_and(ub_expr, lb_expr);
    return true;
};
} // namespace spacer
