#include "muz/spacer/spacer_convex_closure.h"

namespace spacer {
bool convex_closure::compute_cls(vector<rational> &data, expr *&cnst,
                                 expr_ref &cls) {
    // TODO handle duplicates in data
    // TODO use solver in z3
    std::sort(
        data.begin(), data.end(),
        [](rational const &x, rational const &y) -> bool { return x < y; });
    rational step = data[1] - data[0];
    for (unsigned i = 1; i < data.size() - 1; ++i) {
        if (step != data[i + 1] - data[i]) return false;
    }
    // AG: don't understand the comment, improve
    // progression is (forall i step*i + offset) where offset is ( d % step )
    // for any d
    expr_ref cd_expr(m_arith.mk_numeral(step, true), m);
    expr_ref d_expr(m_arith.mk_numeral(data.get(0), true), m);
    expr_ref lhs(m_arith.mk_mod(cnst, cd_expr), m);
    // AG: rhs is a number. It should be reduced to a number not to a mod expression!
    expr_ref rhs(m_arith.mk_mod(d_expr, cd_expr), m);
    // AG: simplify the case when rhs is 1
    // AG: the result is not a convex closure because bounds on cnst are not returned
    // AG: expected output is: data[0] <= cnst <= data[N] && cnst mod step == (data[0] mod step)
    cls = expr_ref(m.mk_eq(lhs, rhs), m);
    return true;
};
} // namespace spacer
