/**
   Copyright (c) 2019 Microsoft Corporation and Arie Gurfinkel

   Module Name:

   spacer_abstraction.cpp

   Abstract:

   Methods to implement conjecture rule in gspacer

   Author:

   Arie Gurfinkel
   Hari Govind


   Notes:

   --*/

#include "ast/for_each_expr.h"

#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_util.h"

namespace spacer {

bool drop_lit(expr_ref_vector &fml_vec, expr_ref &lit,
              expr_ref_vector &abs_fml) {
    abs_fml.reset();
    bool is_smaller = false;
    ast_manager &m = fml_vec.get_manager();
    expr_ref cube(m), lhs(m), rhs(m), lit_lhs(m), lit_rhs(m);
    expr *e1, *e2;
    SASSERT(!m.is_not(lit, e1) || !m.is_eq(e1));
    if (m.is_eq(lit, e1, e2)) {
        lit_lhs = e1;
        lit_rhs = e2;
    } else
        normalize_to_le(lit.get(), lit_lhs, lit_rhs);
    bool rhs_var = get_num_vars(lit_rhs) > 0;
    arith_util m_arith(m);
    expr_ref_vector exp_fml(m);
    for (auto &c : fml_vec) {
        if (m.is_eq(c, e1, e2) &&
            (m_arith.is_arith_expr(e1) || m_arith.is_arith_expr(e2))) {
            exp_fml.push_back(m_arith.mk_le(e1, e2));
            exp_fml.push_back(m_arith.mk_ge(e1, e2));
        } else
            exp_fml.push_back(c);
    }
    for (auto &c : exp_fml) {
        bool norm = normalize_to_le(c, lhs, rhs);
        if (!norm) {
            abs_fml.push_back(c);
            continue;
        }

        // normalize the literal so that it is exactly as in the lemma
        if (rhs_var) {
            normalize_order(lit_lhs, lit_lhs);
            normalize_order(lhs, lhs);
        } else {
            normalize_order(lit_rhs, lit_rhs);
            normalize_order(rhs, rhs);
        }
        TRACE("conjecture_verb", tout << " comparing " << lhs << " <= " << rhs
                                      << " with " << lit_lhs
                                      << " <= " << lit_rhs << "\n";);

        if ((rhs_var && lit_lhs != lhs) || (!rhs_var && lit_rhs != rhs)) {
            abs_fml.push_back(c);
            continue;
        }
        is_smaller = true;
    }
    return is_smaller;
}
} // namespace spacer
