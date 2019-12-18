/**
   Copyright (c) 2019 Microsoft Corporation and Arie Gurfinkel

   Module Name:

   spacer_abstraction.cpp

   Abstract:

   Abstraction of Proof Obligations

   Author:

   Arie Gurfinkel
   Hari Govind


   Notes:

   --*/

#include "ast/for_each_expr.h"

#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_util.h"

namespace spacer {

bool is_mono_var(expr *pattern, ast_manager &m, arith_util &a_util) {
    expr *e;
    if (m.is_not(pattern, e)) return is_mono_var(e, m, a_util);
    if (a_util.is_arith_expr(to_app(pattern)) || m.is_eq(pattern)) {
        return get_num_vars(pattern) == 1 && !has_nonlinear_var_mul(pattern, m);
    }
    return false;
}

void context::set_nvr_abs(const pob_ref &pob_abs) {
    if (!pob_abs) return;
    // HG : this pob should be an abstraction. The neighbours are selected later
    SASSERT(pob_abs->is_abs());
    // do not compute abstractions of abstractions
    pob_abs->set_can_abs(false);

    // if pob_abs is a predecessor of another abs_pob, there are no pob related
    // to pob_abs
    if (!pob_abs->concrete()) return;
    pob_abs->concrete()->set_can_abs(false);
    // get pattern that was used to create reachable
    const expr *pob_pattern = pob_abs->concrete()->get_abs_pattern();
    SASSERT(pob_pattern != nullptr);

    lemma_cluster *lc = pob_abs->pt().get_cluster(pob_pattern);
    SASSERT(lc != nullptr);
    lemma_ref_vector all_lemmas;
    pob_abs->pt().get_all_lemmas(all_lemmas, false);
    for (auto *l : all_lemmas) {
        if (lc->can_contain(l)) l->get_pob()->set_can_abs(false);
bool mono_var_pattern(const expr_ref &pattern, expr_ref &leq_lit) {
    if (get_num_vars(pattern) != 1) return false;
    ast_manager &m = leq_lit.m();
    arith_util a_util(m);
    // if the pattern has multiple literals, check whether exactly one of them
    // is leq
    expr_ref_vector pattern_and(m);
    pattern_and.push_back(pattern);
    flatten_and(pattern_and);
    unsigned count = 0;
    for (auto *lit : pattern_and) {
        if (is_mono_var(lit, m, a_util)) {
            leq_lit = lit;
            count++;
        }
    }
    return count == 1;
}
    }
}

// refine lemma. Right now the refinement is to learn the negation of pob
void context::refine_pob(pob &n, expr_ref_vector &pob_cube) {
    pob_cube.reset();
    pob_cube.push_back(n.post());
    flatten_and(pob_cube);
    simplify_bounds(pob_cube);
}
} // namespace spacer
