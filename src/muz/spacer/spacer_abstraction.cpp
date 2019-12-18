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

void abstract_fml(expr_ref_vector &fml_vec, expr_ref &leq_lit,
                  expr_ref_vector &abs_fml) {
    abs_fml.reset();
    expr *lhs;
    ast_manager &m = leq_lit.get_manager();
    expr_ref cube(m);

    // assume that lhs is a term
    lhs = (to_app(leq_lit))->get_arg(0);

    // long way to check two expressions are the same. normalize and then
    // antiunify
    anti_unifier anti(m);
    expr_ref pat(m);
    substitution sub1(m), sub2(m);
    app *c_app;
    expr *neg_chld;
    for (auto &c : fml_vec) {
        c_app = to_app(c);
        if (m.is_not(c_app, neg_chld)) c_app = to_app(neg_chld);
        if (c_app->get_num_args() != 2) {
            abs_fml.push_back(c);
            continue;
        }
        anti.reset();
        sub1.reset();
        sub2.reset();
        cube = expr_ref(c_app->get_arg(0), m);
        normalize_order(cube, cube);
        anti(cube, lhs, pat, sub1, sub2);
        if (sub1.get_num_bindings() != 0) abs_fml.push_back(c);
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
