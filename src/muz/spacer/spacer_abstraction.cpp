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

// Finds a lemma matching the mono_var_pattern
// stores the pattern in n
bool context::mono_coeff_lm(pob &n, expr_ref &lit) {
    ast_manager &m = lit.m();
    const ptr_vector<lemma> &lemmas = n.lemmas();
    // for every lemma l of n
    for (auto &l : lemmas) {
        // find a group containing lemma l
        lemma_cluster* lc = n.pt().get_cluster(l);
        // skip lemma if no group is found
        if (lc == nullptr) continue;

        const expr_ref& pattern = lc->get_pattern();

        if (mono_var_pattern(pattern, lit)) {
            // HG : store the pattern in the pob. Required because there could
            // be multile patterns among lemmas
            TRACE("merge_dbg",
                  tout << "Found a pattern " << mk_pp(pattern, m) << "\n";);
            n.set_abs_pattern(pattern);
            return true;
        }
    }
    return false;
}

// If a lemma of n matches the mono_var_pattern, abstract all literals that
// contain  the uninterpreted constants in the pattern.  If there are multiple
// mono_var_patterns, pick one
bool context::abstract_pob(pob &n, expr_ref &leq_lit, expr_ref_vector & new_pob) {
    if (!n.can_abs()) return false;
    SASSERT(new_pob.size() == 0);
    expr *lhs;
    expr_ref_vector pob_cube(m), u_consts(m), lhs_consts(m);
    pob_cube.push_back(n.post());
    flatten_and(pob_cube);

    // assume that lhs is a term
    lhs = (to_app(leq_lit))->get_arg(0);
    // filter from pob_cube all literals that contain all uninterpreted constants in lhs
    for (auto &c : pob_cube) {
        if (to_app(c)->get_arg(0) != lhs)
            new_pob.push_back(c);
    }

    // compute abstract pob if any literals found and at least one was removed
    if (new_pob.size() > 0 && new_pob.size() < pob_cube.size())
        return true;
    return false;
}

} // namespace spacer
