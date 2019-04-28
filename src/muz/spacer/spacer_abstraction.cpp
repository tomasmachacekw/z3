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

#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_util.h"

namespace {

// a mono_var_pattern has only one variable in the whole expression and is
// linear
// returns the literal with the variable
bool mono_var_pattern(expr *pattern, expr_ref &leq_lit) {
    ast_manager &m = leq_lit.m();
    arith_util a_util(m);
    // XXX does not handle equality
    if (a_util.is_arith_expr(to_app(pattern)) || m.is_eq(pattern)) {
        bool is_leq =
            spacer::get_num_vars(pattern) == 1 && !spacer::has_nonlinear_mul(pattern, m);
        if (is_leq) leq_lit = pattern;
        return is_leq;
    }
    expr *e;
    if (m.is_not(pattern, e)) { return mono_var_pattern(e, leq_lit); }
    SASSERT(m.is_and(pattern));
    // if the pattern has multiple literals, check whether one of them is leq
    expr_ref_vector pattern_and(m);
    pattern_and.push_back(pattern);
    flatten_and(pattern_and);
    unsigned count = 0;
    for (auto lit : pattern_and) {
        if (mono_var_pattern(lit, leq_lit)) count++;
    }
    return count == 1;
}
// a \subseteq b
bool is_subset(const expr_ref_vector &a, const expr_ref_vector &b) {
    if (a.size() > b.size()) return false;
    for (expr *e : a)
        if (!b.contains(e)) return false;
    return true;
}

} // namespace


namespace spacer {
void context::abstract_pob(pob &n, pob_ref_buffer &out) {
    const ptr_vector<lemma> &lemmas = n.lemmas();
    expr_ref_vector new_pob(m), pob_cube(m), u_consts(m), lhs_consts(m);
    expr *lhs;
    pob_cube.push_back(n.post());
    flatten_and(pob_cube);

    // for every lemma l of n
    for (auto &l : lemmas) {
        // find a group containing lemma l
        const expr_ref_vector &neighbours = l->get_neighbours();

        // skip lemma if no group is found
        if (neighbours.empty() || !neighbours.get(0)) continue;

        expr *pattern = neighbours.get(0);
        expr_ref leq_lit(m);

        if (!mono_var_pattern(pattern, leq_lit)) continue;

        // assume that lhs is a term (actually an uninterpreted constant)
        lhs = (to_app(leq_lit))->get_arg(0);
        get_uninterp_consts(lhs, lhs_consts);
        // filter from pob_cube all literals that contain lhs
        for (auto &c : pob_cube) {
            get_uninterp_consts(c, u_consts);
            SASSERT(u_consts.size() > 0);
            if (!is_subset(lhs_consts, u_consts)) new_pob.push_back(c);
            u_consts.reset();
        }

        // compute abstract pob if any literals found and at least one was
        // removed
        if (new_pob.size() > 0 && new_pob.size() < pob_cube.size()) {
            expr_ref c = mk_and(new_pob);
            pob *f = n.pt().find_pob(&n, c);
            // skip if new pob is already in the queue
            if (f && f->is_in_queue()) continue;

            // create abstract pob
            f = n.pt().mk_pob(&n, n.level(), n.depth(), c, n.get_binding());
            f->set_abs();
            out.push_back(f);

            // AG: ???
            n.set_abs_pattern(pattern);

            TRACE("merge_dbg", tout << " abstracting " << mk_pp(n.post(), m)
                                    << " id is " << n.post()->get_id()
                                    << "\n into pob " << c << " id is "
                                    << f->post()->get_id() << "\n";);
            m_stats.m_num_abstractions++;
            return;
        } else if (new_pob.empty()) {
            // If the pob cannot be abstracted, stop using Farkas generalization
            // on it.
            n.set_farkas_generalizer(false);
        }
    }
}
} // namespace spacer
