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

namespace {
  //a \subseteq b
  bool is_subset(const expr_ref_vector &a ,const expr_ref_vector &b)
  {
    if(a.size() > b.size())
      return false;
    for(expr * e : a)
      if(!b.contains(e))
        return false;
    return true;
  }
}

namespace spacer {

bool is_leq(expr *pattern, ast_manager &m, arith_util &a_util)
{
  expr *e;
  if (m.is_not(pattern, e)) return is_leq(e, m, a_util);
  if (a_util.is_arith_expr(to_app(pattern)) || m.is_eq(pattern)) {
    return get_num_vars(pattern) == 1 && !has_nonlinear_var_mul(pattern, m);
  }
  return false;
}
// a mono_var_pattern has only one variable in the whole expression and is
// linear returns the literal with the variable
bool context::mono_var_pattern(expr *pattern, expr_ref &leq_lit) {
    if(get_num_vars(pattern) != 1) return false;
    ast_manager &m = leq_lit.m();
    arith_util a_util(m);
    // if the pattern has multiple literals, check whether exactly one of them is leq
    expr_ref_vector pattern_and(m);
    pattern_and.push_back(pattern);
    flatten_and(pattern_and);
    unsigned count = 0;
    for (auto *lit : pattern_and) {
      if (is_leq(lit, m, a_util)) { leq_lit = lit; count++; }
    }
    return count == 1;
}

// Finds a lemma matching the mono_var_pattern
// stores the pattern in n
bool context::mono_coeff_lm(pob &n, expr_ref &lit) {
    ast_manager &m = lit.m();
    const ptr_vector<lemma> &lemmas = n.lemmas();
    // for every lemma l of n
    for (auto &l : lemmas) {
        // find a group containing lemma l
        const expr_ref_vector &neighbours = l->get_neighbours();

        // skip lemma if no group is found
        if (neighbours.empty() || !neighbours.get(0)) continue;

        expr *pattern = neighbours.get(0);

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
    get_uninterp_consts(lhs, lhs_consts);
    // filter from pob_cube all literals that contain all uninterpreted constants in lhs
    for (auto &c : pob_cube) {
        get_uninterp_consts(c, u_consts);
        SASSERT(u_consts.size() > 0);
        if (!is_subset(lhs_consts, u_consts)) new_pob.push_back(c);
        u_consts.reset();
    }

    // compute abstract pob if any literals found and at least one was removed
    if (new_pob.size() > 0 && new_pob.size() < pob_cube.size())
        return true;
    return false;
}

} // namespace spacer
