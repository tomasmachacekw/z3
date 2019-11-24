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
        lemma_cluster *lc = n.pt().clstr_match(l);
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

void context::set_nvr_abs(const pob_ref & pob_abs) {
  if(!pob_abs) return;
  //HG : this pob should be an abstraction. The neighbours are selected later
  SASSERT(pob_abs->is_abs());
  //do not compute abstractions of abstractions
  pob_abs->set_nvr_abs();

  //if pob_abs is a predecessor of another abs_pob, there are no pob related to pob_abs
  if(!pob_abs->concrete()) return;
  pob_abs->concrete()->set_nvr_abs();
  //get pattern that was used to create reachable
  const expr * pob_pattern = pob_abs->concrete()->get_abs_pattern();
  SASSERT(pob_pattern != nullptr);

  lemma_cluster* lc = pob_abs->pt().get_cluster(pob_pattern);
  SASSERT(lc != nullptr);
  lemma_ref_vector all_lemmas;
  pob_abs->pt().get_all_lemmas(all_lemmas, false);
  for(auto *l : all_lemmas) {
      if (lc->can_contain(l))
          l->get_pob()->set_nvr_abs();
  }
}

} // namespace spacer
