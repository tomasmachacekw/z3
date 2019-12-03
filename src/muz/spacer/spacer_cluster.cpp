/*

  spacer_cluster.cpp

  Discover and mark lemma clusters.

*/
#include <algorithm>

#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/rewriter/var_subst.h"
#include "ast/substitution/substitution.h"
#include "muz/spacer/spacer_antiunify.h"
#include "muz/spacer/spacer_cluster.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_util.h"
#include "smt/tactic/unit_subsumption_tactic.h"
#include "util/mpq.h"
#include "util/vector.h"

using namespace spacer;
namespace spacer {
void lemma_cluster ::rm_subsumed(lemma_info_vector &removed_lemmas) {
    removed_lemmas.reset();
    if (m_lemma_vec.size() <= 1) return;
    tactic_ref simplifier = mk_unit_subsumption_tactic(m);
    goal_ref g(alloc(goal, m, false, false, false));

    goal_ref_buffer result;
    for (auto l : m_lemma_vec) { g->assert_expr(l.get_lemma()->get_expr()); }
    (*simplifier)(g, result);
    SASSERT(result.size() == 1);
    goal *r = result[0];
    if (r->size() == m_lemma_vec.size()) return;
    lemma_info_vector non_subsumd_lemmas;
    for (auto l : m_lemma_vec) {
        bool found = false;
        for (unsigned i = 0; i < r->size(); i++) {
            if (l.get_lemma()->get_expr() == r->form(i)) {
                found = true;
                non_subsumd_lemmas.push_back(l);
                TRACE("cluster_stats_verb", tout << "Keeping lemma "
                                                 << l.get_lemma()->get_cube()
                                                 << "\n";);
                break;
            }
        }
        if (!found) {
            TRACE("cluster_stats_verb", tout << "Removing subsumed lemma "
                                             << l.get_lemma()->get_cube()
                                             << "\n";);
            removed_lemmas.push_back(l);
        }
    }
    m_lemma_vec.reset();
    m_lemma_vec.append(non_subsumd_lemmas);
}

bool lemma_cluster ::match(const expr_ref &e, substitution &sub) {
    m_matcher.reset();
    bool pos;
    bool is_match = m_matcher(m_pattern.get(), e.get(), sub, pos);
    unsigned n_binds = sub.get_num_bindings();
    std::pair<unsigned, unsigned> var;
    expr_offset r;
    arith_util a_util(m);
    if (!(is_match && pos)) return false;
    // All the matches should be numerals
    for (unsigned i = 0; i < n_binds; i++) {
        sub.get_binding(i, var, r);
        if (!a_util.is_numeral(r.get_expr())) return false;
    }
    return true;
}

bool lemma_cluster ::add_lemma(const lemma_ref &lemma, bool subs_check) {
    substitution sub(m);
    sub.reserve(1, get_num_vars(m_pattern.get()));
    expr_ref cube(m);
    cube = mk_and(lemma->get_cube());
    normalize_order(cube, cube);
    if (!match(cube, sub)) return false;
    TRACE("cluster_stats_verb",
          tout << "Trying to add lemma " << lemma->get_cube() << "\n";);
    lemma_info l_i(lemma, sub);
    m_lemma_vec.push_back(l_i);
    if (subs_check) {
        lemma_info_vector removed_lemmas;
        rm_subsumed(removed_lemmas);
        for (auto r_l : removed_lemmas) {
            // There is going to atmost subsumed lemma that matches l_i
            if (r_l.get_lemma() == l_i.get_lemma()) return false;
        }
    }
    TRACE("cluster_stats", tout << "Added lemma " << lemma->get_cube()
                                << " to  existing cluster " << m_pattern
                                << "\n";);
    return true;
}

} // namespace spacer
