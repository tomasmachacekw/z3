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
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_util.h"
#include "util/vector.h"
#include "util/mpq.h"


using namespace spacer;
namespace spacer {
lemma_cluster::lemma_cluster(context &ctx, int disT)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m),
      m_dis_threshold(disT) {}

// TODO: better distance metrics; currently implemented as boolean function
int lemma_cluster::distance(expr_ref antiU_result, substitution &s1,
                            substitution &s2) {
    SASSERT(s1.get_num_bindings() == s2.get_num_bindings());
    int dis = 0;
    expr_ref_vector uninterp_s1(m), uninterp_s2(m);
    for (unsigned j = 0, sz = s1.get_num_bindings(); j < sz; j++) {
        expr_ref e(m), e2(m);
        expr_offset r, r2;
        var_offset v, v2;
        s1.get_binding(j, v, r);
        s2.get_binding(j, v2, r2);
        if (is_uninterp_const(r.get_expr()) &&
            is_uninterp_const(r2.get_expr())) {
            uninterp_s1.push_back(r.get_expr());
            uninterp_s2.push_back(r2.get_expr());
        } else if (m_arith.is_numeral(r.get_expr()) &&
                   m_arith.is_numeral(r2.get_expr())) {
            continue; // good match
        }             // else if( is_uninterp_const(r.get_expr()) ||
                      // is_uninterp_const(r2.get_expr()) ){}
        else {
            dis += m_dis_threshold; // anything else considered as bad match!
        }
    }

    // Go through the uninterp consts and make sure contains
    SASSERT(uninterp_s1.size() == uninterp_s2.size());
    for (unsigned j = 0, sz = uninterp_s1.size(); j < sz; j++) {
        if (!m.are_equal(uninterp_s1.get(j), uninterp_s2.get(j))) {
            dis += m_dis_threshold;
        }
    }
    return dis;
}

bool lemma_cluster::are_neighbours(const expr_ref &cube, const expr_ref &lcube,
                                   expr_ref &pat, substitution &sub1,
                                   substitution &sub2) {
    anti_unifier anti(m);
    anti(cube, lcube, pat, sub1, sub2);
    return distance(pat, sub1, sub2) < m_dis_threshold;
}

void lemma_cluster::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);

    expr_ref_vector neighbours(m);

    //matrix for discovering linear equalities
    vector<mpq> v;
    //general_matrix lhs;

    expr_ref pattern(m);
    unsigned num_vars_in_pattern = 0;

    pred_transformer &pt = (&*lemma->get_pob())->pt();

    // all ACTIVE lemmas
    lemma_ref_vector all_lemmas;
    pt.get_all_lemmas(all_lemmas, false);

    expr_ref cube(m);
    cube = mk_and(lemma->get_cube());
    normalize_order(cube, cube);

    for (auto *l : all_lemmas) {
        expr_ref lcube(m), lpat(m);
        substitution sub1(m), sub2(m);
        lcube = mk_and(l->get_cube());
        normalize_order(lcube, lcube);
        if (are_neighbours(cube, lcube, lpat, sub1, sub2)) {
            neighbours.push_back(lcube);

            SASSERT(sub1.get_num_bindings() == sub2.get_num_bindings());
            if(sub1.get_num_bindings() == 1){
              // Only one binding here;
             } else {
              //
            }
            //SEE END OF THIS FILE for assumption
            //pushing elems in sub1 into vector v (v.push_back(mpq(elem)))
            //lhs.push_row(v)
            //v.clear()
            //repeat for sub2
            //lhs.push_row(v) and v.clear()

            if (sub1.get_num_bindings() > num_vars_in_pattern) {
                pattern = lpat;
                num_vars_in_pattern = sub1.get_num_bindings();
            }
        }
    }

    if (!neighbours.empty() && num_vars_in_pattern > 0) {
        lemma->update_neighbours(pattern, neighbours);
        m_st.max_group_size = std::max(m_st.max_group_size, neighbours.size());
        TRACE("cluster_stats",
               tout << "pattern: " << pattern << "\n"
               << "lemma cube: " << cube << "\n"
               << "neighbours: " << neighbours << "\n";);
        // XXX Enabled for current experiments only
        IF_VERBOSE(1,
                   verbose_stream() << "\nGROUP SIZE: " << neighbours.size() << "\n"
                   << "pattern: " << pattern << "\n"
                   << "lemma cube: " << cube << "\n"
                   << "neighbours: " << neighbours << "\n";);
    }

    CTRACE(
        "cluster_stats", neighbours.size() >= 10,
        tout << "---Pattern---\n"
             << pattern << "\n"
             << "---Concrete lemmas---\n";
        for (auto *n
             : neighbours) {
            tout << "(" << n->get_id() << "):\n" << mk_epp(n, m) << "\n";
        };
        tout << "\n------\n"
             << "Current #lemmas: " << all_lemmas.size() << "\n";);
}

void lemma_cluster::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.group", m_st.watch.get_seconds());
    st.update("SPACER max lemma group", m_st.max_group_size);
}
} // namespace spacer

//Finding linear eqaulities note:
//The assumption here is that all subs are of the same size
//But if we only work with 2 substitutions, they are by of same size by creation
//namely sub1.get_num_bindings() == sub2.get_num_bindings()
//this is a postcondition of anti_unifier, see L166 spacer_antiunify.cpp
