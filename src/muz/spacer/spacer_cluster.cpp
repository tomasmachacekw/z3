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
#include "muz/spacer/spacer_cluster.h"

using namespace spacer;
namespace spacer {
lemma_cluster_finder::lemma_cluster_finder(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m) {}

bool lemma_cluster_finder::are_neighbours(expr_ref antiU_result, substitution &s1,
                            substitution &s2) {
    SASSERT(s1.get_num_bindings() == s2.get_num_bindings());
    expr_ref_vector uninterp_s1(m), uninterp_s2(m);
    for (unsigned j = 0, sz = s1.get_num_bindings(); j < sz; j++) {
        expr_ref e(m), e2(m);
        expr_offset r, r2;
        var_offset v, v2;
        s1.get_binding(j, v, r);
        s2.get_binding(j, v2, r2);
        if (is_uninterp_const(r.get_expr()) &&
            is_uninterp_const(r2.get_expr())) {
          //HG: right now, we are concerned only with difference in interpreted constants
          //Not sure whether we need this for now.
            uninterp_s1.push_back(r.get_expr());
            uninterp_s2.push_back(r2.get_expr());
        } else if (m_arith.is_numeral(r.get_expr()) &&
                   m_arith.is_numeral(r2.get_expr())) {
            continue; // good match
        }             // else if( is_uninterp_const(r.get_expr()) ||
                      // is_uninterp_const(r2.get_expr()) ){}
        else {
          return false; //anything else is a bad match
        }
    }

    // Go through the uninterp consts and make sure contains
    SASSERT(uninterp_s1.size() == uninterp_s2.size());
    for (unsigned j = 0, sz = uninterp_s1.size(); j < sz; j++) {
        if (!m.are_equal(uninterp_s1.get(j), uninterp_s2.get(j))) {
          //HG: seems like this piece of code will never get executed
          //If both of them are the same uninterpreted constant, they wouldn't be
          //antiunified.
          return false;
        }
    }
    return true;
}

bool lemma_cluster_finder::are_neighbours(const expr_ref &cube, const expr_ref &lcube,
                                   expr_ref &pat, substitution &sub1,
                                   substitution &sub2) {
    anti_unifier anti(m);
    anti(cube, lcube, pat, sub1, sub2);
    return are_neighbours(pat, sub1, sub2);
}

void lemma_cluster_finder::operator()(lemma_ref& lemma) {
  scoped_watch _w_(m_st.watch);
  pred_transformer &pt = (&*lemma->get_pob())->pt();

  //try to add lemma to existing clusters
  if (pt.add_to_cluster(lemma)) { return ; }

  //lemma cannot be added to any existing clusters
  //Check whether it forms a new cluster
  expr_ref_vector patterns(m);
  unsigned num_vars_in_pattern = 0;
  lemma_ref_vector all_lemmas;
  pt.get_all_lemmas(all_lemmas, false);

  expr_ref cube(m), pattern(m);
  cube = mk_and(lemma->get_cube());
  normalize_order(cube, cube);

  expr_ref lcube(m), lpat(m);
  substitution sub1(m), sub2(m);
  lemma_ref_vector neighbours;


  //compute the most general pattern to which lemmas fit
  for (auto *l : all_lemmas) {
    sub1.reset();
    sub2.reset();
    lcube = mk_and(l->get_cube());
    normalize_order(lcube, lcube);
    if (are_neighbours(cube, lcube, lpat, sub1, sub2)) {
      neighbours.push_back(&*l);
      patterns.push_back(lpat);
    }
  }
  //go through all the patterns to see if there is a pattern which is general enough to include all elemmas.
  bool is_general_pattern = false, pos = true;
  sem_matcher matcher(m);
  for(expr* e : patterns) {
    is_general_pattern = true;
    for(auto *l : neighbours) {
      lcube = mk_and(l->get_cube());
      normalize_order(lcube, lcube);
      matcher.reset();
      if(!(matcher(e, lcube.get(), sub1, pos) && pos)) {
        //this pattern is no good
        is_general_pattern = false;
        break;
      }
      if(is_general_pattern) {
        //found a good pattern. make a cluster with it.
        pattern = e;
        num_vars_in_pattern = get_num_vars(pattern);
        break;
      }
    }
  }

  CTRACE("cluster_stats", !neighbours.empty() && num_vars_in_pattern > 0 && !is_general_pattern,
         tout << "Failed to find a general pattern for cluster. Lemma is: " << lemma->get_cube() << "\n";);

  if (is_general_pattern && !neighbours.empty() && num_vars_in_pattern > 0) {
    neighbours.push_back(lemma.get());
    lemma_cluster* cluster = pt.mk_cluster(pattern, neighbours.size());
    bool added = true;
    for(const lemma_ref& l : neighbours) {
      added =  cluster->add_lemma(l);
      CTRACE("cluster_stats", !added,
             tout << "Failed to add lemma to a cluster. Lemma is: " << l->get_cube() << "\n"
             << " and pattern is: " << pattern << " the original lemma is " << lemma->get_cube() << "\n";);
      SASSERT(added);
    }
    TRACE("cluster_stats",
          tout << "created new cluster with pattern: " << pattern << "\n"
          << " and lemma cube: " << cube << "\n";);
  }
}
void lemma_cluster_finder::collect_statistics(statistics &st) const {
  st.update("time.spacer.solve.reach.gen.group", m_st.watch.get_seconds());
}
} // namespace spacer
