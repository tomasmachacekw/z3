/*

  spacer_cluster.cpp

  Discover and mark lemma clusters.

*/
#include <algorithm>

#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_antiunify.h"
#include "muz/spacer/spacer_manager.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/substitution/substitution.h"
#include "ast/rewriter/var_subst.h"


using namespace spacer;
namespace spacer{
    lemma_cluster::lemma_cluster(context &ctx, int disT) :
        lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m), m_dis_threshold(disT) {}

    // TODO: better distance metrics; currently implemented as boolean function
    int lemma_cluster::distance(expr_ref antiU_result, substitution &s1, substitution &s2){
        SASSERT(s1.get_num_bindings() == s2.get_num_bindings());
        int dis = 0;
        expr_ref_vector uninterp_s1(m), uninterp_s2(m);
        for(unsigned j = 0, sz = s1.get_num_bindings(); j < sz; j++){
            expr_ref e(m), e2(m);
            expr_offset r, r2;
            var_offset  v, v2;
            s1.get_binding(j, v, r);
            s2.get_binding(j, v2, r2);
            if( is_uninterp_const(r.get_expr()) && is_uninterp_const(r2.get_expr()) ){
                uninterp_s1.push_back(r.get_expr());
                uninterp_s2.push_back(r2.get_expr());
            } else if( m_arith.is_numeral(r.get_expr()) && m_arith.is_numeral(r2.get_expr()) ){
                continue; //good match
            } // else if( is_uninterp_const(r.get_expr()) || is_uninterp_const(r2.get_expr()) ){}
            else {
                dis += m_dis_threshold; //anything else considered as bad match!
            }
        }

        // Go through the uninterp consts and make sure contains
        SASSERT(uninterp_s1.size() == uninterp_s2.size());
        for(unsigned j = 0, sz = uninterp_s1.size(); j < sz; j++){
            if(!m.are_equal(uninterp_s1.get(j), uninterp_s2.get(j))){
                dis += m_dis_threshold;
            }
        }
        return dis;
    }

    expr_ref_vector lemma_cluster::generate_groups(expr *pattern){
        expr_ref_vector temp(m);
        return temp;
    }

    void lemma_cluster::operator()(lemma_ref &lemma){
        anti_unifier antiU(m);
        expr_ref_vector neighbours(m);
        substitution subs_newLemma(m), subs_oldLemma(m);
        expr_ref cube(m), normalizedCube(m);

        pred_transformer &pt = (&*lemma->get_pob())->pt();

        cube = mk_and(lemma->get_cube());
        normalize_order(cube, normalizedCube);

        lemma_ref_vector all_lemmas;
        pt.get_all_lemmas(all_lemmas, false);
        unsigned worst_subs_num_bindings = 0;
        expr_ref worst_antiUni_result(m);

        for(auto &l : all_lemmas){
            subs_newLemma.reset();
            subs_oldLemma.reset();
            expr_ref oldCube(m), normalizedOldCube(m), antiUni_result(m);
            oldCube = mk_and(l->get_cube());
            normalize_order(oldCube, normalizedOldCube);

            // antiU(normalizedCube, normalizedOldCube, antiUni_result, subs_newLemma, subs_oldLemma);
            // using this order prevents the antiUni_result becoming too strict
            antiU(normalizedOldCube, normalizedCube, antiUni_result, subs_oldLemma, subs_newLemma);

            if( subs_oldLemma.get_num_bindings() == 0 ) { continue; } // skip the Identicals

            int dis = distance(antiUni_result, subs_newLemma, subs_oldLemma);
            if(dis < m_dis_threshold){

                if(subs_newLemma.get_num_bindings() >= worst_subs_num_bindings){
                    worst_subs_num_bindings = subs_newLemma.get_num_bindings();
                    worst_antiUni_result = antiUni_result;
                }

                neighbours.push_back(normalizedOldCube);
                TRACE("distance_dbg",
                      tout
                      << "New Lemma Cube: " << mk_pp(normalizedCube, m) << "\n"
                      << "Old Lemma Cube: " << mk_pp(normalizedOldCube, m) << "\n"
                      << "antiU result: " << mk_pp(antiUni_result, m) << "\n"
                      << "dis: " << dis << "\n"
                      << "neighbours: " << neighbours.size() << "\n";
                      for(auto &n : neighbours){
                          tout << "Neighbour Cube: " << mk_pp(n, m) << "\n";
                      }
                      ;);
            }

            if(neighbours.size() >= m_dis_threshold){
                TRACE("nonlinear_cluster",
                      if(has_nonlinear_mul(antiUni_result, m)) {
                          TRACE("nonlinear_cluster", tout
                                << "Lemma Cube: " << mk_pp(normalizedCube, m) << "\n"
                                << "NL Pattern: " << mk_pp(antiUni_result, m) << "\n";
                                for(auto &n : neighbours){
                                    tout << "Neighbour Cube: " << mk_pp(n, m) << "\n";
                                };);
                          throw unknown_exception();
                      };);

                STRACE("cluster_stats",
                      if(neighbours.size() >= 10) {
                          tout << "---Pattern---\n" << mk_pp(worst_antiUni_result, m);
                          tout << "\n---Concrete lemmas---\n";
                          for(auto &n : neighbours){
                              tout << "(" << n->get_id() << "):\n" << mk_pp(n, m) << "\n";
                          };
                          tout << "\n------\n";
                          tout << "Current #lemmas: " << all_lemmas.size() << "\n";
                          // throw unknown_exception();
                          lemma->update_neighbours(worst_antiUni_result, neighbours);
                          return;
                      }
                      else { continue; }
                      ;);

                TRACE("cluster_dbg",
                      tout << "New Lemma Cube: " << mk_pp(normalizedCube, m) << "\n"
                      << "Pattern found: " << mk_pp(antiUni_result, m) << "\n";
                      for(auto &n : neighbours){
                          tout << "Neighbour Cube: " << mk_pp(n, m) << "\n";
                      };);

                // start marking ...
                lemma->update_neighbours(worst_antiUni_result, neighbours);
                pob_ref &pob = lemma->get_pob();
                pob->update_cluster(generate_groups(antiUni_result));
                return;
            }

        }
    }

}


// [Old dev remarks]
// Given a unary distance function, Could we decide based on dis_new == dis_old?
// int dis_new = distance(subs_newLemma);
// int dis_old = distance(subs_oldLemma);

