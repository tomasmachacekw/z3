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
        lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m){
        dis_threshold = disT;
    }

    // better distance metrics; currently implemented as boolean function
    int lemma_cluster::distance(expr_ref antiU_result, substitution &s1, substitution &s2){
        SASSERT(s1.get_num_bindings() == s2.get_num_bindings());
        int dis = 0;
        expr_ref_vector uninterp_s1(m), uninterp_s2(m);
        for(unsigned j = 0; j < s1.get_num_bindings(); j++){
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
                dis += dis_threshold; //anything else considered as bad match!
            }
        }

        // Go through the uninterp consts and make sure contains
        SASSERT(uninterp_s1.size() == uninterp_s2.size());
        for(auto &u1 : uninterp_s1){
            if(!uninterp_s2.contains(u1)){
                dis += dis_threshold;
                // dis += 1;
            }
        }
        return dis;
    }

    void lemma_cluster::with_var_coeff(app *a,
                                       expr_ref_vector &out,
                                       bool has_var_coeff)
    {
        for(expr *e : *a){
            if(is_uninterp_const(e) && has_var_coeff){
                out.push_back(e);
            }
            else if(is_app(e)){
                with_var_coeff(to_app(e), out, m_arith.is_mul(e)  );
            }
        }
    }


    expr_ref_vector lemma_cluster::generate_groups(expr_ref &antiRes){
        expr_ref_vector temp(m);
        return temp;
    }

    void lemma_cluster::operator()(lemma_ref &lemma){
        anti_unifier antiU(m);
        expr_ref_vector neighbours(m);
        substitution subs_newLemma(m), subs_oldLemma(m);
        expr_ref cube(m), normalizedCube(m);
        cube = mk_and(lemma->get_cube());
        normalize_order(cube, normalizedCube);

        pred_transformer &pt = (&*lemma->get_pob())->pt();
        lemma_ref_vector all_lemmas;
        pt.get_all_lemmas(all_lemmas, false);

        for(auto &l:all_lemmas){
            subs_newLemma.reset();
            subs_oldLemma.reset();
            expr_ref oldCube(m), normalizedOldCube(m), antiUni_result(m);
            oldCube = mk_and(l->get_cube());
            normalize_order(oldCube, normalizedOldCube);

            antiU(normalizedCube, normalizedOldCube, antiUni_result, subs_newLemma, subs_oldLemma);
            if( subs_oldLemma.get_num_bindings() == 0 ) { continue; } // skip the Identicals

            int dis = distance(antiUni_result, subs_newLemma, subs_oldLemma);
            if(dis < dis_threshold){
                neighbours.push_back(normalizedOldCube);
                TRACE("distance_dbg",
                      tout
                      << "New Lemma Cube: " << mk_pp(normalizedCube, m) << "\n"
                      << "Old Lemma Cube: " << mk_pp(normalizedOldCube, m) << "\n"
                      << "antiU result: " << mk_pp(antiUni_result, m) << "\n"
                      << "dis: " << dis << "\n"
                      << "subs new:\n=====\n";
                      subs_newLemma.display(tout);
                      tout << "\n"
                      << "subs old:\n=====\n";
                      subs_oldLemma.display(tout);
                      tout << "\n"
                      ;);
            }

            // [TODO_Maybe] Could we decide based on dis_new == dis_old?
            // int dis_new = distance(subs_newLemma);
            // int dis_old = distance(subs_oldLemma);

            if(neighbours.size() >= dis_threshold){
                TRACE("cluster_dbg",
                      tout << "New Lemma Cube: " << mk_pp(normalizedCube, m) << "\n";
                      for(auto &n : neighbours){
                          tout << "Neighbour Cube: " << mk_pp(n, m) << "\n";
                      };);

                // start marking ...
                lemma->update_neighbours(antiUni_result, neighbours);
                pob_ref &pob = lemma->get_pob();
                pob->update_pattern(generate_groups(antiUni_result));
                return;
                // bailout if none of above works...
                // TODO with marking decide WHEN to give up
                // throw unknown_exception();
            }

        }
    }
    
}
