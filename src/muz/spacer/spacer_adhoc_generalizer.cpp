/*++
  Module Name:

  spacer_adhoc_generalizer.cpp

  Abstract:

  - Checks if SPACER is diverging in mining similar lemmas from the same lemma group.
  - From the diverging lemma group make conjecture for a summarizing lemma candidate.

  Author:

  Jeff

  Revision History:

  --*/

/*
  TODO:
  2. lift parametres upto top-level (threshold is now hard-coded to 5 while distance-threshold is hard-coded to 10)
  3. Boolean literals need to be handled seperately

*/



#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_sem_matcher.h"
#include "muz/spacer/spacer_antiunify.h"

#include "ast/substitution/substitution.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/expr_abstract.h"
#include "ast/rewriter/var_subst.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/factor_equivs.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/substitution/matcher.h"
#include "ast/expr_functors.h"
#include "ast/rewriter/var_subst.h"


using namespace spacer;

namespace spacer {

    lemma_adhoc_generalizer::lemma_adhoc_generalizer(context &ctx, int theta)
        : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m), m_within_scope(m){ threshold = theta; }

    bool lemma_adhoc_generalizer::is_linear_diverging(lemma_ref &lemma){
        return false;
    }

    // Quality of the substitution
    int lemma_adhoc_generalizer::distance(substitution &s){
        int dis = 0;
        for(unsigned j = 0; j < s.get_num_bindings(); j++){
            expr_offset r;
            var_offset  v;
            // current binding is v --> r
            s.get_binding(j, v, r);
            expr_ref e(m);
            e = r.get_expr();
            TRACE("spacer_divergence_detect",
                  tout << "num bindings: " << s.get_num_bindings() << "\n";
                  tout << "sub: v!" << v.first << " = " << e << "\n";);
            SASSERT(v.second == 0 && "Unexpected non-zero offset in a substitution");

            // compute cost of the current expression
            expr *e2 = nullptr;
            // strip negation
            if (m.is_not(e), e2){
                e = e2;
            }

            if (m.is_bool(e)){ // XXX Booleans are bad
                dis += 11;
            }

            else if(m_arith.is_numeral(e)){
                dis += 1;
            } else if (is_uninterp_const(e)){
                dis += 2;
            } else if (is_app(e)){
                dis += 6*(to_app(e)->get_depth());
            }
        }
        return dis;
    }

    // Queue up related lemmas into m_within_scope
    // For example, traverse through ancestors and collect their lemmas
    void lemma_adhoc_generalizer::scope_in(lemma_ref &lemma, int gen){
        m_within_scope.reset();
        pob *p = &*lemma->get_pob();
        pred_transformer &pt = p->pt();
        int i = 0;
        while( (gen < 0 || i < gen) && p->parent()){
            // Comparing signature of starting lemma against ancestors' pt sig, continue if mismatched
            if( &pt != &(p->pt())){
                TRACE("spacer_divergence_detect_dbg", tout << "pt sig mismatched: " << "\n";);
                p = p->parent();
                continue;
            }
            for(auto &lms:p->lemmas()){
                expr_ref e = mk_and(lms->get_cube());
                m_within_scope.push_back(e);
            }
            p = p->parent();
            i++;
        }
    }

    // scoping in ohter lemmas sharing the same PT (within +- num_frames)
    void lemma_adhoc_generalizer::scope_in_same_pt(lemma_ref &lemma, int num_frames){
        m_within_scope.reset();
        pob *p = &*lemma->get_pob();
        pred_transformer &pt = p->pt();
        expr_ref_vector lemmas_with_same_pt(m);
        TRACE("spacer_divergence_detect_samept", tout << "L: " << mk_pp(mk_and(lemma->get_cube()), m) << "\n";);
        int i = 0; // pt.get_num_levels() > num_frames ? (pt.get_num_levels() - num_frames) : num_frames;
        while(i <= pt.get_num_levels()){
            pt.get_lemmas_at_frame(i, lemmas_with_same_pt);
            // for (auto &e:lemmas_with_same_pt){
            // }
            m_within_scope.push_back(mk_and(lemmas_with_same_pt));
            i++;
            TRACE("spacer_divergence_detect_samept",
                  tout << i << " : " << mk_pp(mk_and(lemmas_with_same_pt), m) << "\n";
                  );
        }
    }


    // Now we have the detection next step is generalization of lemma groups
    // 1) monotonic conjectures (only constant terms are varying; not coefficient?)
    //    requires we remember diff between group representative and each memeber (this would also give us the direction of constant)
    // 2) conjectures across lemma groups
    //

    // always using cube as 1st argument to antiU; but it doesn't have to be
    // TODO 1 lemma :: and (...) -> get_arg_num (...)
    void lemma_adhoc_generalizer::operator()(lemma_ref &lemma){
        expr_ref cube(m);
        cube = mk_and(lemma->get_cube());
        TRACE("spacer_divergence_detect_samept", tout << "Initial cube: " << cube << "\n";);
        TRACE("spacer_divergence_detect", tout << "Num of literal: " << num_uninterp_const(to_app(cube)) << "\n";);
        TRACE("spacer_divergence_detect", tout << "Num of numeral: " << num_numeral_const(to_app(cube)) << "\n";);

        scope_in_same_pt(lemma, 5);


        scope_in(lemma, 10);
        int counter = 0;
        anti_unifier antiU(m);
        expr_ref result(m);
        expr_ref_vector neighbours(m);

        for(auto &s:m_within_scope){

            substitution subs1(m), subs2(m);

            TRACE("spacer_divergence_detect", tout << "s: " << mk_pp(s, m) << "\n";);
            antiU(cube , s, result, subs1, subs2);
            expr_ref applied(m);
            subs1.apply(result, applied);

            TRACE("spacer_divergence_detect", tout << "Num of var occurances in result: " << num_vars(result) << "\n";);

            int dis = distance(subs1);

            // penalize singleton cubes for experiment
            // if(!m.is_and(cube)) {
            //     dis += 7;
            // }

            if(dis > 0 && dis <= 6) {
                counter++;
                TRACE("spacer_divergence_detect_dbg", tout
                      << "scoped lem: " << mk_pp(s, m) << "\n"
                      << "anti-result: " << mk_pp(result, m) << "\n"
                      << "anti-applied: " << mk_pp(applied, m) << "\n"
                      << "dis: " << dis << "\n";);
                neighbours.push_back(s);
            }

            if(counter >= threshold){
                // Try to generate good summary lemma before bailout
                // (1). (x >= N1) && (y <= N2) ===> if N1 >= N2 then x >= y
                if(m.is_and(cube)){
                    app * fst = to_app(to_app(cube)->get_arg(0));
                    app * snd = to_app(to_app(cube)->get_arg(1));
                    TRACE("spacer_divergence_bingo",
                          tout << " fst : " << mk_pp(fst, m) << "\n"
                               << " snd : " << mk_pp(snd, m) << "\n"
                          ;);

                        if(m_arith.is_ge(fst) && m_arith.is_le(snd)){
                            rational n1, n2;
                            if(m_arith.is_numeral(fst->get_arg(1), n1) && m_arith.is_numeral(snd->get_arg(1), n2)){
                                if(n1 > n2){
                                    TRACE("spacer_divergence_bingo", tout << n1 << " / " << n2 << "\n";);
                                    expr_ref_vector conjecture(m);
                                    conjecture.push_back( m_arith.mk_gt(fst->get_arg(0), snd->get_arg(0)) );
                                    TRACE("spacer_divergence_bingo",
                                          tout << mk_pp(conjecture.back(), m) << "\n";);
                                    pred_transformer &pt = lemma->get_pob()->pt();
                                    unsigned uses_level = 0;
                                    if(pt.check_inductive(lemma->level(), conjecture, uses_level, lemma->weakness())){
                                        TRACE("spacer_divergence_bingo", tout << "Inductive!" << "\n";);
                                        lemma->update_cube(lemma->get_pob(), conjecture);
                                        lemma->set_level(uses_level);
                                        counter = 0;
                                        return;
                                    } else {
                                        TRACE("spacer_divergence_bingo", tout << "Not inductive!" << "\n";);
                                        return;
                                    }
                                }
                            }

                    }
                }
                // End of trying here; time to bailout!

                TRACE("spacer_divergence_detect_dbg", tout << "Reached repetitive lemma threshold, Abort!" << "\n";);
                TRACE("spacer_diverg_report",
                      tout << "Abort due to: " << mk_pp(applied, m)
                      << "\n--- neighbours ---\n";
                      for(auto &l:neighbours){
                          tout << mk_pp(l, m) << "\n";
                      };
                      tout << "--- other statistics ---\n"
                      << "Number of args: " << to_app(cube)->get_num_args() << "\n"
                      << "Number of literals: " << ((!m.is_and(cube)) ? "1" : std::to_string(to_app(cube)->get_num_args())) << "\n"
                      << "pattern from antiU: " << mk_pp(result, m) << "\n"
                      ;);
                throw unknown_exception();
            }
        }
    }


    /*
void lemma_adhoc_generalizer::operator()(lemma_ref &lemma){
  TRACE("spacer_adhoc_genz",
    tout << "Initial cube: " << mk_and(lemma->get_cube()) << "\n";);

  if(lemma->get_cube().size() < 2){
      TRACE("spacer_adhoc_genz", tout << "singleton cube!"  << "\n";);
  }

  // pred_transformer &pt = lemma->get_pob()->pt();
  pob *p = &*lemma->get_pob();

  // parent-matching
  unsigned i = 0;
  unsigned match_count = 0;
  sem_matcher smatcher(m);
  anti_unifier antiU(m);
  substitution subs1(m), subs2(m);
  expr_ref result(m);
  expr_ref result_buffer(m.mk_true(), m);

  subs1.reserve(2, to_app(lemma->get_expr())->get_depth());
  subs2.reserve(2, to_app(lemma->get_expr())->get_depth());

  while(p->parent()){
    i = 0;
    p = p->parent();

    for(auto &lms:p->lemmas()){
      antiU( mk_and(lemma->get_cube()), mk_and(lms->get_cube()), result, subs1, subs2);
      int dis = smatcher.distance(result, subs1);
      if(dis > 0 && dis < 10) {
          TRACE("adhoc_parent_matching",
                tout << "Parent_" << i++ << ": "<< mk_and(lms->get_cube()) << "\n"
                << "anti res: " << result << "\n"
                << "distance: " << dis << "\n";);
          match_count++;
       }
      if(match_count >= 5){
          TRACE("adhoc_parent_matching_long", tout << "LONG MATCHes (>=5)" << "\n"
                << "Parent_" << i++ << ": "<< mk_and(lms->get_cube()) << "\n"
                << "anti res: " << result << "\n"
                << "distance: " << dis << "\n";);

      }
    }
  }

    */


    /* MISC */

    int lemma_adhoc_generalizer::num_numeral_const(app *a){
        int count = 0;
        for(expr *e : *a){
            if(m_arith.is_numeral(e)){
                count++;
            }
            else if(is_app(e)){
                count += num_numeral_const(to_app(e));
            }
        }
        return count;
    }

    int lemma_adhoc_generalizer::num_uninterp_const(app *a){
        int count = 0;
        for(expr *e : *a){
            if(is_uninterp_const(e)){
                count++;
            }
            else if(is_app(e)){
                count += num_uninterp_const(to_app(e));
            }
        }
        return count;
    }


    // number of variable occurances in a given e (counting repetitive occurances)
    int lemma_adhoc_generalizer::num_vars(expr *e){
        int count = 0;
        if(is_var(e)) {count++;}
        else if(is_app(e)){
          for(expr *x: *to_app(e)){
             count += num_vars(x);
          }
        }
        return count;
    }


}

// two ways of creating pattern: 1. (one pattern against all lemmas in scope) 2. (keep having different anti-unified patterns)
