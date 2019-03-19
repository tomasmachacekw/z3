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

  TRACE flags:
  1. spacer_diverge_report: for conclusive summary
  2. spacer_diverge_dbg: for debugging information
*/



#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_sem_matcher.h"
#include "muz/spacer/spacer_antiunify.h"
#include "muz/spacer/spacer_util.h"

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

    lemma_adhoc_generalizer::lemma_adhoc_generalizer(context &ctx, int theta, bool if_bailout)
        : lemma_generalizer(ctx),
          m(ctx.get_ast_manager()),
          m_arith(m),
          m_within_scope(m){
        threshold = theta;
        diverge_bailout = if_bailout;
    }

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
            TRACE("spacer_diverge_dbg",
                  tout << "num bindings: " << s.get_num_bindings() << "\n"
                       << "sub: v!" << v.first << " = " << e << "\n";);
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
    // void lemma_adhoc_generalizer::scope_in(lemma_ref &lemma, int gen){
    //     m_within_scope.reset();
    //     pob *p = &*lemma->get_pob();
    //     pred_transformer &pt = p->pt();
    //     int i = 0;
    //     while( (gen < 0 || i < gen) && p->parent()){
    //         // Comparing signature of starting lemma against ancestors' pt sig, continue if mismatched
    //         if( &pt != &(p->pt())){
    //             TRACE("spacer_diverge_dbg", tout << "pt sig mismatched: " << "\n";);
    //             p = p->parent();
    //             continue;
    //         }
    //         for(auto &lms:p->lemmas()){
    //             expr_ref e = mk_and(lms->get_cube());
    //             m_within_scope.push_back(e);
    //         }
    //         p = p->parent();
    //         i++;
    //     }
    // }

    void lemma_adhoc_generalizer::scope_in_leq(lemma_ref &lemma, int num_frames){
        m_within_scope.reset();
        pred_transformer &pt = (&*lemma->get_pob())->pt();
        lemma_ref_vector lemmas_with_same_pt;
        pt.get_lemmas_at_frame_leq(pt.get_num_levels(), lemmas_with_same_pt);
        TRACE("spacer_diverge_dbg",
              tout << "Lem: " << mk_pp(mk_and(lemma->get_cube()), m) << "\n"
                   << "pt.get_num_levels(): " << pt.get_num_levels() << "\n"
                   << "size of lemmas_with_same_pt: " << lemmas_with_same_pt.size() << "\n";
              for(auto &l: lemmas_with_same_pt){
                  tout << mk_pp(mk_and(l->get_cube()), m) << "\n";
              };);
        for(auto &l: lemmas_with_same_pt){
            if(l->level()!=0)
                m_within_scope.push_back(mk_and(l->get_cube()));
        };
        }

    void lemma_adhoc_generalizer::scope_in_geq(lemma_ref &lemma, int num_frames){
        m_within_scope.reset();
        pred_transformer &pt = (&*lemma->get_pob())->pt();
        lemma_ref_vector lemmas_with_same_pt;
        pt.get_lemmas_at_frame_geq(pt.get_num_levels(), lemmas_with_same_pt);
        for(auto &l: lemmas_with_same_pt){
            if(l->level()!=0)
                m_within_scope.push_back(mk_and(l->get_cube()));
        };
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
        TRACE("spacer_diverge_dbg_neighbours",
              tout << "Initial cube: " << cube << "\n"
                   << "Num of literal: " << num_uninterp_const(to_app(cube)) << "\n"
                   << "Num of numeral: " << num_numeral_const(to_app(cube)) << "\n";);

        scope_in_geq(lemma, 5);
        // scope_in_leq(lemma, 5);

        TRACE("spacer_diverge_dbg_neighbours",
              for(auto &s:m_within_scope){
                  tout << "s_leq: " << mk_pp(s, m) << "\n";
              };);

        int counter = 0;
        int i;
        for(i = 0; i < m_within_scope.size(); i++){
            expr_ref s(m);
            s = m_within_scope.get(i);
            anti_unifier antiU(m);
            expr_ref result(m);
            substitution subs1(m), subs2(m);
            expr_ref_vector neighbours(m);

            antiU(cube , s, result, subs1, subs2);
            expr_ref applied(m);
            subs1.apply(result, applied);
            int dis = distance(subs1);
            TRACE("spacer_diverge_dbg_neighbours",
                  tout << "s: " << mk_pp(s, m) << " dis: " << dis << "\n";
                ;);
            // XXX penalize singleton cubes for experiment
            // if(!m.is_and(cube)) {
            //     dis += 7;
            // }

            if(dis > 0 && dis <= 6) {
                counter++;
                TRACE("spacer_diverge_dbg", tout
                      << "scoped lem: " << mk_pp(s, m) << "\n"
                      << "anti-result: " << mk_pp(result, m) << "\n"
                      << "anti-applied: " << mk_pp(applied, m) << "\n"
                      << "counter: " << counter << "\n"
                      << "dis: " << dis << "\n";);
                neighbours.push_back(s);
            }

            if(counter >= threshold){
                /* among neighbours, finding best antiU pattern */
                /* This gives more robustness against communtative operators */
                substitution subsa(m), subsb(m);
                int min_dis = 6;
                expr_ref min_result(m);

                // expr_ref normedCube(m);
                // normalize(cube, normedCube, true, false);
                // TRACE("spacer_diverge_report",
                //       tout << "Cube: " << mk_pp(cube, m) << "\n"
                //            << "normed cube: " << mk_pp(normedCube, m) << "\n";);

                for(auto &n:neighbours){
                    subsa.reset();
                    subsb.reset();
                    antiU(cube , n, result, subsa, subsb);
                    int dis = distance(subsa);
                    if(dis < min_dis){
                        min_dis = dis;
                        min_result = result;
                    }
                }
                // XXX this will make pattern for lia-0010 too specific!
                // TODO We really need true sorting on lemmas (might be expensive so only do on the neighbours)
                result = min_result;

                /* Mitigation */
                // Try to generate good summary lemma before bailout
                // (1). (x >= N1) && (y <= N2) ===> if N1 > N2 then x > y
                if(m.is_and(cube)){
                    app * fst = to_app(to_app(cube)->get_arg(0));
                    app * snd = to_app(to_app(cube)->get_arg(1));
                    TRACE("spacer_diverge_dbg_neighbours",
                          tout << " fst : " << mk_pp(fst, m) << "\n"
                               << " snd : " << mk_pp(snd, m) << "\n"
                          ;);

                    if(m_arith.is_ge(fst) && m_arith.is_le(snd)){
                        rational n1, n2;
                        if(m_arith.is_numeral(fst->get_arg(1), n1) && m_arith.is_numeral(snd->get_arg(1), n2)){
                            if(n1 > n2){
                                TRACE("spacer_diverge_dbg", tout << n1 << " / " << n2 << "\n";);
                                expr_ref_vector conjecture(m);
                                conjecture.push_back( m_arith.mk_gt(fst->get_arg(0), snd->get_arg(0)) );
                                if(check_inductive_and_update(lemma, conjecture)){
                                    TRACE("spacer_diverge_report",
                                          tout << "Pattern discovered due to: " << mk_pp(applied, m)
                                          << "\n--- neighbours ---\n";
                                          for(auto &l:neighbours){
                                              tout << mk_pp(l, m) << "\n";
                                          };
                                          tout << "Inductive invariant found: " << mk_pp(conjecture.get(0), m) << "\n"
                                          ;);
                                    return;
                                };
                                }
                            }

                    }
                    // XXX Hackish approach for 0007
                    // if(m_arith.is_le(fst) && m_arith.is_ge(snd)){
                    //     rational n1, n2;
                    //     if(m_arith.is_numeral(fst->get_arg(1), n1) && m_arith.is_numeral(snd->get_arg(1), n2)){
                    //         if(n2 > n1){
                    //             TRACE("spacer_divergence_bingo", tout << n1 << " / " << n2 << "\n";);
                    //             expr_ref_vector conjecture(m);

                    //             conjecture.push_back( m_arith.mk_eq(m_arith.mk_add(fst->get_arg(0),m_arith.mk_int(1))
                    //                                                                , snd->get_arg(0)) );
                    //             if(check_inductive_and_update(lemma, conjecture)){ return; };
                    //         }
                    //     }
                    // }
                }


                if(is_app(result)){
                    app * pattern = to_app(result);
                    expr_ref out(m);
                    expr_ref_vector conjecture(m);

                    // XXX Ideally replaces code above
                    // if(cross_halfplanes(to_app(cube), out)){
                    //     conjecture.push_back(out);
                    //     if(check_inductive_and_update(lemma, conjecture)){
                    //         TRACE("spacer_diverg_report",
                    //               tout << "Pattern discovered due to: " << mk_pp(applied, m)
                    //               << "\n--- neighbours ---\n";
                    //               for(auto &l:neighbours){
                    //                   tout << mk_pp(l, m) << "\n";
                    //               };
                    //               tout << "Inductive invariant found: " << mk_pp(out, m) << "\n"
                    //               ;);
                    //         return;
                    //     };
                    // }

                    out.reset();
                    if(monotonic_coeffcient(pattern, out)){
                        // ENSURE(out);
                        conjecture.push_back(out);
                        if(check_inductive_and_update(lemma, conjecture)){
                            TRACE("spacer_diverge_report",
                                  tout << "Pattern discovered due to: " << mk_pp(applied, m)
                                       << "\n--- neighbours ---\n";
                                  for(auto &l:neighbours){
                                      tout << mk_pp(l, m) << "\n";
                                  };
                                  tout << "Inductive invariant found: " << mk_pp(out, m) << "\n"
                                  ;);
                            return;
                        };
                    }
                }

                // End of trying here; time to bailout!
                if(diverge_bailout){
                TRACE("spacer_diverge_report", tout << "Reached repetitive lemma threshold, Abort!" << "\n";);
                TRACE("spacer_diverge_report",
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
    }

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

    void lemma_adhoc_generalizer::uninterp_consts(app *a, expr_ref_vector &out){
        for(expr *e : *a){
            if(is_uninterp_const(e)){
                out.push_back(e);
            }
            else if(is_app(e)){
                uninterp_consts(to_app(e), out);
            }
        }

    }

    void lemma_adhoc_generalizer::uninterp_consts_with_var_coeff(app *a
                                                                 , expr_ref_vector &out
                                                                 , bool has_var_coeff)
    {
        for(expr *e : *a){
            if(is_uninterp_const(e) && has_var_coeff){
                out.push_back(e);
            }
            else if(is_app(e)){
                uninterp_consts_with_var_coeff(to_app(e), out, m_arith.is_mul(e) && (num_vars(e)>=1) );
            }
        }

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

    bool lemma_adhoc_generalizer::check_inductive_and_update(lemma_ref &lemma, expr_ref_vector conj){
        TRACE("spacer_diverge_dbg", tout << "Attempt to update lemma with: "
              << mk_pp(conj.back(), m) << "\n";);
        pred_transformer &pt = lemma->get_pob()->pt();
        unsigned uses_level = 0;
        if(pt.check_inductive(lemma->level(), conj, uses_level, lemma->weakness())){
            TRACE("spacer_diverge_dbg", tout << "Inductive!" << "\n";);
            lemma->update_cube(lemma->get_pob(), conj);
            lemma->set_level(uses_level);
            return true;
        } else {
            TRACE("spacer_diverge_dbg", tout << "Not inductive!" << "\n";);
            return false;
        }
    }

    bool lemma_adhoc_generalizer::cross_halfplanes(app *pattern, expr_ref &out){
        if(m.is_and(pattern) && pattern->get_num_args() == 2){
            app * fst = to_app(pattern->get_arg(0));
            app * snd = to_app(pattern->get_arg(1));
            TRACE("spacer_diverge_dbg",
                  tout << " fst : " << mk_pp(fst, m) << "\n"
                       << " snd : " << mk_pp(snd, m) << "\n"
                  ;);
            if(m_arith.is_ge(fst) && m_arith.is_le(snd)){
                rational n1, n2;
                if(m_arith.is_numeral(fst->get_arg(1), n1) && m_arith.is_numeral(snd->get_arg(1), n2)){
                    if(n1 > n2){
                        out = m_arith.mk_gt(fst->get_arg(0), snd->get_arg(0));
                        return true;
                    }
                }
            }
        }
        return false;
    }

    // chc-lia-0008
    // pattern: x * A + y * B + (n_1 * C) >= n_2
    // candidate: x * A + y * B >= (-1 * n_1 * C) + n_2
    // candidate: A + B >= (-1 * n_1 * C) + n_2
    // candidate: A + B >= 0
    bool lemma_adhoc_generalizer::monotonic_coeffcient(app *pattern, expr_ref &out){
        expr_ref_vector uni_consts(m), var_coeff(m);
        if(m_arith.is_ge(pattern) || m_arith.is_gt(pattern)){
            uninterp_consts_with_var_coeff(pattern, var_coeff, false);
            // If we have uninterp_consts_with_var_coeff
            if(var_coeff.size() > 0){
                uninterp_consts(pattern, uni_consts);
                TRACE("spacer_diverge_report",
                      tout << "Found pattern similar to 0008.smt2" << "\n";
                      tout << "Pattern: " << mk_pp(pattern, m) << "\n";
                      tout << "Uninterpreted Const with Var coeff:" << "\n";
                      for(expr * c:var_coeff){
                          tout << mk_pp(c, m) <<"\n";
                      }
                      ;);
                expr_ref sum(m);
                sum = var_coeff.get(0);
                for(int i = 1; i < var_coeff.size(); i++){
                    sum = m_arith.mk_add(sum, var_coeff.get(i));
                }
                out = m_arith.mk_lt(sum, m_arith.mk_int(0));
                return true;
            }
        }
        return false;
    }
}
