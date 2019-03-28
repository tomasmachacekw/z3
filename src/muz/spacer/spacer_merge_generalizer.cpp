/*

  Suite of merging strategies.

*/
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"


using namespace spacer;
namespace spacer{
    lemma_merge_generalizer::lemma_merge_generalizer(context &ctx, int th) :
        lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m){
        threshold = th;
    }

    void lemma_merge_generalizer::operator()(lemma_ref &lemma){
        expr_ref_vector neighbours = lemma->get_neighbours();
        if(neighbours.size() > 0){
            substitution subs_newLemma(m), subs_oldLemma(m);
            expr_ref cube(m), normalizedCube(m), out(m);
            cube = mk_and(lemma->get_cube());
            normalize_order(cube, normalizedCube);
            TRACE("merge_dbg",
                  tout << "Start merging with lemma cube: " << mk_pp(normalizedCube, m) << "\n"
                  "Discovered pattern: " << mk_pp(neighbours.get(0), m) << "\n"
                  "Neighbours: " << mk_pp(neighbours.get(1), m) << "\n"
                  ;);
            bool res = monotonic_coeffcient(cube, to_app(neighbours.get(0)), out);
            if(res){
                expr_ref_vector conj(m);
                conj.push_back(out);
                if(check_inductive_and_update(lemma, conj))
                    return;
            }
            throw unknown_exception();
        }
    }


    /* with t <= k
       conjecture t <= infinite */
    bool lemma_merge_generalizer::leq_monotonic_k(expr_ref &literal, app *pattern, expr_ref &out){
        if(m_arith.is_le(pattern) && is_var(pattern->get_arg(1))){
            // out = forall int i m_arith.mk_le(pattern->get_arg(0), i)
            return true;
        }
        return false;
    }

    /* with t <= k , k < 0
       conjecture t <= 0 */
    bool lemma_merge_generalizer::leq_monotonic_neg_k(expr_ref &literal, app *pattern, expr_ref &out){
        if(m_arith.is_le(pattern) && is_var(pattern->get_arg(1))){
            SASSERT(is_app(literal));
            SASSERT(m_arith.is_numeral(to_app(literal)->get_arg(1)));
            rational r;
            m_arith.is_numeral(to_app(literal)->get_arg(1), r);
            if(r < -1){
                out = m_arith.mk_lt(pattern->get_arg(0), m_arith.mk_int(0));
                return true;
            } else if (r < 0){
                out = m_arith.mk_le(pattern->get_arg(0), m_arith.mk_int(0));
                return true;
            }
        }
        return false;
    }

    /* with t1 <= k1 && k2 <= t2 , k1 + c = k2
       conjecture t1 + c' <= t2 where 0 <= c' <= c */
    // XXX potentially return expr_ref_vector for c' from 0 to c
    bool lemma_merge_generalizer::merge_halfspaces(expr_ref &literal, app *pattern, expr_ref &out){
        rational k1, k2;
        expr_ref t1(m), t2(m);
        out = m_arith.mk_le(t1, t2);
        // out = m_arith.mk_le(m_arith.mk_add(t1, m_arith.mk_int(k2 - k1)), t2);
        return false;
    }

    /* with t1 = k1 && t2 = k2 , k1 + c = k2
       conjecture t1 + c' <= t2 where 0 <= c' <= c */
    // XXX should the lemma be t1 = k1 && t2 = k2 or we have to scan for all equalities?
    // XXX alternatively we can have another merge (and eq1 eq2 ... eqn)
    bool lemma_merge_generalizer::merge_lines(expr_ref &literal, app *pattern, expr_ref &out){
        rational k1, k2;
        expr_ref t1(m), t2(m);
        // out = m_arith.mk_le(t1, t2);
        out = m_arith.mk_eq(m_arith.mk_add(t1, m_arith.mk_int(k2 - k1)), t2);
        return false;
    }

    /* with k1 * t1 + k2 * t2 >= t3 , k1 > 0 , k2 > 0
       conjecture t1 + t2 >= 0
     */
    bool lemma_merge_generalizer::monotonic_coeffcient(expr_ref &literal, app *pattern, expr_ref &out){
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

    /* merging over neighbours
       if we know a < b + k and b < a + k
       we can conjecture a == b
     */
    bool lemma_merge_generalizer::neighbour_equality(expr_ref_vector &neighbour, expr_ref &out){
        return false;
    }

    bool lemma_merge_generalizer::check_inductive_and_update(lemma_ref &lemma, expr_ref_vector conj){
        TRACE("merge_dbg", tout << "Attempt to update lemma with: "
              << mk_pp(conj.back(), m) << "\n";);
        pred_transformer &pt = lemma->get_pob()->pt();
        unsigned uses_level = 0;
        if(pt.check_inductive(lemma->level(), conj, uses_level, lemma->weakness())){
            TRACE("merge_dbg", tout << "Inductive!" << "\n";);
            lemma->update_cube(lemma->get_pob(), conj);
            lemma->set_level(uses_level);
            return true;
        } else {
            TRACE("merge_dbg_", tout << "Not inductive!" << "\n";);
            return false;
        }
    }

    int lemma_merge_generalizer::num_vars(expr *e){
        int count = 0;
        if(is_var(e)) {count++;}
        else if(is_app(e)){
            for(expr *x: *to_app(e)){
                count += num_vars(x);
            }
        }
        return count;
    }

    void lemma_merge_generalizer::uninterp_consts_with_var_coeff(app *a,
                                                                 expr_ref_vector &out,
                                                                 bool has_var_coeff)
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



}
