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
        // TODO port from adhoc_gen
        return false;
    }
}
