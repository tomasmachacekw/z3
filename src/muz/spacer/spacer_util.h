/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_util.h

Abstract:

    Utility functions for SPACER.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.
    Arie Gurfinkel
    Anvesh Komuravelli

Revision History:

--*/

#ifndef _SPACER_UTIL_H_
#define _SPACER_UTIL_H_

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "util/obj_hashtable.h"
#include "util/ref_vector.h"
#include "util/trace.h"
#include "util/vector.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/expr_map.h"
#include "model/model.h"

#include "util/stopwatch.h"
#include "muz/spacer/spacer_antiunify.h"

class model;
class model_core;

namespace spacer {

    inline unsigned infty_level () {
        return UINT_MAX;
    }

    inline bool is_infty_level(unsigned lvl) {
        // XXX: level is 16 bits in class pob
        return lvl >= 65535;
    }

    inline unsigned next_level(unsigned lvl) {
        return is_infty_level(lvl)?lvl:(lvl+1);
    }

    inline unsigned prev_level (unsigned lvl) {
        if (is_infty_level(lvl)) return infty_level();
        if (lvl == 0) return 0;
        return lvl - 1;
    }

    struct pp_level {
        unsigned m_level;
        pp_level(unsigned l): m_level(l) {}
    };

    inline std::ostream& operator<<(std::ostream& out, pp_level const& p) {
        if (is_infty_level(p.m_level)) {
            return out << "oo";
        } else {
            return out << p.m_level;
        }
    }

    typedef ptr_vector<app> app_vector;
    typedef ptr_vector<func_decl> decl_vector;
    typedef obj_hashtable<func_decl> func_decl_set;

    /**
       \brief hoist non-boolean if expressions.
    */

    void to_mbp_benchmark(std::ostream &out, const expr* fml, const app_ref_vector &vars);


    // TBD: deprecate by qe::mbp
    /**
     * do the following in sequence
     * 1. use qe_lite to cheaply eliminate vars
     * 2. for remaining boolean vars, substitute using M
     * 3. use MBP for remaining array and arith variables
     * 4. for any remaining arith variables, substitute using M
     */
    void qe_project (ast_manager& m, app_ref_vector& vars,
                     expr_ref& fml, model &mdl,
                     bool reduce_all_selects=false,
                     bool native_mbp=false,
                     bool dont_sub=false);

    // deprecate
    void qe_project (ast_manager& m, app_ref_vector& vars, expr_ref& fml,
                     model_ref& M, expr_map& map);

    // TBD: sort out
    void expand_literals(ast_manager &m, expr_ref_vector& conjs);
    void compute_implicant_literals(model &mdl,
                                    expr_ref_vector &formula,
                                    expr_ref_vector &res);
    void simplify_bounds (expr_ref_vector &lemmas);
    void normalize(expr *e, expr_ref &out, bool use_simplify_bounds = true, bool factor_eqs = false);
    void normalize_order(expr *e, expr_ref &out);
    /**
     * Ground expression by replacing all free variables by skolem
     * constants. On return, out is the resulting expression, and vars is
     * a map from variable ids to corresponding skolem constants.
     */
    void ground_expr (expr *e, expr_ref &out, app_ref_vector &vars);

    void mbqi_project(model &mdl, app_ref_vector &vars, expr_ref &fml);

    bool contains_selects (expr* fml, ast_manager& m);
    void get_select_indices (expr* fml, app_ref_vector& indices);

    void find_decls (expr* fml, app_ref_vector& decls, std::string& prefix);

    /**
     * extended pretty-printer
     * used for debugging
     * disables aliasing of common sub-expressions
     */
    struct mk_epp : public mk_pp {
        params_ref m_epp_params;
        expr_ref m_epp_expr;
    mk_epp(ast *t, ast_manager &m, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = nullptr);
        void rw(expr *e, expr_ref &out);
    };

    /**
       Auxiliary functions used in C(luster) S(plit) M(erge) project
    */

    // unsigned get_num_uninterp_const(expr *a);
    // void get_uninterp_consts(expr *a, expr_ref_vector &out);
    // bool has_nonlinear_mul(expr *e, ast_manager &m);
    // // int num_numeral_const(app *a);
    // unsigned get_num_vars(expr *e);
    unsigned get_num_uninterp_consts(expr *a);
    void get_uninterp_consts(expr *a, expr_ref_vector &out);
    bool has_nonlinear_mul(expr *e, ast_manager &m);
    /// Returns number of free variables in a given expression 
    unsigned get_num_vars(expr *e);

    void get_uninterp_consts_with_var_coeff(const expr *e, expr_ref_vector &out);
    void get_uninterp_consts_with_pos_coeff(const expr *e, expr_ref_vector &out);
    void get_uninterp_consts_with_neg_coeff(const expr *e, expr_ref_vector &out);

    bool is_ge_or_gt(const expr *e, expr_ref &lhs, expr_ref &rhs);
    bool is_le_or_lt(const expr *e, expr_ref &lhs, expr_ref &rhs);
    // order by term instead of ast_lt
    struct term_order_proc {
        ast_manager &m;
        term_order_proc(ast_manager &mgr) : m(mgr){}
        void uninterp_consts(app *a, expr_ref_vector &out){
            if(is_uninterp_const(a)){ out.push_back(a); }
            for(expr *e : *a){
                if(is_uninterp_const(e)){ out.push_back(e); }
                else if(is_app(e)){
                    for(expr *arg : *to_app(e)){
                        if(is_app(arg)){ uninterp_consts(to_app(arg), out); }
                    }
                }
            }
        }
        bool operator()(expr *arg1, expr *arg2){
            arith_util m_arith(m);
            expr *a1_1, *a1_2, *a2_1, *a2_2;
            ast_lt_proc comp;
            if(m_arith.is_mul(arg1, a1_1, a1_2) && m_arith.is_mul(arg2, a2_1, a2_2)){
                return comp(a1_2, a2_2);
                // return (a1_2->get_id() < a2_2->get_id());
            }
            else if(m_arith.is_mul(arg1, a1_1, a1_2)){
                return comp(a1_2, arg2);
            }
            else if(m_arith.is_mul(arg2, a2_1, a2_2)){
                return comp(arg1, a2_2);
            }
            else if(is_app(arg1) && is_app(arg2)){
                // expr *t1 = nullptr;
                // expr *t2 = nullptr;
                // if(m.is_not(arg1, t1)){};
                // if(m.is_not(arg2, t2)){};
                STRACE("spacer_normalize_order", tout
                       << "both apps :" << mk_pp(arg1, m)
                       << "/" << mk_pp(arg2, m) << "\n";);
                expr_ref_vector uni_consts(m), uni_consts2(m);
                uninterp_consts(to_app(arg1), uni_consts);
                uninterp_consts(to_app(arg2), uni_consts2);
                TRACE("spacer_normalize_order",
                      tout << "unic1.size() :" << uni_consts.size() << " ";
                      tout << "unic2.size() :" << uni_consts2.size();
                      tout << "\n";);

                if(uni_consts.size() > 0 && uni_consts2.size() > 0){
                    ast_lt_proc comp;
                    expr * head = uni_consts.get(0);
                    expr * head2 = uni_consts2.get(0);
                    STRACE("spacer_normalize_order",
                           tout << "heads :" << mk_pp(head, m);
                           tout << (comp(head, head2) ? " < " : " > ");
                           tout << mk_pp(head2, m) << "\n\n";);

                    return comp(head, head2);
                }
            }
            // fallback to default comp
            STRACE("spacer_normalize_order",
                   tout << "args :" << mk_pp(arg1, m);
                   tout << (comp(arg1, arg2) ? " < " : " > ");
                   tout << mk_pp(arg2, m) << "\n\n";);
            return comp(arg1, arg2);
        }
    };
}

#endif
