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

    int num_uninterp_const(app *a);
    void uninterp_consts(app *a, expr_ref_vector &out);
    // int num_numeral_const(app *a);


    // order by term instead of ast_lt
    struct term_order_proc {
        ast_manager &m;
        term_order_proc(ast_manager &mgr) : m(mgr){}
        bool operator()(expr *arg1, expr *arg2){
            arith_util m_arith(m);
            expr *a1_1, *a1_2, *a2_1, *a2_2;
            if(m_arith.is_mul(arg1, a1_1, a1_2) && m_arith.is_mul(arg2, a2_1, a2_2)){
                return (a1_2->get_id() < a2_2->get_id());
            }
            return false;
        }
    };
}

#endif
