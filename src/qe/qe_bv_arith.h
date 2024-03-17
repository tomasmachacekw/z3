/***
 */
#pragma once
#include "model/model.h"
#include "ast/arith_decl_plugin.h"
#include "qe/qe_mbp.h"

namespace qe {
    bool contains(expr *e, expr *v);
    unsigned contains_num(expr *e, expr *v);

    void mk_add(expr_ref_vector &f, expr_ref &res);
    void mk_add(expr_ref t1, expr_ref t2, expr_ref &res);
    void mk_neg(expr *f, expr_ref &res);
    void mk_mul(expr* a, rational b, expr_ref &res);
    void mk_mul(expr* a, expr* b, expr_ref &c);
    void mk_exists(expr *f, app_ref_vector &vars, expr_ref &res);

    void split_legacy(expr_ref var, expr *lhs, expr *rhs, expr_ref& t1, expr_ref& t2, expr_ref& t2_neg, expr_ref& t3);
    void split_term_legacy(expr_ref var, expr* exp, expr_ref& t, expr_ref& t2, expr_ref& t2_neg);

    /**
       MBP for BV
     */

    class bv_project_plugin : public project_plugin {
        struct imp;
        imp* m_imp;
    public:
        bv_project_plugin(ast_manager& m);
        ~bv_project_plugin() override;
        bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) override;
        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        family_id get_family_id() override;
        void operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        void operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits, unsigned mbp_mode) override;
        vector<def> project(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        void saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) override;

        opt::inf_eps maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt);

        /**
         * \brief check if formulas are purified, or leave it to caller to ensure that
         * arithmetic variables nested under foreign functions are handled properly.
         */
        void set_check_purified(bool check_purified);
    };
};