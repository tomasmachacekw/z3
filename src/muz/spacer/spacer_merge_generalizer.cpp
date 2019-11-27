/*

  Suite of merging strategies.

*/
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_util.h"
#include "smt/smt_solver.h"

namespace spacer {
lemma_merge_generalizer::lemma_merge_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m),
      m_cvx_cls(m, ctx.use_sage()), m_dim_frsh_cnsts(m), m_dim_vars(m) {}

void lemma_merge_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);

    if (core(lemma)) {
        TRACE("merge_dbg", tout << "Lemma cube after merge generalization: "
                                << lemma->get_cube() << "\n";);
    }
}

void lemma_merge_generalizer::to_real(expr_ref &fml) {
    if (m_arith.is_numeral(fml)) return;
    if (is_uninterp_const(fml) && m_arith.is_int(fml)) {
        fml = m_arith.mk_to_real(fml);
        return;
    }
    if (m_arith.is_arith_expr(fml)) {
        app *fml_app = to_app(fml);
        unsigned N = fml_app->get_num_args();
        expr_ref_vector nw_args(m);
        expr_ref chld(m);
        for (unsigned i = 0; i < N; i++) {
            chld = fml_app->get_arg(i);
            to_real(chld);
            nw_args.push_back(chld);
        }
        fml = m.mk_app(fml_app->get_family_id(), fml_app->get_decl_kind(),
                       nw_args.size(), nw_args.c_ptr());
    }
}

void lemma_merge_generalizer::to_real(const expr_ref_vector &fml,
                                      expr_ref &nw_fml) {
    expr_ref lhs(m), rhs(m);
    expr_ref_vector rw_fml(m);
    for (auto &e : fml) {
        if (!(m.is_eq(e) || m_arith.is_arith_expr(e))) continue;
        app *e_app = to_app(e);
        SASSERT(to_app(e)->get_num_args() == 2);
        lhs = e_app->get_arg(0);
        rhs = e_app->get_arg(1);
        to_real(rhs);
        to_real(lhs);
        rw_fml.push_back(to_expr(m.mk_app(e_app->get_family_id(),
                                          e_app->get_decl_kind(), lhs, rhs)));
    }
    nw_fml = mk_and(rw_fml);
}

void lemma_merge_generalizer::add_dim_vars(const lemma_cluster &lc) {
    const expr_ref &pattern(lc.get_pattern());
    expr_offset r;
    std::pair<unsigned, unsigned> v;
    unsigned n_vars = get_num_vars(pattern);
    // temporary pointer to an existing expr
    expr_ref var(m);
    const lemma_info_vector &lemmas(lc.get_lemmas());
    const substitution &t_sub(lemmas[0].get_sub());
    for (unsigned j = 0; j < n_vars; j++) {
        // get var id
        t_sub.get_binding(j, v, r);
        // get variable
        var = m.mk_var(v.first, m_arith.mk_int());
        m_cvx_cls.set_dimension(j, var);
        m_dim_vars[j] = var;
        app_ref var_app(m);
        var_app = m.mk_fresh_const("mrg_cvx", m_arith.mk_int());
        // TODO: do we need two variables for a <= x <= b ?
        m_dim_frsh_cnsts[j] = var_app;
    }
}

void lemma_merge_generalizer::add_points(const lemma_cluster &lc) {
    vector<rational> point;
    unsigned n_vars = get_num_vars(lc.get_pattern());
    const lemma_info_vector &lemmas(lc.get_lemmas());
    expr_offset r;
    std::pair<unsigned, unsigned> v;
    for (const lemma_info &lemma : lemmas) {
        const substitution &sub(lemma.get_sub());
        point.reset();
        for (unsigned j = 0; j < n_vars; j++) {
            sub.get_binding(j, v, r);
            rational coeff;
            bool is_int = false;
            m_arith.is_numeral(r.get_expr(), coeff, is_int);
            SASSERT(is_int);
            point.push_back(coeff);
        }
        m_cvx_cls.push_back(point);
    }
}
void lemma_merge_generalizer::reset(unsigned n_vars) {
    // start convex closure computation
    m_cvx_cls.reset(n_vars);
    m_dim_vars.reset();
    m_dim_frsh_cnsts.reset();
    m_dim_frsh_cnsts.reserve(n_vars);
    m_dim_vars.reserve(n_vars);
    m_exact = true;
}

bool lemma_merge_generalizer::core(lemma_ref &lemma) {
    lemma_cluster *pt_cls = (&*lemma->get_pob())->pt().clstr_match(lemma);
    if (pt_cls == nullptr) return false;
    lemma_cluster lc(*pt_cls);

    lc.add_lemma(lemma);

    const expr_ref &pattern(lc.get_pattern());

    TRACE("merge_dbg",
          tout << "Start merging with lemma cube: " << lemma->get_cube()
               << "\n Discovered pattern: " << pattern << "\n";);

    unsigned n_vars = get_num_vars(pattern);
    SASSERT(n_vars > 0);
    reset(n_vars);
    // create and add dim vars
    add_dim_vars(lc);
    // add points
    add_points(lc);

    expr_ref_vector cls(m);
    m_exact = m_cvx_cls.closure(cls);
    CTRACE("merge_dbg", !m_exact,
           tout << "Convex closure introduced new variables. Closure is"
                << mk_and(cls) << "\n";);

    if (!m_exact) {
        // Add the new variables to the list of variables to be eliminated
        const var_ref_vector &vars = m_cvx_cls.get_nw_vars();
        app_ref var_app(m);
        for (auto v : vars) {
            m_dim_vars.push_back(to_expr(v));
            var_app = m.mk_fresh_const("mrg_syn_cvx", m_arith.mk_real());
            m_dim_frsh_cnsts.push_back(var_app);
        }
    }

    cls.push_back(pattern.get());
    expr_ref cvx_pattern(m);
    var_to_const(mk_and(cls), cvx_pattern);

    // TODO check mbp over approximates cvx cls and update lemma
    return false;
}

void lemma_merge_generalizer::var_to_const(expr *pattern,
                                           expr_ref &rw_pattern) {
    expr_safe_replace s(m);
    obj_map<expr, expr *> sub;
    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        s.insert(m_dim_vars[i].get(), to_expr(m_dim_frsh_cnsts[i].get()));
    }
    s(pattern, rw_pattern);
    TRACE("merge_dbg_verb", tout << "Rewrote all vars into u_consts "
                                 << mk_pp(pattern, m) << " into " << rw_pattern
                                 << "\n";);

    expr_ref_vector nw_pattern(m);
    flatten_and(rw_pattern, nw_pattern);

    if (m_exact) {
        TRACE("merge_dbg_verb", tout << "Rewrote " << mk_pp(pattern, m)
                                     << " into " << rw_pattern << "\n";);
        return;
    }

    to_real(nw_pattern, rw_pattern);
    TRACE("merge_dbg_verb", tout << "To real produced " << rw_pattern << "\n";);
    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        if (m_arith.is_real(m_dim_frsh_cnsts[i].get())) continue;
        app_ref var_app(m);
        var_app = m_arith.mk_to_real(m_dim_frsh_cnsts[i].get());
        m_dim_frsh_cnsts[i] = var_app;
    }
    TRACE("merge_dbg_verb", tout << "Rewrote " << mk_pp(pattern, m) << " into "
                                 << rw_pattern << "\n";);
}

void lemma_merge_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.merge", m_st.watch.get_seconds());
    m_cvx_cls.collect_statistics(st);
}

} // namespace spacer
