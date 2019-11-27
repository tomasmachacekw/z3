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
    // TODO block lemma using cls
    return false;
}

void lemma_merge_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.merge", m_st.watch.get_seconds());
    m_cvx_cls.collect_statistics(st);
}

} // namespace spacer
