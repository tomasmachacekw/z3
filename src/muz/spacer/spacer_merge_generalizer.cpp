/*

  Suite of merging strategies.

*/
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_util.h"
#include "smt/smt_solver.h"
using namespace spacer;
namespace {
// returns that var in expr whose idx is x
// returns nullptr if var is not found
expr *var_find(expr *exp, unsigned x) {
    if (is_var(exp) && to_var(exp)->get_idx() == x) return exp;
    if (is_app(exp)) {
        app *app = to_app(exp);
        unsigned n_chld = app->get_num_args();
        for (unsigned i = 0; i < n_chld; i++) {
            expr *res = var_find(app->get_arg(i), x);
            if (res != nullptr) return res;
        }
    }
    return nullptr;
}
} // namespace
namespace spacer {
lemma_merge_generalizer::lemma_merge_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m),
      m_cvx_cls(m, ctx.use_sage()), m_dim_frsh_cnsts(m) {}

void lemma_merge_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);

    if (core(lemma)) {
        lemma_bool_inductive_generalizer ind_gen(m_ctx, 0, false, false);
        ind_gen(lemma);
        TRACE("merge_dbg", tout << "Lemma cube after inductive generalization: "
                                << lemma->get_cube() << "\n";);
    }
}

bool lemma_merge_generalizer::core(lemma_ref &lemma) {
    lemma_cluster *lc = (&*lemma->get_pob())->pt().get_cluster(lemma);
    if (lc == nullptr || lc->get_size() < 2) { return false; }

    substitution subs_newLemma(m), subs_oldLemma(m);
    expr_ref cube(m), normalizedCube(m), out(m);
    expr_ref_vector non_boolean_literals(m), non_bool_lit_pattern(m);
    expr_ref_vector conjuncts(m);
    expr_ref_vector non_var_or_bool_Literals(m);

    const expr_ref &pattern(lc->get_pattern());
    cube = mk_and(lemma->get_cube());
    normalize_order(cube, normalizedCube);
    TRACE("merge_dbg",
          tout << "Start merging with lemma cube: " << normalizedCube
               << "\n Discovered pattern: " << pattern << "\n";);

    if (has_nonlinear_var_mul(pattern, m)) {
        TRACE("merge_dbg",
              tout << "Found non linear pattern. Marked to split \n";);
        lemma->get_pob()->set_pattern(pattern.get());
        lemma->get_pob()->set_split();
        return true;
    }

    expr_ref_vector norm_pat_vec(m);
    norm_pat_vec.push_back(pattern);
    flatten_and(norm_pat_vec);

    // Seperating boolean literals and non-boolean ones
    for (expr *c : norm_pat_vec) {
        if (m.is_not(c) && is_uninterp_const(to_app(c)->get_arg(0))) {
            non_var_or_bool_Literals.push_back(c);
        } else if (!is_uninterp_const(c) && get_num_vars(c) > 0) {
            non_bool_lit_pattern.push_back(c);
        } else
            non_var_or_bool_Literals.push_back(c);
    }
    TRACE("merge_dbg",
          tout << "partitioned " << pattern << "into:\n"
               << "bools and non vars: " << non_var_or_bool_Literals << "\n"
               << "non-bools: " << non_bool_lit_pattern << "\n";);

    if (non_bool_lit_pattern.empty()) { return false; }
    non_boolean_literals.reset();
    expr_ref_vector normalizedCube_vec(m);
    flatten_and(normalizedCube, normalizedCube_vec);
    for (auto c : normalizedCube_vec) {
        if (!non_var_or_bool_Literals.contains(c))
            non_boolean_literals.push_back(c);
    }
    normalizedCube = mk_and(non_boolean_literals);
    TRACE("merge_dbg",
          tout << "non_boolean_literals_cube: " << normalizedCube << "\n";);

    unsigned n_vars = get_num_vars(mk_and(non_bool_lit_pattern));
    SASSERT(n_vars > 0);
    // start convex closure computation
    m_cvx_cls.reset(n_vars);
    m_dim_vars.reset();
    m_dim_frsh_cnsts.reset();
    m_dim_frsh_cnsts.reserve(n_vars);
    m_dim_vars.reserve(n_vars);

    const lemma_info_vector lemmas = lc->get_lemmas();
    const substitution &t_sub(lemmas[0].get_sub());

    // add dimension variable
    for (unsigned j = 0; j < n_vars; j++) {
        // long way to get variable
        expr_offset r;
        std::pair<unsigned, unsigned> v;
        t_sub.get_binding(j, v, r);
        expr *var = var_find(pattern, v.first);
        SASSERT(var != nullptr);
        m_cvx_cls.set_dimension(j, var);
        m_dim_vars[j] = var;
        app_ref var_app(m);
        var_app = m.mk_fresh_const("mrg_cvx", m_arith.mk_int());
        m_dim_frsh_cnsts[j] = var_app;
    }

    // add points
    vector<rational> point;
    for (const lemma_info &lemma : lemmas) {
        const substitution &sub(lemma.get_sub());
        point.reset();
        for (unsigned j = 0; j < n_vars; j++) {
            expr_offset r;
            std::pair<unsigned, unsigned> v;
            sub.get_binding(j, v, r);
            rational coeff;
            bool is_int;
            m_arith.is_numeral(r.get_expr(), coeff, is_int);
            SASSERT(is_int);
            point.push_back(coeff);
        }
        m_cvx_cls.push_back(point);
    }
    expr_ref_vector cls(m);
    bool exact = m_cvx_cls.closure(cls);
    if (!exact) { return false; }

    cls.push_back(pattern.get());
    expr_ref cvx_pattern(m);
    rewrite_pattern(mk_and(cls), cvx_pattern);

    model_ref mdl;

    // get a model for the lemma
    // TODO: replace with pob's model
    ref<solver> sol = mk_smt_solver(m, params_ref::get_empty(), symbol::null);
    expr_ref_vector pat(m);
    pat.push_back(cvx_pattern);
    sol->assert_expr(pat);
    lbool res = sol->check_sat(0, nullptr);
    VERIFY(res == l_true);
    sol->get_model(mdl);
    SASSERT(mdl.get() != nullptr);
    TRACE("merge_dbg", tout << "calling mbp with " << cvx_pattern << "\n";);
    qe_project(m, m_dim_frsh_cnsts, cvx_pattern, *mdl.get(), true, true, true);
    TRACE("merge_dbg",
          tout << "Pattern after computing cvx cls: " << cvx_pattern << "\n";);
    if (m_dim_frsh_cnsts.size() > 0) {
        TRACE("merge_dbg", tout << "could not eliminate all vars\n";);
        return false;
    }
    pat.reset();
    pat.push_back(cvx_pattern);
    return check_inductive_and_update(lemma, pat, non_var_or_bool_Literals);
}

// rewrites all variables into their corresponding frsh constants
void lemma_merge_generalizer::rewrite_pattern(expr *pattern,
                                              expr_ref &rw_pattern) {
    expr_safe_replace s(m);
    obj_map<expr, expr *> sub;
    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        s.insert(m_dim_vars[i], to_expr(m_dim_frsh_cnsts[i].get()));
    }
    s(pattern, rw_pattern);
    TRACE("merge_dbg", tout << "Rewrote " << mk_pp(pattern, m) << " into "
                            << rw_pattern << "\n";);
}

/* core lemma update function*/
bool lemma_merge_generalizer::check_inductive_and_update(
    lemma_ref &lemma, expr_ref_vector &conj,
    expr_ref_vector &non_var_or_bool_Literals) {
    conj.append(non_var_or_bool_Literals);
    TRACE("merge_dbg", tout << "Attempt to update lemma with: " << conj << "\n"
                            << "at level " << lemma->level() << "\n";);
    pred_transformer &pt = lemma->get_pob()->pt();
    pob_ref pob = lemma->get_pob();
    unsigned uses_level = 0;
    if (pt.check_inductive(lemma->level(), conj, uses_level,
                           lemma->weakness())) {
        TRACE("merge_dbg", tout << "POB blocked using merge at level "
                                << uses_level << "\n";);
        lemma->update_cube(lemma->get_pob(), conj);
        lemma->set_level(uses_level);
        return true;
    }

    if (pob->get_merge_atmpts() > 3) {
        pob->set_merge_conj(conj);
        TRACE("merge_dbg", tout << "merge conjecture  " << mk_and(conj)
                                << " set on pob " << pob->post() << "\n";);
    }
    // keep track of failed merge attempts
    pob->bump_merge_atmpts();
    return false;
}

void lemma_merge_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.merge", m_st.watch.get_seconds());
}
} // namespace spacer
