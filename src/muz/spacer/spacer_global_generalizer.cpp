/*

  Suite of global guidance strategies.

*/
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "model/model2expr.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_util.h"
#include "smt/smt_solver.h"

namespace {
struct compute_lcm {
    ast_manager &m;
    arith_util m_arith;
    rational m_val;
    compute_lcm(ast_manager &a_m) : m(a_m), m_arith(m), m_val(1) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        rational val;
        if (m_arith.is_numeral(n, val)) {
            m_val = lcm(denominator(abs(val)), m_val);
        }
    }
};
struct cnst_in_ind_proc {
    ast_manager &m;
    array_util m_array;
    expr_ref c;
    bool found;
    expr_ref_vector cnsts;
    cnst_in_ind_proc(ast_manager &a_m, expr* cnst) : m(a_m), m_array(m), c(cnst, m), found(false), cnsts(m) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        if (m_array.is_select(n)) {
            cnsts.reset();
            spacer::get_uninterp_consts(n, cnsts);
            if(cnsts.contains(c))
                found = true;
        }
    }
};
bool cnst_in_ind(ast_manager &m, expr* c, expr* n) {
    cnst_in_ind_proc finder(m, c);
    for_each_expr(finder, n);
    return finder.found;
}
app *mk_frsh_const(ast_manager &m, unsigned idx, sort *s) {
  std::stringstream name;
  name << "gspcVar!" << idx;
  return m.mk_const(symbol(name.str().c_str()), s);
}

bool contains_bv(ast_manager &m, const substitution &sub, unsigned &sz) {
  bv_util m_bv(m);
  std::pair<unsigned, unsigned> v;
  expr_offset r;
  for (unsigned j = 0; j < sub.get_num_bindings(); j++) {
    sub.get_binding(j, v, r);
    rational offset;
    if (m_bv.is_numeral(r.get_expr(), offset, sz))
      return true;
  }
  return false;
}

bool all_same_sz(ast_manager &m, const substitution &sub, unsigned sz) {
  bv_util m_bv(m);
  std::pair<unsigned, unsigned> v;
  expr_offset r;
  for (unsigned j = 0; j < sub.get_num_bindings(); j++) {
    sub.get_binding(j, v, r);
    rational offset;
    if (!(m_bv.is_numeral(r.get_expr(), offset) &&
          m_bv.get_bv_size(r.get_expr()) == sz))
      return false;
  }
  return true;
}
} // namespace
namespace spacer {
lemma_global_generalizer::lemma_global_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m), m_array(m),
      m_bv(m), m_cvx_cls(m, ctx.use_sage()), m_dim_frsh_cnsts(m),
      m_dim_vars(m) {
  m_solver = mk_smt_solver(m, params_ref::get_empty(), symbol::null);
}

void lemma_global_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    core(lemma);
}

void lemma_global_generalizer::to_real(expr_ref &fml) {
    if (m_arith.is_numeral(fml) || m_arith.is_to_real(fml)) return;
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
    if (m_array.is_select(fml)) {
        app *fml_app = to_app(fml);
        expr_ref_vector nw_args(m);
        expr_ref ind(m);
        ind = m_arith.mk_to_real(fml_app->get_arg(1));
        nw_args.push_back(fml_app->get_arg(0));
        nw_args.push_back(m_arith.mk_to_int(ind));
        fml = m_array.mk_select(nw_args.size(), nw_args.c_ptr());
    }
}

rational lemma_global_generalizer::get_lcm(expr *e) {
    compute_lcm g(m);
    for_each_expr(g, e);
    TRACE("subsume_verb",
          tout << "lcm of " << mk_pp(e, m) << " is " << g.m_val << "\n";);
    return g.m_val;
}

void lemma_global_generalizer::to_int(expr_ref &fml) {
    TRACE("subsume_verb", tout << "to int " << mk_pp(fml, m) << "\n";);
    if (m_arith.is_to_real(fml)) {
        fml = to_app(fml)->get_arg(0);
        TRACE("subsume_dbg_verb",
              tout << "to int finished " << mk_pp(fml, m) << "\n";);
        return;
    }
    if (m_arith.is_to_int(fml)) {
        expr_ref res(m);
        fml = to_app(fml)->get_arg(0);
        to_int(fml);
        return;
    }
    // Don't normalize constants.
    if (is_uninterp_const(fml)) return;

    rational val;
    if (m_arith.is_numeral(fml, val)) {
        // If its not an integer, try constructing int from it
        fml = m_arith.mk_int(val);

        TRACE("subsume_verb",
              tout << "to int finished " << mk_pp(fml, m) << "\n";);
        return;
    }
    app *fml_app = to_app(fml);
    unsigned N = fml_app->get_num_args();
    expr_ref_vector nw_args(m);
    for (unsigned i = 0; i < N; i++) {
        expr_ref chld(fml_app->get_arg(i), m);
        to_int(chld);
        nw_args.push_back(chld);
    }
    fml = m.mk_app(fml_app->get_family_id(), fml_app->get_decl_kind(),
                   nw_args.size(), nw_args.c_ptr());

    TRACE("subsume_verb", tout << "to int finished " << mk_pp(fml, m) << "\n";);
}

void lemma_global_generalizer::normalize(expr_ref &fml) {
    expr_ref_vector fml_vec(m), rw_fml(m);
    flatten_and(fml.get(), fml_vec);
    expr *s, *t;
    for (expr *e : fml_vec) {
        if (!(m_arith.is_arith_expr(e) || m.is_eq(e))) continue;
        app *e_app = to_app(e);
        SASSERT(e_app->get_num_args() == 2);
        expr_ref lhs(e_app->get_arg(0), m);
        expr_ref rhs(e_app->get_arg(1), m);
        // handle mod
        if (m_arith.is_mod(lhs, s, t)) {
            rational val;
            bool is_int = false;
            // if e is mod, it should already be in linear integer arithmetic
            if (!(m_arith.is_numeral(t, val, is_int) && is_int &&
                  get_lcm(s) == rational::one()))
                NOT_IMPLEMENTED_YET();
            // mod cannot be equal to a non-integer
            SASSERT(m_arith.is_numeral(rhs, val, is_int) && is_int);
            // since e is already in linear integer arithmetic, it is already
            // normalized
            rw_fml.push_back(e);
            continue;
        }

        // make sure that no child is a mod expression
        SASSERT(!contains_mod(lhs));
        SASSERT(!contains_mod(rhs));
        rational lcm = get_lcm(e);
        SASSERT(lcm != rational::zero());
        if (lcm != 1) {
            mul_and_simp(lhs, lcm);
            mul_and_simp(rhs, lcm);
            TRACE("subsume_verb", tout << "mul and simp reduced lhs to "
                                       << mk_pp(lhs, m) << " and rhs to "
                                       << mk_pp(rhs, m) << "\n";);
        }
        to_int(lhs);
        to_int(rhs);
        app *norm_e =
            m.mk_app(e_app->get_family_id(), e_app->get_decl_kind(), lhs, rhs);
        rw_fml.push_back(to_expr(norm_e));
    }
    fml = mk_and(rw_fml);
}
void lemma_global_generalizer::to_real(const expr_ref_vector &fml,
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

void lemma_global_generalizer::add_dim_vars(const lemma_cluster &lc) {
    const expr_ref &pattern = lc.get_pattern();
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
        // always compute convex closure over integers.
        var = m.mk_var(v.first, m.get_sort(r.get_expr()));
        m_cvx_cls.set_dimension(j, var);
        m_dim_vars[j] = var;
        app_ref var_app(m);
        var_app = m.mk_fresh_const("mrg_cvx", m.get_sort(r.get_expr()));
        // TODO: do we need two variables for a <= x <= b ?
        m_dim_frsh_cnsts[j] = var_app;
    }
}

void lemma_global_generalizer::add_int_points(const lemma_cluster &lc) {
    vector<rational> point;
    unsigned n_vars = get_num_vars(lc.get_pattern());
    const lemma_info_vector &lemmas(lc.get_lemmas());
    expr_offset r;
    std::pair<unsigned, unsigned> v;
    // compute lcm
    rational m_lcm = rational::one();
    for (const lemma_info &lemma : lemmas) {
        const substitution &sub(lemma.get_sub());
        point.reset();
        for (unsigned j = 0; j < n_vars; j++) {
            sub.get_binding(j, v, r);
            rational offset;
            if (!m_arith.is_numeral(r.get_expr(), offset)) {
              m_bv.is_numeral(r.get_expr(), offset);
            }
            m_lcm = lcm(m_lcm, denominator(abs(offset)));
        }
    }
    m_cvx_cls.set_lcm(m_lcm);
    // compute m_lcm and multiply m_data to make everything in integer.
    for (const lemma_info &lemma : lemmas) {
        const substitution &sub(lemma.get_sub());
        point.reset();
        for (unsigned j = 0; j < n_vars; j++) {
            sub.get_binding(j, v, r);
            rational offset;
            if (!m_arith.is_numeral(r.get_expr(), offset)) {
              m_bv.is_numeral(r.get_expr(), offset);
            }
            point.push_back(m_lcm * offset);
        }
        m_cvx_cls.push_back(point);
    }
}
void lemma_global_generalizer::reset(unsigned n_vars) {
    // start convex closure computation
    m_cvx_cls.reset(n_vars);
    m_dim_vars.reset();
    m_dim_frsh_cnsts.reset();
    m_dim_frsh_cnsts.reserve(n_vars);
    m_dim_vars.reserve(n_vars);
    m_syn_cvx_cls = true;
}
bool lemma_global_generalizer::skolemize_sel_vars(expr_ref& f, app_ref_vector& vars) {
    unsigned idx = vars.size();
    TRACE("subsume", tout << "Trying to skolemize " << f << "\n";);
    //if there are constants in m_dim_fresh_cnsts that don't appear as indices in sel, return false
    for(auto c : m_dim_frsh_cnsts) {
        if (!cnst_in_ind(m, c, f)) {
            TRACE("global", tout << "not in index " << f << " " << mk_pp(c, m) << "\n";);
            return false;
        }
    }
    expr_ref sk(m), c(m);
    app_ref v(m);
    expr_safe_replace sub(m);
    for(unsigned i = 0; i < m_dim_frsh_cnsts.size(); i++) {
        c = m_dim_frsh_cnsts.get(i);
        //Make fresh constants for instantiation
        //TODO: Is it better to use one of the actual values?
        v = mk_frsh_const(m, i + idx, m.get_sort(c));
        vars.push_back(v);
        //Make skolem constants for ground pob
        sk = mk_zk_const(m, i + idx, m.get_sort(c));
        sub.insert(c, sk);
    }
    sub(f.get(), f);
    TRACE("subsume", tout << "skolemized into " << f << "\n";);
    m_dim_frsh_cnsts.reset();
    return true;
}
bool lemma_global_generalizer::subsume(lemma_cluster lc, lemma_ref &lemma,
                                       expr_ref_vector &subs_gen, app_ref_vector& vars) {
    const expr_ref &pattern = lc.get_pattern();
    unsigned n_vars = get_num_vars(pattern);
    SASSERT(n_vars > 0);
    reset(n_vars);

    unsigned sz = 0;
    if (contains_bv(m, lc.get_lemmas()[0].get_sub(), sz)) {
      if (!all_same_sz(m, lc.get_lemmas()[0].get_sub(), sz)) {
        TRACE("global",
              tout << "cannot compute cvx cls of different size variables\n";);
        return false;
      }
      m_cvx_cls.set_bv(sz);
    }
    // create and add dim vars
    add_dim_vars(lc);
    // add points
    add_int_points(lc);
    expr_ref_vector cls(m);
    m_syn_cvx_cls = m_cvx_cls.closure(cls);
    CTRACE("subsume_verb", !m_syn_cvx_cls,
           tout << "Convex closure introduced new variables. Closure is"
                << mk_and(cls) << "\n";);

    if (!m_syn_cvx_cls) {
        // For now, no syntactic convex closure for bv
        return false;
        m_st.m_num_syn_cls++;
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

    if (!m_syn_cvx_cls) {
        expr_ref_vector temp(m);
        flatten_and(cvx_pattern, temp);
        cvx_pattern.reset();
        to_real(temp, cvx_pattern);
        TRACE("subsume_verb",
              tout << "To real produced " << cvx_pattern << "\n";);
        rewrite_frsh_cnsts();
        TRACE("subsume_verb", tout << "Rewrote " << mk_pp(mk_and(temp), m)
                                   << " into " << cvx_pattern << "\n";);
    }

    model_ref mdl;

    // get a model for the lemma
    expr_ref_vector pat(m);
    pat.push_back(cvx_pattern);

    // call solver to get model for mbp
    m_solver->push();
    m_solver->assert_expr(pat);
    m_solver->push();
    expr_ref_vector neg(m);
    for (auto l : lc.get_lemmas()) {
      neg.push_back((l.get_lemma()->get_expr()));
    }
    expr_ref neg_expr(m.mk_and(neg), m);
    m_solver->assert_expr(neg_expr);
    lbool res = m_solver->check_sat(0, nullptr);
    if (res == l_true) {
      m_solver->get_model(mdl);
      m_solver->pop(1);
    } else {
      m_solver->pop(1);
      res = m_solver->check_sat(0, nullptr);
      m_solver->get_model(mdl);
    }
    VERIFY(res == l_true);

    SASSERT(mdl.get() != nullptr);
    TRACE("subsume", expr_ref t(m); model2expr(mdl, t);
          tout << "calling mbp with " << cvx_pattern << " and " << t << "\n";);
    qe_project(m, m_dim_frsh_cnsts, cvx_pattern, *mdl.get(), true, true, !m_ctx.use_ground_pob());
    TRACE("subsume_verb", tout << "Pattern after mbp of computing cvx cls: "
                               << cvx_pattern << "\n";);

    if (!m_syn_cvx_cls) { normalize(cvx_pattern); }
    if (m_dim_frsh_cnsts.size() > 0 && !m_ctx.use_ground_pob()) {
        //Try to skolemize
        bool skmized = skolemize_sel_vars(cvx_pattern, vars);
        if(!skmized) {
            m_st.m_num_mbp_failed++;
            m_solver->pop(1);
            TRACE("subsume", tout << "could not eliminate all vars\n";);
            return false;
        }
        //TODO: fix. Should not assume that the skolem mpb overapproximates cvx_cls
        flatten_and(cvx_pattern, subs_gen);
        return true;
    }
    // check whether mbp over approximates cnx_cls
    // If not, remove literals from mbp till mbp overapproximates cnx_cls
    expr_ref_vector neg_mbp(m);
    // subs_gen stores the generalization
    flatten_and(cvx_pattern, subs_gen);
    for (expr *e : subs_gen) { neg_mbp.push_back(mk_not(m, e)); }

    expr_ref asmpt(m);
    expr_ref_vector pat_nw(m), n_mbp_nw(m);

    while (neg_mbp.size() > 0) {
        asmpt = mk_or(neg_mbp);
        TRACE("subsume_verb", tout << "checking neg mbp: " << asmpt << "\n";);

        m_solver->push();
        m_solver->assert_expr(asmpt);
        res = m_solver->check_sat(0, nullptr);
        if (res == l_false) {
            // one for getting model and one for checking cvx_cls ==> mbp
            m_solver->pop(2);
            return true;
        }

        // remove satisfied literals
        model_ref rslt;
        m_solver->get_model(rslt);

        for (unsigned i = 0; i < neg_mbp.size(); i++) {
            if (!rslt->is_true(neg_mbp.get(i))) {
                n_mbp_nw.push_back(neg_mbp.get(i));
                pat_nw.push_back(subs_gen.get(i));
            }
        }
        neg_mbp.reset();
        for (auto a : n_mbp_nw) neg_mbp.push_back(a);
        subs_gen.reset();
        for (auto a : pat_nw) subs_gen.push_back(a);
        n_mbp_nw.reset();
        pat_nw.reset();

        // reset solver
        m_solver->pop(1);
    }
    // could not find an over approximation
    TRACE("global", tout << "mbp could not overapproximate cnx_cls\n";);
    m_solver->pop(1);
    m_st.m_num_no_ovr_approx++;
    return false;
}
bool lemma_global_generalizer::core(lemma_ref &lemma) {
    lemma_cluster *pt_cls = (&*lemma->get_pob())->pt().clstr_match(lemma);
    if (pt_cls == nullptr) return false;

    // the lemma has not been added to the cluster yet since the lemma has not
    // been added to spacer yet. So we create a new, local, cluster and add the
    // lemma to it.
    lemma_cluster lc(*pt_cls);

    lc.add_lemma(lemma, true);

    const expr_ref &pattern = lc.get_pattern();

    TRACE(
        "global",
        tout << "Start global generalization of lemma : " << lemma->get_cube()
             << "\n Discovered cluster: " << pattern << "\n and lemmas ";
        for (const lemma_info &lemma
             : lc.get_lemmas()) {
            tout << "\n \t" << lemma.get_lemma()->get_cube();
        });
    if (has_nonlinear_var_mul(pattern, m)) {
        m_st.m_num_non_lin++;
        if (pt_cls->get_gas() == 0) {
            m_st.m_num_cls_ofg++;
            return false;
        }
        TRACE("global",
              tout << "Found non linear pattern. Marked to concretize \n";);
        lemma->get_pob()->set_concr_pat(pattern);
        lemma->get_pob()->set_concretize();
        lemma->get_pob()->set_gas(lc.get_pob_gas());
        pt_cls->dec_gas();
        return false;
    }

    expr_ref lit(m);
    if (should_conjecture(pattern, lit)) {
        // Create a conjecture by dropping literal from pob.
        pob_ref n = lemma->get_pob();
        TRACE("global", tout << "Conjecture with pattern " << mk_pp(pattern, m)
                             << " with gas " << pt_cls->get_gas() << "\n";);

        expr_ref_vector conj(m);
        expr_ref n_pob = expr_ref(n->post(), m);
        expr_ref_vector fml_vec(m);
        fml_vec.push_back(n_pob);
        flatten_and(fml_vec);
        bool is_smaller = drop_lit(fml_vec, lit, conj);

        if (pt_cls->get_gas() == 0) m_st.m_num_cls_ofg++;

        if (conj.size() == 0 || pt_cls->get_gas() == 0) {
            // If the pob cannot be abstracted, stop using generalization on
            // it
            TRACE("global", tout << "stop local generalization on pob " << n_pob
                                 << " id is " << n_pob->get_id() << "\n";);

            n->stop_local_gen();
        } else if (!is_smaller) {
            // The literal to be abstracted is not in the pob
            TRACE("global", tout << "cannot conjecture on " << n_pob
                                 << " with lit " << lit << "\n";);
            // TODO: Should we stop local generalization at this point ?
            m_st.m_num_cant_abs++;
        } else {
            // There is enough gas to conjecture on pob
            n->set_conj_pattern(conj);
            n->set_expand_bnd();
            n->set_may_pob_lvl(pt_cls->get_min_lvl() + 1);
            n->set_gas(pt_cls->get_pob_gas());
            pt_cls->dec_gas();
            TRACE("global", tout << "set conjecture " << conj << " at level "
                                 << n->get_may_pob_lvl() << "\n";);
        }
    }

    // if subsumption removed all the other lemmas, there is nothing to
    // generalize
    if (lc.get_size() < 2) return false;
    // in all other cases subsume
    expr_ref_vector subsume_gen(m);
    app_ref_vector vars(lemma->get_bindings());
    if (subsume(lc, lemma, subsume_gen, vars)) {
        pob_ref pob = lemma->get_pob();
        pob->set_subsume_pob(subsume_gen);
        pob->set_subsume_bindings(vars);
        pob->set_may_pob_lvl(pt_cls->get_min_lvl() + 1);
        pob->stop_local_gen();
        pob->set_gas(pt_cls->get_pob_gas() + 1);
        TRACE("global", tout << "subsume pob " << mk_and(subsume_gen)
                             << " at level " << pt_cls->get_min_lvl() + 1
                             << " set on pob " << mk_pp(pob->post(), m)
                             << "\n";);
        pt_cls->dec_gas();
        if (pt_cls->get_gas() == 0) { m_st.m_num_cls_ofg++; }
        //expand bnd if there is enough gas in the cluster
        else {pob->set_expand_bnd();}
    }
    return false;
}

void lemma_global_generalizer::var_to_const(expr *pattern,
                                            expr_ref &rw_pattern) {
    expr_safe_replace s(m);
    obj_map<expr, expr *> sub;
    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        s.insert(m_dim_vars[i].get(), to_expr(m_dim_frsh_cnsts[i].get()));
    }
    s(pattern, rw_pattern);
    TRACE("subsume_verb", tout << "Rewrote all vars into u_consts "
                               << mk_pp(pattern, m) << " into " << rw_pattern
                               << "\n";);
    return;
}

void lemma_global_generalizer::rewrite_frsh_cnsts() {
    app_ref var_app(m);
    for (unsigned i = 0; i < m_dim_vars.size(); i++) {
        if (m_arith.is_real(m_dim_frsh_cnsts[i].get())) continue;
        var_app = m_arith.mk_to_real(m_dim_frsh_cnsts[i].get());
        m_dim_frsh_cnsts[i] = var_app;
    }
}

void lemma_global_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.global", m_st.watch.get_seconds());
    st.update("SPACER cluster out of gas", m_st.m_num_cls_ofg);
    st.update("SPACER num sync cvx cls", m_st.m_num_syn_cls);
    st.update("SPACER num mbp failed", m_st.m_num_mbp_failed);
    st.update("SPACER num non lin", m_st.m_num_non_lin);
    st.update("SPACER num no over approximate", m_st.m_num_no_ovr_approx);
    st.update("SPACER num cant abstract", m_st.m_num_cant_abs);
    m_cvx_cls.collect_statistics(st);
}

} // namespace spacer
