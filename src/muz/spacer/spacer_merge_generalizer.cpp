/*

  Suite of merging strategies.

*/
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_convex_closure.h"
using namespace spacer;
namespace spacer {

lemma_merge_generalizer::lemma_merge_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m) {}

/* Guards! Guards! */
bool lemma_merge_generalizer::lt_or_leq(const expr_ref &literal) {
    if (!is_app(literal)) { return false; }
    ast_manager m = literal.get_manager();
    arith_util m_arith(m);
    return (m_arith.is_le(literal) || m_arith.is_lt(literal));
}

bool lemma_merge_generalizer::gt_or_geq(const expr_ref &literal) {
    if (!is_app(literal)) { return false; }
    ast_manager m = literal.get_manager();
    arith_util m_arith(m);
    return (m_arith.is_ge(literal) || m_arith.is_gt(literal));
}

bool lemma_merge_generalizer::only_halfSpace(const expr_ref &literal) {
    return gt_or_geq(literal) || lt_or_leq(literal);
}

bool lemma_merge_generalizer::is_simple_literal(const expr_ref &literal) {
    return is_app(literal) && to_app(literal)->get_depth() <= 2;
}
/* end of Guards */


bool lemma_merge_generalizer::half_plane_prog(
    const expr_ref &literal, const expr_ref &pattern,
    const lemma_info_vector& lemmas, expr_ref_vector &conjectures) {

    expr *lhs, *rhs;
    vector<rational> data;
    rational num;
    bool is_int = false;
    //pattern is lhs =  interpreted constant
    if(!(m.is_eq(literal, lhs, rhs) && m_arith.is_numeral(rhs, num, is_int) && is_int)) return false;

    TRACE("merge_strategies", tout << "entered half_plane_prog with: "
                                   << mk_epp(pattern, m) << "\n";);
    rhs = to_app(pattern)->get_arg(1);
    SASSERT(is_var(rhs));
    var* v = to_var(rhs);
    rational neighbour_num;
    expr_offset neighbour_rhs;
    for(const lemma_info& lemma: lemmas) {
      const substitution& s(lemma.get_sub());
      s.find(v, 0, neighbour_rhs);
      if(!m_arith.is_numeral(neighbour_rhs.get_expr(), num, is_int) && is_int) {
        return false;
      }
      data.push_back(neighbour_num);
    }

    if(!data.contains(num))
      data.push_back(num);

    TRACE("merge_strategies", tout << "entered half_plane_prog with data: "; for(auto e : data) tout << mk_epp(m_arith.mk_numeral(e, true), m) << " "; tout << "\n"; );

    //search for pattern only if there are atleast 3 neighbours
    if( data.size() < 3 ) { return false; }

    //compute convex closure
    expr_ref conj(m);
    convex_closure cvx_cls(m);
    bool success = cvx_cls.compute_cls(data, lhs, conj);
    if (!success) { return false; }
    conjectures.push_back(conj);

    TRACE("merge_strategies",
          tout << "conjectures are " << mk_and(conjectures) << "\n";);
    return true;
}

/*
  AG: I think this is only sound if k1 == k2

  (>= (+ (* k_1 t_1) (* k_2 t_2)) k_3) with all k >= 0
   ------------------------------------
   (>= (+ t_1 t_2) 0)
*/
bool lemma_merge_generalizer::half_plane_03(
    const expr_ref &literal, const expr *pattern, expr_ref_vector &conjectures) {
    if (!only_halfSpace(literal)) { return false; }
    TRACE("merge_strategies", tout << "entered half_plane_03 with: "
                                   << mk_epp(literal, m) << "\n";);
    expr_ref conj(m);
    rational rhs(0);
    bool is_int = true;
    ;
    app_ref app(m);
    app = to_app(literal);
    expr_ref_vector var_coeff(m), neg_coeff_uniCs(m), pos_coeff_uniCs(m);
    get_uninterp_consts_with_var_coeff(to_app(pattern), var_coeff);

    if (var_coeff.empty()) { return false; }

    get_uninterp_consts_with_pos_coeff(app, pos_coeff_uniCs);
    get_uninterp_consts_with_neg_coeff(app, neg_coeff_uniCs);

    expr_ref sum(m), neg_sum(m), pos_sum(m);
    sum = m_arith.mk_add(var_coeff.size(), var_coeff.c_ptr());

    TRACE("merge_strategies",
          tout << "literal: " << mk_epp(literal, m) << "\n"
               << "app->get_arg(1): " << mk_epp(app->get_arg(1), m) << "\n"
               << "sum: " << mk_epp(sum, m) << "\n";);

    if (gt_or_geq(literal)) {
        if (!m_arith.is_numeral(app->get_arg(1), rhs, is_int)) { return false; }
        if (!(rhs > rational(0))) { return false; }
    } else if (lt_or_leq(literal)) {
        if (!m_arith.is_numeral(app->get_arg(1), rhs, is_int)) { return false; }
        if (!(rhs < rational(0))) { return false; }
    }

    if (!neg_coeff_uniCs.empty()) {
        // JEF: neg_coeff hence top level not
        neg_sum =
            m_arith.mk_add(neg_coeff_uniCs.size(), neg_coeff_uniCs.c_ptr());
        conj = m.mk_not(m.mk_app(app->get_family_id(), app->get_decl_kind(),
                                 sum, m_arith.mk_numeral(rational(0), is_int)));
        conjectures.push_back(conj);
        TRACE("merge_strategies", tout << "Conj: " << mk_epp(conj, m) << "\n";);
    } else if (!pos_coeff_uniCs.empty()) {
        pos_sum =
            m_arith.mk_add(pos_coeff_uniCs.size(), pos_coeff_uniCs.c_ptr());
        conj = m.mk_app(app->get_family_id(), app->get_decl_kind(), sum,
                        m_arith.mk_numeral(rational(0), is_int));
        conjectures.push_back(conj);
        TRACE("merge_strategies", tout << "Conj: " << mk_epp(conj, m) << "\n";);
    }

    TRACE("merge_strategies", tout << "Ret: " << !conjectures.empty() << "\n";);
    return !conjectures.empty();
}

/*

  [Branch 1]
  (>= t_1 k_1) (<= t_2 k_2) and k_1 > k_2
  ------
  (> t_1 t_2)

  [Branch 2]
  (<= t_1 k_1) (>= t_2 k_2) and k_1 < k_2
  ------
  (< t_1 t_2)

  // AG: Branch 3.1 and Branch 3.2 are unsound
  // XXX JEF: This is aggressive imo;
  [Branch 3.1]
  (>= t_1 k_1) (>= t_2 k_2) and k_1 > k_2
  ------
  (> t_1 t_2)

  [Branch 3.2]
  (>= t_1 k_1) (>= t_2 k_2) and k_1 < k_2
  ------
  (< t_1 t_2)

  // AG: the flip side of 3.1 and 3.2 might be unsound as well
  // TODO Branch 4.1 & 4.2: flip side of 3.1 and 3.2

*/
bool lemma_merge_generalizer::half_plane_XX(
    const expr_ref &literal, const expr_ref &pattern, expr_ref_vector &conjectures) {
    expr_ref conj(m);
    if (!(m.is_and(literal) && to_app(literal)->get_num_args() == 2))
        return false;

    th_rewriter rw(m);
    expr_ref fst(m), snd(m);
    fst = to_app(literal)->get_arg(0);
    snd = to_app(literal)->get_arg(1);

    // check for numerics
    rational k1, k2;
    if (!(m_arith.is_numeral(to_app(fst)->get_arg(1), k1)) ||
        !(m_arith.is_numeral(to_app(snd)->get_arg(1), k2))) {
        return false;
    }

    expr_ref t1(m), t2(m);
    t1 = to_app(fst)->get_arg(0);
    t2 = to_app(snd)->get_arg(0);

    if (t1 == t2) return false;

    if (gt_or_geq(fst) && lt_or_leq(snd)) {
      // t1 >= k1 && t2 <= k2
      conj = m_arith.mk_le(m_arith.mk_sub(t2, t1),
                           m_arith.mk_numeral(k2 - k1, true));
      rw(conj);
      conjectures.push_back(conj);
      return true;
    } else if (lt_or_leq(fst) && gt_or_geq(snd)) {
        // t1 <= k1 && t2 >= k2
      conj = m_arith.mk_le(m_arith.mk_sub(t1, t2),
                           m_arith.mk_numeral(k1 - k2, true));
            // simplify newly constructed literal
      rw(conj);
      conjectures.push_back(conj);
      return true;
    } else if (gt_or_geq(fst) && gt_or_geq(snd)) {
      // t1 >= k1 && t2 >= k2
      conj = m_arith.mk_ge(m_arith.mk_add(t1, t2),
                           m_arith.mk_numeral(k1 + k2, true));
      rw(conj);
      conjectures.push_back(conj);
      return true;
    } else if (m.is_eq(fst)) {
      // from t1 = k1 & t2 op k2 conjecture t1 + t2 op k1 + k2
      conj = m.mk_app(to_app(snd)->get_family_id(),
                      to_app(snd)->get_decl_kind(),
                      m_arith.mk_add(t1, t2),
                      m_arith.mk_numeral(k1 + k2, true));
      conjectures.push_back(conj);
      return true;
    } else if (m.is_eq(snd)) {
      // from t2 = k2 & t1 op k1 conjecture t1 + t2 op k1 + k2
      conj = m.mk_app(to_app(fst)->get_family_id(),
                      to_app(fst)->get_decl_kind(),
                      m_arith.mk_add(t1, t2),
                      m_arith.mk_numeral(k1 + k2, true));
      conjectures.push_back(conj);
      return true;
    }
    // none of the conjectures fits, give up!
    return false;
}

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
    lemma_cluster* lc = (&*lemma->get_pob())->pt().get_cluster(lemma);
    if(lc == nullptr || lc->get_size() < 2) {
      return false;
    }
    substitution subs_newLemma(m), subs_oldLemma(m);
    expr_ref cube(m), normalizedCube(m), out(m);
    expr_ref_vector non_boolean_literals(m), non_bool_lit_pattern(m);
    expr_ref_vector conjuncts(m);
    expr_ref_vector non_var_or_bool_Literals(m);

    const expr_ref& pattern(lc->get_pattern());
    cube = mk_and(lemma->get_cube());
    normalize_order(cube, normalizedCube);
    TRACE("merge_dbg",
          tout << "Start merging with lemma cube: " << normalizedCube
               << "\n Discovered pattern: " << pattern <<"\n";);

    if(has_nonlinear_var_mul(pattern, m)) {
        TRACE("merge_dbg", tout << "Found non linear pattern. Marked to split \n";);
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
    TRACE("merge_dbg", tout << "partitioned " << pattern
                            << "into:\n"
                            << "bools and non vars: " << non_var_or_bool_Literals << "\n"
                            << "non-bools: " << non_bool_lit_pattern<< "\n";);

    if (non_bool_lit_pattern.empty()) { return false ;}
    non_boolean_literals.reset();
    expr_ref_vector normalizedCube_vec(m);
    flatten_and(normalizedCube, normalizedCube_vec);
    for (auto c : normalizedCube_vec) {
      if(!non_var_or_bool_Literals.contains(c))
        non_boolean_literals.push_back(c);
    }
    normalizedCube = mk_and(non_boolean_literals);
    TRACE("merge_dbg",
          tout << "non_boolean_literals_cube: " << normalizedCube << "\n";);

    if (half_plane_prog(normalizedCube, mk_and(non_bool_lit_pattern), lc->get_lemmas(), conjuncts)) {
      TRACE("merge_strategies",
            tout << "Applied half_plane_prog on: " << normalizedCube << "\n";);
      m_st.half_plane_prog++;
      if (check_inductive_and_update(lemma, conjuncts, non_var_or_bool_Literals)) {
        m_st.half_plane_prog_success++;
        IF_VERBOSE(1, verbose_stream() << "Merge Half Plane Prog success ");
        return true;
      }
    }


    if (half_plane_03(normalizedCube, mk_and(non_bool_lit_pattern), conjuncts)) {
        TRACE("merge_strategies",
              tout << "Applied half_plane_03 on: " << normalizedCube << "\n";);
        m_st.half_plane03++;
        if (check_inductive_and_update(lemma, conjuncts, non_var_or_bool_Literals)) {
            m_st.half_plane03_success++;
            IF_VERBOSE(1, verbose_stream() << "M03Y ");
            return true;
        }
    }

    if (half_plane_XX(normalizedCube, mk_and(non_bool_lit_pattern), conjuncts)) {
        TRACE("merge_strategies",
              tout << "Applied half_plane_XX on: " << normalizedCube << "\n";);
        m_st.half_planeXX++;
        if (conjuncts.size() > 1) {
            TRACE("multi_merge", tout << "multi-merge conjectures: \n";
                  for (auto &conj
                       : conjuncts) { tout << mk_epp(conj, m) << "\n"; } tout
                  << "\n";);
            if (check_inductive_and_update_multiple(lemma, conjuncts,
                                                    non_var_or_bool_Literals)) {
                TRACE("multi_merge",
                      tout << "multi-merge found inductive: "
                           << mk_epp(mk_and(lemma->get_cube()), m) << "\n";);
                m_st.half_planeXX_success++;
                IF_VERBOSE(1, verbose_stream() << "MXX ");
                return true;
            }
        }
        else if (check_inductive_and_update(lemma, conjuncts, non_var_or_bool_Literals)) {
            m_st.half_planeXX_success++;
            IF_VERBOSE(1, verbose_stream() << "MXX ");
            return true;
        }
    }

    if (lc->get_size() >= 10) {
        TRACE("cluster_stats",
              tout << "Found big cluster and Tried all merge strategies\n";);
        return false;
    }

    TRACE("merge_dbg", tout << "tried all merge strategies\n";);
    return false;
}

/* core lemma update function*/
bool lemma_merge_generalizer::check_inductive_and_update(
    lemma_ref &lemma, expr_ref_vector& conj, expr_ref_vector& non_var_or_bool_Literals) {
    conj.append(non_var_or_bool_Literals);
    TRACE("merge_dbg", tout << "Attempt to update lemma with: " << conj << "\n"
                            << "at level " << lemma->level() << "\n";);
    pred_transformer &pt = lemma->get_pob()->pt();
    pob_ref pob = lemma->get_pob();
    unsigned uses_level = 0;
    if (pt.check_inductive(lemma->level(), conj, uses_level,
                           lemma->weakness())) {
      TRACE("merge_dbg", tout << "POB blocked using merge at level " << uses_level
            << "\n";);
      lemma->update_cube(lemma->get_pob(), conj);
      lemma->set_level(uses_level);
      return true;
    }

    if(pob->get_merge_atmpts() > 3) {
      pob->set_merge_conj(conj);
      TRACE("merge_dbg", tout << "merge conjecture  " << mk_and(conj) << " set on pob " << pob->post() << "\n";);
    }
    //keep track of failed merge attempts
    pob->bump_merge_atmpts();
    return false;
}

bool lemma_merge_generalizer::check_inductive_and_update_multiple(
    lemma_ref &lemma, expr_ref_vector& conjs, expr_ref_vector& non_var_or_bool_Literals) {
    expr_ref_vector conj_and(m);
    for (auto* conj : conjs) {
      //HG : need to decide which conjecture to use if more than one is
      //inductive. Right now, this is being done arbitrarly
      conj_and.reset();
      flatten_and(conj, conj_and);
      if(check_inductive_and_update(lemma, conj_and, non_var_or_bool_Literals))
        return true;
    }
    return false;
}

void lemma_merge_generalizer::collect_statistics(statistics &st) const {
      st.update("SPACER merge gen half plane 03", m_st.half_plane03);
    st.update("SPACER merge gen half plane 03 success",
              m_st.half_plane03_success);
    st.update("SPACER merge gen half plane XX", m_st.half_planeXX);
    st.update("SPACER merge gen half plane XX success",
              m_st.half_planeXX_success);
    st.update("time.spacer.solve.reach.gen.merge", m_st.watch.get_seconds());
    st.update("SPACER merge half plane prog",m_st.half_plane_prog);
    st.update("SPACER merge half plane prog success",m_st.half_plane_prog_success);
}
} // namespace spacer
