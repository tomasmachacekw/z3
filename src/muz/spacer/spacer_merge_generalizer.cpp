/*

  Suite of merging strategies.

*/
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_util.h"

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

/* Conjecture Rules
   each rule returns if the conjecture can be made; together with the
   conjecture(s) these rules are implemented for simple literals
   XXX SASSERT(uninterp consts prefix normal form)!
*/

/* (<= t k)  for k < 0
   ------
   (<= t 0)
*/
// XXX zero trick is needed to avoid ambiguious `mk_numeral`
bool lemma_merge_generalizer::half_plane_01(
    const expr_ref &literal, const expr_ref &pattern,
    const expr_ref_vector &neighbour_lemmas, expr_ref_vector &conjectures) {
    if (!(lt_or_leq(literal) && is_simple_literal(literal))) return false;

    TRACE("merge_strategies", tout << "entered half_plane_01 with: "
                                   << mk_epp(literal, m) << "\n";);
    expr_ref conj(m);
    rational rhs, zero(0);
    bool isInt;
    if (m_arith.is_numeral(to_app(literal)->get_arg(1), rhs, isInt)) {
        TRACE("merge_strategies",
              tout << "rhs, isInt?: " << rhs << " / " << isInt << "\n";
              tout << "numeral: " << mk_epp(m_arith.mk_numeral(zero, isInt), m)
                   << "\n";);
        if (rhs < zero) {
            conj = m.mk_app(to_app(literal)->get_family_id(),
                            to_app(literal)->get_decl_kind(),
                            to_app(literal)->get_arg(0),
                            m_arith.mk_numeral(zero, isInt));
            TRACE("merge_strategies",
                  tout << "Conj: " << mk_epp(conj, m) << "\n";);
            conjectures.push_back(conj);
            return true;
        } else if (rhs >= zero) {
            // XXX not applicable since the literal is t <= k with k > 0,
            // XXX can only make k greater, but don't know by how much
            return false;
        }
    }
    return false;
}

/* (>= t k)  for k > 0
   ------
   (>= t 0)
*/
bool lemma_merge_generalizer::half_plane_02(
    const expr_ref &literal, const expr_ref &pattern,
    const expr_ref_vector &neighbour_lemmas, expr_ref_vector &conjectures) {
    if (!(gt_or_geq(literal) && is_simple_literal(literal))) return false;

    TRACE("merge_strategies", tout << "entered half_plane_02 with: "
                                   << mk_epp(literal, m) << "\n";);
    expr_ref conj(m);
    rational rhs, zero(0);
    bool isInt;
    if (m_arith.is_numeral(to_app(literal)->get_arg(1), rhs, isInt)) {
        if (rhs > zero) {
            conj = m.mk_app(to_app(literal)->get_family_id(),
                            to_app(literal)->get_decl_kind(),
                            to_app(literal)->get_arg(0),
                            m_arith.mk_numeral(zero, isInt));
            TRACE("merge_strategies", tout << "half_plane_02 rhs > zero: "
                                           << mk_epp(conj, m) << "\n";);
            conjectures.push_back(conj);
            return true;
        } else if (rhs <= zero) {
            // XXX not applicable since the literal is t >= k with k <= 0,
            // XXX can only make k smaller, but don't know by how much
            return false;
        }
    }
    return false;
}

/*
  AG: I think this is only sound if k1 == k2

  (>= (+ (* k_1 t_1) (* k_2 t_2)) k_3) with all k >= 0
   ------------------------------------
   (>= (+ t_1 t_2) 0)
*/
bool lemma_merge_generalizer::half_plane_03(
    const expr_ref &literal, const expr *pattern,
    const expr_ref_vector &neighbour_lemmas, expr_ref_vector &conjectures) {
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
    const expr_ref &literal, const expr_ref &pattern,
    const expr_ref_vector &neighbour_lemmas, expr_ref_vector &conjectures) {
    expr_ref conj(m);
    if (!(m.is_and(literal) && to_app(literal)->get_num_args() == 2))
        return false;

    th_rewriter rw(m);
    expr_ref fst(m), snd(m);
    fst = to_app(literal)->get_arg(0);
    snd = to_app(literal)->get_arg(1);

    // check for right operators
    if (!(only_halfSpace(fst)) || !(only_halfSpace(snd))) {
        return false;
    }

    // check for numerics
    rational k1, k2;
    if (!(m_arith.is_numeral(to_app(fst)->get_arg(1), k1)) ||
        !(m_arith.is_numeral(to_app(snd)->get_arg(1), k2))) {
        return false;
    }

    expr_ref t1(m), t2(m);
    t1 = to_app(fst)->get_arg(0);
    t2 = to_app(snd)->get_arg(0);

    if (gt_or_geq(fst) && lt_or_leq(snd)) {
        // t1 >= k1 && t2 <= k2
        if (k1 > k2) {
            // [Branch 1]
            conj = m_arith.mk_gt(t1, t2);
            conjectures.push_back(conj);
            return true;
        } else {
            STRACE("merge_dbg", tout << "got here with k2 >= k1\n";);
            conj = m_arith.mk_ge(t2, t1);
            conjectures.push_back(conj);
            conj = m_arith.mk_gt(t2, t1);
            conjectures.push_back(conj);
            // dont forget we're in cube space!
            // so (2 * a < b) => (>= (* 2 a) b)
            conj = m_arith.mk_ge(m_arith.mk_mul(m_arith.mk_int(2), t1), t2);
            conjectures.push_back(conj);
            return true;
        }
    } else if (lt_or_leq(fst) && gt_or_geq(snd)) {
        // t1 <= k1 && t2 >= k2
        if (k1 < k2) {
            // [Branch 2]
            conj = m_arith.mk_le(m_arith.mk_sub(t1, t2),
                                 m_arith.mk_numeral(k1 - k2, true));
            // simplify newly constructed literal
            rw(conj);
            conjectures.push_back(conj);
            conj = m_arith.mk_lt(t1, t2);
            conjectures.push_back(conj);
            return true;
        }
    } else if (gt_or_geq(fst) && gt_or_geq(snd)) {
       if (k1 + k2 > 0) {
            conj = m_arith.mk_gt(m_arith.mk_add(t1, t2),
                                 m_arith.mk_numeral(rational(0), true));
            rw(conj);
            conjectures.push_back(conj);
        }

       // t1 >= k1 && t2 >= k2
       conj = m_arith.mk_ge(m_arith.mk_add(t1, t2),
                            m_arith.mk_numeral(k1 + k2, true));
       rw(conj);
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
    expr_ref_vector neighbours = lemma->get_neighbours();
    if (neighbours.size() < 2 /* 7 */) { return false; }
    substitution subs_newLemma(m), subs_oldLemma(m);
    expr_ref cube(m), normalizedCube(m), out(m);
    expr_ref_vector non_boolean_literals(m);
    expr_ref_vector conjuncts(m);

    cube = mk_and(lemma->get_cube());
    normalize_order(cube, normalizedCube);
    TRACE("merge_dbg",
          tout << "Start merging with lemma cube: " << normalizedCube
               << "\n"
                  "Discovered pattern: "
               << mk_pp(neighbours.get(0), m)
               << "\n"
                  "First neighbour: "
               << mk_pp(neighbours.get(1), m) << "\n";);

    expr_ref pat(m);
    pat = neighbours.get(0);

    // Seperating boolean literals and non-boolean ones
    expr_ref_vector bool_Literals(m);

    if (m.is_and(neighbours.get(0))) {
        for (expr *c : *to_app(neighbours.get(0))) {
            if (m.is_not(c) && is_uninterp_const(to_app(c)->get_arg(0))) {
                bool_Literals.push_back(c);
            } else if (!is_uninterp_const(c)) {
                non_boolean_literals.push_back(c);
            } else
                bool_Literals.push_back(c);
        }
    }
    TRACE("merge_dbg", tout << "partitioned " << mk_pp(neighbours.get(0), m)
                            << "into:\n"
                            << "bools: " << bool_Literals << "\n"
                            << "non-bools: " << non_boolean_literals << "\n";);

    if (!non_boolean_literals.empty()) {
        non_boolean_literals.reset();
        for (auto c : lemma->get_cube()) {
            if (m.is_not(c) && is_uninterp_const(to_app(c)->get_arg(0))) {
                continue;
            }
            if (!is_uninterp_const(c)) non_boolean_literals.push_back(c);
        }
        cube = mk_and(non_boolean_literals);
        normalize_order(cube, normalizedCube);
        TRACE("fun",
              tout << "non_boolean_literals_cube: " << normalizedCube << "\n";);
    }

    if (false &&
        half_plane_01(normalizedCube, normalizedCube, neighbours, conjuncts)) {
        TRACE("merge_strategies",
              tout << "Applied half_plane_01 on: " << normalizedCube << "\n";);
        m_st.half_plane01++;
        if (check_inductive_and_update(lemma, conjuncts, bool_Literals)) {
            m_st.half_plane01_success++;
            IF_VERBOSE(1, verbose_stream() << "M01Y ");
            return true;
        }
    }

    if (false &&
        half_plane_02(normalizedCube, normalizedCube, neighbours, conjuncts)) {
        TRACE("merge_strategies",
              tout << "Applied half_plane_02 on: " << normalizedCube << "\n";);
        m_st.half_plane02++;
        if (check_inductive_and_update(lemma, conjuncts, bool_Literals)) {
            m_st.half_plane02_success++;
            IF_VERBOSE(1, verbose_stream() << "M02Y ");
            return true;
        }
    }

    if (half_plane_03(normalizedCube, neighbours.get(0), neighbours,
                      conjuncts)) {
        TRACE("merge_strategies",
              tout << "Applied half_plane_03 on: " << normalizedCube << "\n";);
        m_st.half_plane03++;
        if (check_inductive_and_update(lemma, conjuncts, bool_Literals)) {
            m_st.half_plane03_success++;
            IF_VERBOSE(1, verbose_stream() << "M03Y ");
            return true;
        }
    }

    if (half_plane_XX(normalizedCube, normalizedCube, neighbours, conjuncts)) {
        TRACE("merge_strategies",
              tout << "Applied half_plane_XX on: " << normalizedCube << "\n";);
        m_st.half_planeXX++;
        if (conjuncts.size() > 1) {
            TRACE("multi_merge", tout << "multi-merge conjectures: \n";
                  for (auto &conj
                       : conjuncts) { tout << mk_epp(conj, m) << "\n"; } tout
                  << "\n";);
            if (check_inductive_and_update_multiple(lemma, conjuncts,
                                                    bool_Literals)) {
                TRACE("multi_merge",
                      tout << "multi-merge found inductive: "
                           << mk_epp(mk_and(lemma->get_cube()), m) << "\n";);
                m_st.half_planeXX_success++;
                IF_VERBOSE(1, verbose_stream() << "MXX ");
                return true;
            }
        }
        else if (check_inductive_and_update(lemma, conjuncts, bool_Literals)) {
            m_st.half_planeXX_success++;
            IF_VERBOSE(1, verbose_stream() << "MXX ");
            return true;
        }
    }

    if (neighbours.size() >= 10) {
        TRACE("cluster_stats",
              tout << "Found big cluster and Tried all merge strategies\n";);
        return false;
        // throw unknown_exception();
    }

    TRACE("merge_dbg", tout << "tried all merge strategies\n";);
    return false;
}

/* core lemma update function*/
bool lemma_merge_generalizer::check_inductive_and_update(
    lemma_ref &lemma, expr_ref_vector conj, expr_ref_vector bool_Literals) {
    conj.append(bool_Literals);
    TRACE("merge_dbg", tout << "Attempt to update lemma with: " << conj << "\n"
                            << "at level " << lemma->level() << "\n";);
    pred_transformer &pt = lemma->get_pob()->pt();
    unsigned uses_level = 0;
    if (pt.check_inductive(lemma->level(), conj, uses_level,
                           lemma->weakness())) {
        TRACE("merge_dbg", tout << "Inductive!"
                                << "\n";);
        lemma->update_cube(lemma->get_pob(), conj);
        lemma->set_level(uses_level);
        return true;
    } else {
        TRACE("merge_dbg", tout << "Not inductive!"
                                << "\n";);
        return false;
    }
}

bool lemma_merge_generalizer::check_inductive_and_update_multiple(
   lemma_ref &lemma, expr_ref_vector conjs, expr_ref_vector bool_Literals) {
    bool found_inductive = false;
    for(auto &conj :conjs){
        expr_ref_vector c(m);
        c.append(bool_Literals);
        c.push_back(conj);
        STRACE("multi_merge",
               tout << "Attempt to update lemma with: " << c
               << "; at level " << lemma->level() ;);
        pred_transformer &pt = lemma->get_pob()->pt();
        unsigned uses_level = 0;
        if (pt.check_inductive(lemma->level(), c, uses_level,
                               lemma->weakness())) {
            STRACE("multi_merge", tout << " found Inductive!"
                   << "\n";);
            lemma->update_cube(lemma->get_pob(), c);
            lemma->set_level(uses_level);
            found_inductive = true;
        } else {
            STRACE("multi_merge", tout << " is Not inductive!\n";);
        }
    }
    return found_inductive;
}

void lemma_merge_generalizer::collect_statistics(statistics &st) const {
    st.update("SPACER merge gen half plane 01", m_st.half_plane01);
    st.update("SPACER merge gen half plane 01 success",
              m_st.half_plane01_success);
    st.update("SPACER merge gen half plane 02", m_st.half_plane02);
    st.update("SPACER merge gen half plane 02 success",
              m_st.half_plane02_success);
    st.update("SPACER merge gen half plane 03", m_st.half_plane03);
    st.update("SPACER merge gen half plane 03 success",
              m_st.half_plane03_success);
    st.update("SPACER merge gen half plane XX", m_st.half_planeXX);
    st.update("SPACER merge gen half plane XX success",
              m_st.half_planeXX_success);
    st.update("time.spacer.solve.reach.gen.merge", m_st.watch.get_seconds());
}

/*
  Summarize using concrete numerical bounds from neighbours
  1) simple half spaces (>= t1 n1)
 */
bool lemma_merge_generalizer::merge_summarize(
    const expr_ref &literal, const expr_ref pattern,
    const expr_ref_vector &neighbour_lemmas, expr_ref_vector &conjectures) {
    if (!only_halfSpace(literal)) { return false; }
    TRACE(
        "merge_dbg_summarize", tout << "---Pattern---\n"
                                    << pattern << "\n"
                                    << "---Concrete lemmas---\n";
        for (auto *n
             : neighbour_lemmas) {
            tout << "(" << n->get_id() << "):\n" << mk_epp(n, m) << "\n";
        };
        tout << "\n------\n";);

    // case 1) simple half spaces
    if (is_simple_literal(pattern)) {
        rational maxima(0), minima(0), temp(0);
        for (auto *n : neighbour_lemmas) {
            if (!m_arith.is_numeral(to_app(n)->get_arg(1), temp)) { continue; }
            if (temp >= maxima) { maxima = temp; }
            if (temp <= minima) { minima = temp; }
        }
        TRACE("merge_dbg_summarize", tout << "---Simple half spaces---\n";
              tout << "MAX/MIN: " << maxima << "/" << minima;
              tout << "\n------\n";);
    }
    return false;
}
} // namespace spacer
