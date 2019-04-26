/*

  Suite of merging strategies.

*/
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_generalizers.h"
#include "muz/spacer/spacer_manager.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"

using namespace spacer;
namespace spacer {

    lemma_merge_generalizer::lemma_merge_generalizer(context &ctx) :
        lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m) {}


    /* Guards! Guards! */
    bool lemma_merge_generalizer::lt_or_leq (const expr_ref &literal){
        if(!is_app(literal)) { return false; }
        ast_manager m = literal.get_manager();
        arith_util m_arith(m);
        return (m_arith.is_le(to_app(literal)) ||
                m_arith.is_lt(to_app(literal)));
    }

    bool lemma_merge_generalizer::gt_or_geq (const expr_ref &literal){
        if(!is_app(literal)) { return false; }
        ast_manager m = literal.get_manager();
        arith_util m_arith(m);
        return (m_arith.is_ge(to_app(literal)) ||
                m_arith.is_gt(to_app(literal)));
    }

    bool lemma_merge_generalizer::only_halfSpace (const expr_ref &literal){
        return gt_or_geq(literal) || lt_or_leq(literal);
    }

    bool lemma_merge_generalizer::is_simple_literal (const expr_ref &literal){
        if(!is_app(literal)) { return false; }
        return (to_app(literal)->get_depth() <= 2);
    }
    /* end of Guards */

    /* Conjecture Rules
       each rule returns if the conjecture can be made; together with the conjecture(s)
       these rules are implemented for simple literals
       XXX SASSERT(uninterp consts prefix normal form)!
    */

    /* (<= t k)  for k < 0
       ------
       (<= t 0)
    */
    // XXX zero trick is needed to avoid ambiguious `mk_numeral`
    bool lemma_merge_generalizer::half_plane_01 (const expr_ref &literal, const expr_ref &pattern,
                                                 const expr_ref_vector &neighbour_lemmas, expr_ref_vector &conjectures)
    {
        if(!(lt_or_leq(literal)) || !is_simple_literal(literal)) { return false; }
        STRACE("merge_strategies", tout << "entered half_plane_01 with: " << mk_epp(literal, m) << "\n";);
        expr_ref conj(m);
        rational rhs, zero(0);
        bool isInt;
        if(m_arith.is_numeral(to_app(literal)->get_arg(1), rhs, isInt)){
            STRACE("merge_strategies", tout << "rhs, isInt?: " << rhs << " / " << isInt << "\n";);
            STRACE("merge_strategies", tout << "numeral: " << mk_epp(m_arith.mk_numeral(zero, isInt), m) << "\n";);
            if(rhs < zero){
                conj = m.mk_app(to_app(literal)->get_family_id(),
                                to_app(literal)->get_decl_kind(),
                                to_app(literal)->get_arg(0),
                                m_arith.mk_numeral(zero, isInt));
                STRACE("merge_strategies", tout << "Conj: " << mk_epp(conj, m) << "\n";);
                conjectures.push_back(conj);
                return true;
            }
            if(rhs >= zero){
                conj = m_arith.mk_lt(to_app(literal)->get_arg(0), m_arith.mk_numeral(zero, isInt));
                conjectures.push_back(conj);
                return true;
            }
        }
        return false;
    }

    /* (>= t k)  for k > 0
       ------
       (>= t 0)
    */
    bool lemma_merge_generalizer::half_plane_02 (const expr_ref &literal, const expr_ref &pattern,
                                                 const expr_ref_vector &neighbour_lemmas,
                                                 expr_ref_vector &conjectures)
    {
        if(!(gt_or_geq(literal)) || !is_simple_literal(literal)) { return false; }
        STRACE("merge_strategies", tout << "entered half_plane_02 with: " << mk_epp(literal, m) << "\n";);
        expr_ref conj(m);
        rational rhs, zero(0);
        bool isInt;
        if(m_arith.is_numeral(to_app(literal)->get_arg(1), rhs, isInt)){
            if(rhs <= zero){
                conj = m.mk_app(to_app(literal)->get_family_id(),
                                to_app(literal)->get_decl_kind(),
                                to_app(literal)->get_arg(0), m_arith.mk_numeral(zero, isInt));
                conjectures.push_back(conj);
                return true;
            }
            if(rhs > zero){
                conj = m_arith.mk_lt(to_app(literal)->get_arg(0), m_arith.mk_numeral(zero, isInt));
                conjectures.push_back(conj);
                return true;
            }
        }
        return false;
    }

    /* (>= (+ (* k_1 t_1) (* k_2 t_2)) k_3) with all k >= 0
       ------
       (>= (+ t_1 t_2) 0)
    */
    bool lemma_merge_generalizer::half_plane_03 (const expr_ref &literal, const expr * pattern,
                                                 const expr_ref_vector &neighbour_lemmas,
                                                 expr_ref_vector &conjectures)
    {
        if(!only_halfSpace(literal)) { return false; }
        STRACE("merge_strategies", tout << "entered half_plane_03 with: " << mk_epp(literal, m) << "\n";);
        expr_ref conj(m);
        rational rhs;
        app_ref app(m);
        app = to_app(literal);
        expr_ref_vector var_coeff(m), neg_coeff_uniCs(m), pos_coeff_uniCs(m);
        get_uninterp_consts_with_var_coeff(to_app(pattern), var_coeff);

        if(var_coeff.size() == 0) { return false; }

        get_uninterp_consts_with_pos_coeff(app, pos_coeff_uniCs);
        get_uninterp_consts_with_neg_coeff(app, neg_coeff_uniCs);

        expr_ref sum(m), neg_sum(m), pos_sum(m);
        sum = m_arith.mk_add(var_coeff.size(), var_coeff.c_ptr());

        STRACE("merge_strategies", tout <<
               "literal: " << mk_epp(literal, m) << "\n" <<
               "app->get_arg(1): " << mk_epp(app->get_arg(1), m) << "\n" <<
               "sum: " << mk_epp(sum, m) << "\n"
               ;);
        if(only_halfSpace(literal)){
            if(gt_or_geq(literal)){
                if(!m_arith.is_numeral(app->get_arg(1), rhs)) { return false; }
                if(!(rhs > 0)) { return false; }
            }
            if(lt_or_leq(literal)){
                if(!m_arith.is_numeral(app->get_arg(1), rhs)) { return false; }
                if(!(rhs < 0)) { return false; }
            }

            if(neg_coeff_uniCs.size() > 0){
                // JEF: neg_coeff hence top level not
                neg_sum = m_arith.mk_add(neg_coeff_uniCs.size(), neg_coeff_uniCs.c_ptr());
                conj = m.mk_not(m.mk_app(app->get_family_id(), app->get_decl_kind(), sum, m_arith.mk_int(0)));
                conjectures.push_back(conj);
                STRACE("merge_strategies", tout << "Conj: " << mk_epp(conj, m) << "\n";);
            }
            else if(pos_coeff_uniCs.size() > 0){
                pos_sum = m_arith.mk_add(pos_coeff_uniCs.size(), pos_coeff_uniCs.c_ptr());
                conj = m.mk_app(app->get_family_id(), app->get_decl_kind(), sum, m_arith.mk_int(0));
                conjectures.push_back(conj);
                STRACE("merge_strategies", tout << "Conj: " << mk_epp(conj, m) << "\n";);
            }

        }
        STRACE("merge_strategies", tout << "Ret: " << !conjectures.empty() << "\n";);
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

      // XXX JEF: This is aggressive imo;
      [Branch 3.1]
      (>= t_1 k_1) (>= t_2 k_2) and k_1 > k_2
      ------
      (> t_1 t_2)

      [Branch 3.2]
      (>= t_1 k_1) (>= t_2 k_2) and k_1 < k_2
      ------
      (< t_1 t_2)

      // TODO Branch 4.1 & 4.2: flip side of 3.1 and 3.2

    */
    bool lemma_merge_generalizer::half_plane_XX(const expr_ref &literal, const expr_ref &pattern,
                                                const expr_ref_vector &neighbour_lemmas,
                                                expr_ref_vector &conjectures)
    {
        expr_ref conj(m);
        if (! (m.is_and(literal) && to_app(literal)->get_num_args() == 2)) return false;

        expr_ref fst(m), snd(m);
        fst = to_app(literal)->get_arg(0);
        snd = to_app(literal)->get_arg(1);

        // check for right operators
        if(!(only_halfSpace(fst)) || !(only_halfSpace(snd))) { return false; }

        // check for numerics
        rational k1, k2;
        if(!(m_arith.is_numeral(to_app(fst)->get_arg(1), k1)) ||
           !(m_arith.is_numeral(to_app(snd)->get_arg(1), k2))) { return false; }

        expr_ref t1(m), t2(m);
        t1 = to_app(fst)->get_arg(0);
        t2 = to_app(snd)->get_arg(0);

        if(gt_or_geq(fst) && lt_or_leq(snd)){
            if(k1 > k2){
                // [Branch 1]
                conj = m_arith.mk_gt(t1, t2);
                conjectures.push_back(conj);
                return true;
            }
        } else if(lt_or_leq(fst) && gt_or_geq(snd)){
            if(k1 < k2){
                // [Branch 2]
                conj = m_arith.mk_lt(t1, t2);
                conjectures.push_back(conj);
                return true;
            }
        } else if(gt_or_geq(fst) && gt_or_geq(snd)){
            if(k1 > k2){
                // [Branch 3.1]
                conj = m_arith.mk_gt(t1, t2);
                conjectures.push_back(conj);
                return true;
            }
            if(k1 < k2){
                // [Branch 3.2]
                conj = m_arith.mk_gt(t1, t2);
                conjectures.push_back(conj);
                return true;
            }
        }
        // none of the conjectures fits, give up!
        return false;
    }


    void lemma_merge_generalizer::operator()(lemma_ref &lemma){
        expr_ref_vector neighbours = lemma->get_neighbours();
        if(neighbours.size() == 0) { return; }
        substitution subs_newLemma(m), subs_oldLemma(m);
        expr_ref cube(m), normalizedCube(m), out(m);
        expr_ref_vector non_boolean_literals(m);
        expr_ref_vector conjuncts(m);

        cube = mk_and(lemma->get_cube());
        normalize_order(cube, normalizedCube);
        TRACE("merge_dbg",
              tout << "Start merging with lemma cube: " << mk_pp(normalizedCube, m) << "\n"
              "Discovered pattern: " << mk_pp(neighbours.get(0), m) << "\n"
              "Neighbours: " << mk_pp(neighbours.get(1), m) << "\n"
              ;);

        expr_ref pat(m);
        pat = neighbours.get(0);
        // if(merge_summarize(normalizedCube, pat, neighbours, conjuncts)){
        //     // TODO update
        // }

        // update the pattern by dropping singleton uninterp_consts
        if(m.is_and(neighbours.get(0))){
            for(expr * c: *to_app(neighbours.get(0))){
                if(m.is_not(c) && is_uninterp_const(to_app(c)->get_arg(0))) { continue; }
                if(!is_uninterp_const(c)) { non_boolean_literals.push_back(c); }
            }
        }
        STRACE("fun", tout << "non_boolean_literals\n";
               for(auto nbl:non_boolean_literals){ tout << mk_pp(nbl, m) << "\n"; };);
        if(non_boolean_literals.size() > 0) {
            neighbours.set(0, mk_and(non_boolean_literals));
            non_boolean_literals.reset();
            for(auto c:lemma->get_cube()){
                if(m.is_not(c) && is_uninterp_const(to_app(c)->get_arg(0))) { continue; }
                if(!is_uninterp_const(c))
                    non_boolean_literals.push_back(c);
            }
            cube = mk_and(non_boolean_literals);
            normalize_order(cube, normalizedCube);
            STRACE("fun", tout << "non_boolean_literals_cube: " << mk_pp(normalizedCube, m) << "\n";);
        }

        if(half_plane_01(normalizedCube, normalizedCube, neighbours, conjuncts)){
            STRACE("merge_strategies", tout << "Applied half_plane_01 on: " << mk_pp(normalizedCube, m) << "\n";);
            if(check_inductive_and_update(lemma, conjuncts))
                return;
        }

        if(half_plane_02(normalizedCube, normalizedCube, neighbours, conjuncts)){
            STRACE("merge_strategies", tout << "Applied half_plane_02 on: " << mk_pp(normalizedCube, m) << "\n";);
            if(check_inductive_and_update(lemma, conjuncts))
                return;
        }

        if(half_plane_03(normalizedCube, neighbours.get(0), neighbours, conjuncts)){
            STRACE("merge_strategies", tout << "Applied half_plane_03 on: " << mk_pp(normalizedCube, m) << "\n";);
            if(check_inductive_and_update(lemma, conjuncts))
                return;
        }


       if(half_plane_XX(normalizedCube, normalizedCube, neighbours, conjuncts)){
            STRACE("merge_strategies", tout << "Applied half_plane_XX on: " << mk_pp(normalizedCube, m) << "\n";);
            if(check_inductive_and_update(lemma, conjuncts))
                return;
        }

        if(neighbours.size() >= 10) {
            TRACE("cluster_stats", tout << "Found big cluster and Tried all merge strategies\n";);
            return;
            // throw unknown_exception();
        }

        TRACE("merge_dbg", tout << "tried all merge strategies\n";);
        return;
    }
    /* core lemma update function*/
    bool lemma_merge_generalizer::check_inductive_and_update(lemma_ref &lemma, expr_ref_vector conj){
        STRACE("merge_dbg", tout << "Attempt to update lemma with: "
               << mk_pp(conj.back(), m) << "\n";);
        STRACE("merge_dbg", tout << "lemma_lvl: " << lemma->level() << "\n";);
        pred_transformer &pt = lemma->get_pob()->pt();
        lemma_ref_vector all_lemmas;
        pt.get_all_lemmas(all_lemmas, false);
        unsigned uses_level = 0;
        if(pt.check_inductive(lemma->level(), conj, uses_level, lemma->weakness())){
            STRACE("merge_dbg", tout << "Inductive!" << "\n";);
            lemma->update_cube(lemma->get_pob(), conj);
            lemma->set_level(uses_level);
            return true;
        } else {
            STRACE("merge_dbg", tout << "Not inductive!" << "\n";);
            return false;
        }
    }

    void lemma_merge_generalizer::collect_statistics(statistics &st) const{
        // TODO update stats here
    }

    /*
      Summarize using concrete numerical bounds from neighbours
      1) simple half spaces (>= t1 n1)
     */
    bool lemma_merge_generalizer::merge_summarize(const expr_ref &literal,
                                                  const expr_ref pattern,
                                                  const expr_ref_vector &neighbour_lemmas,
                                                  expr_ref_vector &conjectures)
    {
        if(!only_halfSpace(literal)) { return false; }
        TRACE("merge_dbg_summarize",
              tout << "---Pattern---\n" << pattern << "\n"
              << "---Concrete lemmas---\n";
              for(auto *n : neighbour_lemmas){
                  tout << "(" << n->get_id() << "):\n"
                       << mk_epp(n, m) << "\n";
              };
              tout << "\n------\n"
              ;);

        // case 1) simple half spaces
        if(is_simple_literal(pattern)){
            rational maxima(0), minima(0), temp(0);
            for(auto *n : neighbour_lemmas){
                if(!m_arith.is_numeral(to_app(n)->get_arg(1), temp)) { continue; }
                if(temp >= maxima){ maxima = temp; }
                if(temp <= minima){ minima = temp; }
            }
            TRACE("merge_dbg_summarize",
                  tout << "---Simple half spaces---\n";
                  tout << "MAX/MIN: " << maxima << "/" << minima;
                  tout << "\n------\n"
                  ;);
        }
        return false;
    }
}
