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
    bool lemma_merge_generalizer::half_plane_01 (const expr_ref &literal, const expr_ref &pattern,
                                                 const expr_ref_vector &neighbour_lemmas, expr_ref_vector &conjectures)
    {
        if(!(lt_or_leq(literal)) || !is_simple_literal(literal)) { return false; }
        ast_manager m = literal.get_manager();
        arith_util m_arith(m);
        expr_ref conj(m);
        rational rhs;
        if(m_arith.is_numeral(to_app(literal)->get_arg(1), rhs) && rhs >= 0) { 

            // AG: assumes that literal is integer sort, but could be rational sort
            conj = m.mk_app(to_app(literal)->get_family_id(),
                            to_app(literal)->get_decl_kind(),
                            to_app(literal)->get_arg(0), m_arith.mk_int(0));
            conjectures.push_back(conj);
            // AG: dead code
            if(rhs < -1) {
                conj = m_arith.mk_lt(to_app(literal)->get_arg(0), m_arith.mk_int(0));
                conjectures.push_back(conj);
            }
            return true;
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
        ast_manager m = literal.get_manager();
        arith_util m_arith(m);
        expr_ref conj(m);
        rational rhs;


        if(m_arith.is_numeral(to_app(literal)->get_arg(1), rhs) && rhs <= 0) { 
            // AG: what if literal is of sort real
            conj = m.mk_app(to_app(literal)->get_family_id(),
                            to_app(literal)->get_decl_kind(),
                            to_app(literal)->get_arg(0), m_arith.mk_int(0));
            conjectures.push_back(conj);
            // AG: dead code
            if(rhs > 1) {
                conj = m_arith.mk_lt(to_app(literal)->get_arg(0), m_arith.mk_int(0));
                conjectures.push_back(conj);
            }
            return true;
        }
        return false;
    }

    /* (>= (+ (* k_1 t_1) (* k_2 t_2)) k_3) with all k >= 0
       ------
       (>= (+ t_1 t_2) 0)
    */
    bool lemma_merge_generalizer::half_plane_03 (const expr_ref &literal, const expr_ref &pattern,
                                                 const expr_ref_vector &neighbour_lemmas,
                                                 expr_ref_vector &conjectures)
    {
        if(!only_halfSpace(literal)) { return false; }
        STRACE("merge_strategies", tout << "Applied half_plane_03 on: " << mk_epp(literal, m) << "\n";);
        ast_manager m = literal.get_manager();
        arith_util m_arith(m);
        expr_ref conj(m);
        rational rhs;
        app_ref app(m);
        app = to_app(literal);
        expr_ref_vector var_coeff(m), neg_coeff_uniCs(m), pos_coeff_uniCs(m);
        get_uninterp_consts_with_var_coeff(to_app(pattern), var_coeff);

        if(var_coeff.size() == 0) { return false; }

        get_uninterp_consts_with_pos_coeff(app, pos_coeff_uniCs);
        get_uninterp_consts_with_neg_coeff(app, neg_coeff_uniCs);

        expr_ref sum(m);
        sum = m_arith.mk_add(var_coeff.size(), var_coeff.c_ptr());
        STRACE("merge_strategies", tout << "literal: " << mk_epp(literal, m) << "\n";);
        if(gt_or_geq(literal)){
            if(!m_arith.is_numeral(app->get_arg(1), rhs) || !(rhs >= 0)) { return false; }
            if(!pos_coeff_uniCs.empty()){
                conj = m.mk_app(app->get_family_id(), app->get_decl_kind(), sum, m_arith.mk_int(0));
                conjectures.push_back(conj);
            }
        } else {
            SASSERT(lt_or_leq(literal));
            if(!m_arith.is_numeral(app->get_arg(1), rhs) || !(rhs <= 0)) { return false; }
            if(!pos_coeff_uniCs.empty()){
                conj = m.mk_app(app->get_family_id(), app->get_decl_kind(), sum, m_arith.mk_int(0));
                conjectures.push_back(conj);
            }
        }
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

      [Branch 3.1]
      (>= t_1 k_1) (>= t_2 k_2) and k_1 > k_2
      ------
      (> t_1 t_2)

      [Branch 3.2]
      (>= t_1 k_1) (>= t_2 k_2) and k_1 < k_2
      ------
      (< t_1 t_2)


    */
    bool lemma_merge_generalizer::half_plane_XX(const expr_ref &literal, const expr_ref &pattern,
                                                const expr_ref_vector &neighbour_lemmas,
                                                expr_ref_vector &conjectures)
    {
        expr_ref conj(m);
        if (! (m.is_and(literal) && to_app(literal)->get_num_args() == 2)) return false;

        TRACE("AHA", tout << "Entered half_plane_XX\n" << literal << "\n";);

        expr_ref fst(m), snd(m);
        fst = to_app(literal)->get_arg(0);
        snd = to_app(literal)->get_arg(1);

        STRACE("AHA", tout << "fst: " << fst << "\nsnd:" << snd << "\n" ;);

        // check for right operators
        if(!(only_halfSpace(fst)) || !(only_halfSpace(snd))) { return false; }

        // check for numerics
        rational k1, k2;
        if(!(m_arith.is_numeral(to_app(fst)->get_arg(1), k1)) ||
           !(m_arith.is_numeral(to_app(snd)->get_arg(1), k2))) { return false; }

        expr_ref t1(m), t2(m);
        t1 = to_app(fst)->get_arg(0);
        t2 = to_app(snd)->get_arg(0);

        STRACE("AHA", tout << "t1: " << t1 << "\nt2:" << t2 << "\n" ;);

        if(gt_or_geq(fst) && lt_or_leq(snd)){
            if(k1 > k2){
                STRACE("AHA", tout << "branch 1\n";);
                // [Branch 1]
                conj = m_arith.mk_gt(t1, t2);
                conjectures.push_back(conj);
                return true;
            }
        } else if(lt_or_leq(fst) && gt_or_geq(snd)){
            if(k1 < k2){
                STRACE("AHA", tout << "branch 2\n";);
                // [Branch 2]
                conj = m_arith.mk_lt(t1, t2);
                conjectures.push_back(conj);
                return true;
            }
        } else if(gt_or_geq(fst) && gt_or_geq(snd)){
            if(k1 > k2){
                STRACE("AHA", tout << "branch 3.1\n";);
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
        } // TODO Branch 4.1 & 4.2
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
        if(merge_summarize(normalizedCube, pat, neighbours, conjuncts)){
            // TODO update
        }

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

        // if(monotonic_coeffcient(cube, to_app(neighbours.get(0)), out)){
        //     STRACE("cluster_stats", tout << "mono coeff found a conjecture...\n"
        //            << mk_pp(out, m) << "\n";);
        //     expr_ref_vector conj(m);
        //     conj.push_back(out);
        //     if(check_inductive_and_update(lemma, conj))
        //         return;

        // }

        /* if(merge_halfspaces(normalizedCube, to_app(neighbours.get(0)), out, conjuncts)){ */
        /*     STRACE("cluster_stats", tout << "merge halfplanes found a conjecture...\n" */
        /*            << mk_pp(out, m) << "\n";); */
        /*     expr_ref_vector conj(m); */
        /*     conj.push_back(out); */
        /*     if(check_inductive_and_update(lemma, conj)) */
        /*         return; */
        /*     else{ */
        /*         conjuncts.push_back(out); */
        /*         conj.reset(); */
        /*         conj.push_back(mk_and(conjuncts)); */
        /*         if(check_inductive_and_update(lemma, conj)) */
        /*             return; */
        /*     } */
        /* } */

        // if(leq_monotonic_neg_k(normalizedCube, to_app(neighbours.get(0)), out)){
        //     STRACE("cluster_stats", tout << "leq monotoinc k found a conjecture...\n"
        //            << mk_pp(out, m) << "\n";);
        //     expr_ref_vector conj(m);
        //     conj.push_back(out);
        //     if(check_inductive_and_update(lemma, conj))
        //         return;
        // }

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

        if(half_plane_03(normalizedCube, normalizedCube, neighbours, conjuncts)){
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
    /*
      TODO cluster statistics / conjecture effective statistics
      TODO formalize guards
      TODO frame this as strategies
      TODO problem classification: linear pattern / non-linear patterns
      TODO guard normalization
    */
    /* with t <= k
       conjecture t <= infinite */
    bool lemma_merge_generalizer::leq_monotonic_k(expr_ref &literal, app *pattern, expr_ref &out){
        if(m_arith.is_le(pattern) && is_var(pattern->get_arg(1))){
            if(get_num_vars(pattern->get_arg(0)) == 0){
                out = m_arith.mk_le(pattern->get_arg(0), m_arith.mk_int(0));
                return true;
            }
        }
        if(m_arith.is_ge(pattern) && is_var(pattern->get_arg(1))){
            if(get_num_vars(pattern->get_arg(0)) == 0){
                out = m_arith.mk_ge(pattern->get_arg(0), m_arith.mk_int(0));
                return true;
            }
        }
        return false;
    }

    /* with t <= k , k < 0
       conjecture t <= 0 */
    bool lemma_merge_generalizer::leq_monotonic_neg_k(expr_ref &literal, app *pattern, expr_ref &out){
        if(m_arith.is_le(pattern) && is_var(pattern->get_arg(1)) && get_num_vars(pattern->get_arg(0)) == 0){
            SASSERT(is_app(literal));
            SASSERT(m_arith.is_numeral(to_app(literal)->get_arg(1)));
            rational r;
            m_arith.is_numeral(to_app(literal)->get_arg(1), r);
            if(r < 0){
                out = m_arith.mk_lt(pattern->get_arg(0), m_arith.mk_int(0));
                return true;
            } else if (r <= 0){
                out = m_arith.mk_le(pattern->get_arg(0), m_arith.mk_int(0));
                return true;
            }
        }
        if(m_arith.is_ge(pattern) && is_var(pattern->get_arg(1)) && get_num_vars(pattern->get_arg(0)) == 0){
            SASSERT(is_app(literal));
            SASSERT(m_arith.is_numeral(to_app(literal)->get_arg(1)));
            rational r;
            m_arith.is_numeral(to_app(literal)->get_arg(1), r);
            if(r > 0){
                out = m_arith.mk_gt(pattern->get_arg(0), m_arith.mk_int(0));
                return true;
            } else if (r <= 0){
                out = m_arith.mk_ge(pattern->get_arg(0), m_arith.mk_int(0));
                return true;
            }
        }


        return false;
    }

    /* with t1 <= k1 && k2 <= t2 , k1 + c = k2
       conjecture t1 + c' <= t2 where 0 <= c' <= c */
    // XXX potentially return expr_ref_vector for c' from 0 to c
    bool lemma_merge_generalizer::merge_halfspaces(expr_ref &literal, app *pattern, expr_ref &out, expr_ref_vector &conjuncts){
        if(m.is_and(pattern) && pattern->get_num_args() == 2){
            app * concrete_fst = to_app(to_app(literal)->get_arg(0));
            app * concrete_snd = to_app(to_app(literal)->get_arg(1));
            app * fst = to_app(pattern->get_arg(0));
            app * snd = to_app(pattern->get_arg(1));
            TRACE("spacer_diverge_dbg",
                  tout << " fst : " << mk_pp(fst, m) << "\n"
                  << " snd : " << mk_pp(snd, m) << "\n"
                  << " c_fst : " << mk_pp(concrete_fst, m) << "\n"
                  << " c_snd : " << mk_pp(concrete_snd, m) << "\n"
                  ;);
            if(m_arith.is_ge(fst) && m_arith.is_le(snd)){
                rational n1, n2;
                TRACE("merge_dbg", tout << "GOT HERE >= & <=\n";);
                if(m_arith.is_numeral(concrete_fst->get_arg(1), n1) &&
                   m_arith.is_numeral(concrete_snd->get_arg(1), n2)){
                    if(n1 > n2){
                        out = m_arith.mk_gt(fst->get_arg(0), snd->get_arg(0));
                        return true;
                    }
                }
            }

            if(m_arith.is_le(fst) && m_arith.is_ge(snd)){
                rational n1, n2;
                TRACE("merge_dbg", tout << "GOT HERE <= & >=\n";);
                if(m_arith.is_numeral(concrete_fst->get_arg(1), n1) &&
                   m_arith.is_numeral(concrete_snd->get_arg(1), n2)){
                    if(n1 < n2){
                        out = m_arith.mk_lt(fst->get_arg(0), snd->get_arg(0));
                        return true;
                    }
                }
            }

            if(m_arith.is_ge(fst) && m_arith.is_ge(snd)){
                rational n1, n2;
                TRACE("merge_dbg", tout << "GOT HERE >= & >=\n"
                      << mk_pp(concrete_fst, m) << "\n"
                      << mk_pp(concrete_snd, m) << "\n"
                      ;);
                if(m_arith.is_numeral(concrete_fst->get_arg(1), n1) &&
                   m_arith.is_numeral(concrete_snd->get_arg(1), n2)){
                    if(n1 > n2){
                        out = m_arith.mk_gt(concrete_fst->get_arg(0), concrete_snd->get_arg(0));
                        conjuncts.push_back( m_arith.mk_gt(concrete_fst->get_arg(0), m_arith.mk_int(n1)) );
                        conjuncts.push_back( m_arith.mk_gt(m_arith.mk_int(n2), concrete_snd->get_arg(0)) );
                        return true;
                    }
                    if(n1 < n2){
                        out = m_arith.mk_gt(concrete_snd->get_arg(0), concrete_fst->get_arg(0));
                        conjuncts.push_back( m_arith.mk_gt(concrete_snd->get_arg(0), m_arith.mk_int(n2)) );
                        conjuncts.push_back( m_arith.mk_gt(m_arith.mk_int(n1), concrete_fst->get_arg(0)) );
                        return true;
                    }
                }
            }


        }
        return false;
        // rational k1, k2;
        // expr_ref t1(m), t2(m);
        // out = m_arith.mk_le(t1, t2);
        // // out = m_arith.mk_le(m_arith.mk_add(t1, m_arith.mk_int(k2 - k1)), t2);
        // return false;
    }

    /* with t1 = k1 && t2 = k2 , k1 + c = k2
       conjecture t1 + c' <= t2 where 0 <= c' <= c */
    // XXX should the lemma be t1 = k1 && t2 = k2 or we have to scan for all equalities?
    // XXX alternatively we can have another merge (and eq1 eq2 ... eqn)
    bool lemma_merge_generalizer::merge_lines(expr_ref &literal, app *pattern, expr_ref &out){
        rational k1, k2;
        expr_ref t1(m), t2(m);
        // out = m_arith.mk_le(t1, t2);
        out = m_arith.mk_eq(m_arith.mk_add(t1, m_arith.mk_int(k2 - k1)), t2);
        return false;
    }

    /*
      with k1 * t1 + k2 * t2 >= t3 , k1 > 0 , k2 > 0
      conjecture t1 + t2 >= 0
    */
    bool lemma_merge_generalizer::monotonic_coeffcient(expr_ref &literal, app *pattern, expr_ref &out){
        expr_ref_vector uni_consts(m), var_coeff(m);
        num_expr_pair_vec coeff_uniC;
        expr_ref p(m);
        p = pattern;
        // if(m_arith.is_ge(pattern) || m_arith.is_gt(pattern)){
        if(gt_or_geq(p)){
            expr_ref_vector neg_coeff_uniCs(m), pos_coeff_uniCs(m);
            get_uninterp_consts_with_pos_coeff(to_app(literal), pos_coeff_uniCs);
            get_uninterp_consts_with_neg_coeff(to_app(literal), neg_coeff_uniCs);

            get_uninterp_consts_with_var_coeff(pattern, var_coeff);
            // XXX This check is necessary! arith.mk_add doesn't fallback gracefully with 0 as first argument

            if(var_coeff.size() > 0){
                expr_ref sum(m);
                sum = m_arith.mk_add(var_coeff.size(), var_coeff.c_ptr());
                // XXX TODO In case of mix signs on coeff, we need to spread on both sides of compare
                // if(neg_coeff_uniCs.size() > 0 && pos_coeff_uniCs.size() > 0) { return false; }
                // if the coefficients are negative we write positive coeff on out but with a sign flip on compare
                if(!neg_coeff_uniCs.empty()){
                    // func_decl * f_decl = pattern->get_decl();
                    // decl_kind dk = f_decl->get_decl_kind();
                    // TODO m.mk_app(m_faid, dk, sum, m_arith.mk_int(0))
                    out = m_arith.mk_lt(sum, m_arith.mk_int(0));
                }
                else if(!pos_coeff_uniCs.empty()){
                    out = m_arith.mk_lt(sum, m_arith.mk_int(0));
                }
                else { return false; }
                TRACE("merge_dbg", tout << "Mono coeff!\n"
                      << "Pattern: " << mk_pp(pattern, m) << "\n"
                      << "Cube: " << literal << "\n"
                      << "Out: " << mk_pp(out, m) << "\n"
                      << "Pos_coeff: " << pos_coeff_uniCs << "\n"
                      << "Neg_coeff: " << neg_coeff_uniCs << "\n"
                      ;);
                return true;
            }

        }
        return false;
    }

    /* merging over neighbours
       if we know a < b + k and b < a + k
       we can conjecture a == b
    */
    // XXX possibly the only merge without using pattern at all!
    bool lemma_merge_generalizer::neighbour_equality(expr_ref &literal, app *pattern, expr_ref_vector &neighbour, expr_ref &out){
        if( m_arith.is_ge(pattern) && get_num_uninterp_consts(pattern) == 0){
            // for 0 <= i < n :: check literal.uninterp_consts[i] == neighbour[1].uninterp_consts[n-i]
            TRACE("merge_dbg", tout << "Enter neighbour eq\n";);
            expr_ref_vector uc1(m), uc2(m);
            get_uninterp_consts(to_app(literal), uc1);
            get_uninterp_consts(to_app(neighbour.get(1)), uc2);
            // bool mismatch = false;
            TRACE("merge_dbg",
                  tout << "pattern:\n"
                  << mk_pp(pattern, m) << "\n"
                  << "uc1:\n"
                  << uc1 << "\n"
                  << "uc2:\n"
                  << uc1 << "\n"
                  ;);
            // if(uc1.size() == uc2.size() || uc1.size() == 0 || uc2.size() == 0){ return false; }
            out = m.mk_eq(uc1.get(0), uc2.get(0));
            return true;
            // int n = uc2.size();
            // for(int i = 0; i < n; i++){
            //     if(uc1.get(i) != uc2.get(n - 1 - i)){
            //         TRACE("merge_dbg", tout << "Mismatched!\n";);
            //         mismatch = true;
            //         break;
            //     }
            // }
            // if(!mismatch){
            //     out = m.mk_eq(uc1.get(0), uc2.get(0));
            //     return true;
            // }
        }
        return false;
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
        return false;
    }
}
