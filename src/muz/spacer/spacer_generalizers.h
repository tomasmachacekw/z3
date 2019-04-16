/*++
Copyright (c) 2017 Microsoft Corporation and Arie Gurfinkel

Module Name:

    spacer_generalizers.h

Abstract:

    Generalizer plugins.

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-22.
    Arie Gurfinkel
Revision History:

--*/

#ifndef _SPACER_GENERALIZERS_H_
#define _SPACER_GENERALIZERS_H_

#include "muz/spacer/spacer_context.h"
#include "ast/arith_decl_plugin.h"

namespace spacer {

// can be used to check whether produced core is really implied by
// frame and therefore valid TODO: or negation?
class lemma_sanity_checker : public lemma_generalizer {
public:
    lemma_sanity_checker(context& ctx) : lemma_generalizer(ctx) {}
    ~lemma_sanity_checker() override {}
    void operator()(lemma_ref &lemma) override;
};

/**
 * Boolean inductive generalization by dropping literals
 */
class lemma_bool_inductive_generalizer : public lemma_generalizer {

    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() {reset();}
        void reset() {count = 0; num_failures = 0; watch.reset();}
    };

    unsigned m_failure_limit;
    bool m_array_only;
    stats m_st;

public:
    lemma_bool_inductive_generalizer(context& ctx, unsigned failure_limit,
                                     bool array_only = false) :
        lemma_generalizer(ctx), m_failure_limit(failure_limit),
        m_array_only(array_only) {}
    ~lemma_bool_inductive_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics& st) const override;
    void reset_statistics() override {m_st.reset();}
};

class unsat_core_generalizer : public lemma_generalizer {
    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() { reset(); }
        void reset() {count = 0; num_failures = 0; watch.reset();}
    };

    stats m_st;
public:
    unsat_core_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    ~unsat_core_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics &st) const override;
    void reset_statistics() override {m_st.reset();}
};

class lemma_array_eq_generalizer : public lemma_generalizer {
private:
    bool is_array_eq(ast_manager &m, expr *e);
public:
    lemma_array_eq_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    ~lemma_array_eq_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

};

class lemma_eq_generalizer : public lemma_generalizer {
public:
    lemma_eq_generalizer(context &ctx) : lemma_generalizer(ctx) {}
    ~lemma_eq_generalizer() override {}
    void operator()(lemma_ref &lemma) override;
};

class lemma_quantifier_generalizer : public lemma_generalizer {
    struct stats {
        unsigned count;
        unsigned num_failures;
        stopwatch watch;
        stats() {reset();}
        void reset() {count = 0; num_failures = 0; watch.reset();}
    };

    ast_manager &m;
    arith_util m_arith;
    stats m_st;
    expr_ref_vector m_cube;

    bool m_normalize_cube;
    int m_offset;
public:
    lemma_quantifier_generalizer(context &ctx, bool normalize_cube = true);
    ~lemma_quantifier_generalizer() override {}
    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics& st) const override;
    void reset_statistics() override {m_st.reset();}
private:
    bool generalize(lemma_ref &lemma, app *term);

    void find_candidates(expr *e, app_ref_vector &candidate);
    bool is_ub(var *var, expr *e);
    bool is_lb(var *var, expr *e);
    void mk_abs_cube (lemma_ref &lemma, app *term, var *var,
                      expr_ref_vector &gnd_cube,
                      expr_ref_vector &abs_cube,
                      expr *&lb, expr *&ub, unsigned &stride);

    bool match_sk_idx(expr *e, app_ref_vector const &zks, expr *&idx, app *&sk);
    void cleanup(expr_ref_vector& cube, app_ref_vector const &zks, expr_ref &bind);

    bool find_stride(expr_ref_vector &c, expr_ref &pattern, unsigned &stride);
};

class lemma_merge_generalizer : public lemma_generalizer {
    ast_manager &m;
    arith_util m_arith;
    int threshold;
    typedef std::pair<rational, expr*> coeff_uninterpC;
    typedef vector<coeff_uninterpC> coeff_uninterpC_vec;

public:
    lemma_merge_generalizer(context &ctx, int threshold);
    ~lemma_merge_generalizer() override {}
    void operator()(lemma_ref &lemma) override;
    bool check_inductive_and_update(lemma_ref &lemma, expr_ref_vector conj);

private:
    bool leq_monotonic_k(expr_ref &l, app *pattern, expr_ref &out);
    bool leq_monotonic_neg_k(expr_ref &l, app *pattern, expr_ref &out);
    bool merge_halfspaces(expr_ref &literal, app *pattern, expr_ref &out, expr_ref_vector &conjuncts);
    bool merge_lines(expr_ref &literal, app *pattern, expr_ref &out);
    bool monotonic_coeffcient(expr_ref &literal, app *pattern, expr_ref &out);
    bool neighbour_equality(expr_ref &literal, app *pattern, expr_ref_vector &neighbour, expr_ref &out);

    // Guards
    bool half_plane_01(expr_ref literal, expr_ref pattern,
                       expr_ref_vector neighbour_lemmas, expr_ref_vector &conjectures);
    bool half_plane_02(expr_ref literal, expr_ref pattern,
                       expr_ref_vector neighbour_lemmas, expr_ref_vector &conjectures);
    bool half_plane_03(expr_ref literal, app * pattern,
                        expr_ref_vector neighbour_lemmas, expr_ref_vector &conjectures);
    bool half_plane_XX(expr_ref literal, expr_ref pattern,
                       expr_ref_vector neighbour_lemmas, expr_ref_vector &conjectures);
};

class lemma_cluster : public lemma_generalizer {
    ast_manager &m;
    arith_util m_arith;
    int m_dis_threshold;
    typedef std::pair<unsigned, unsigned> var_offset;

private:
    /// Returns an approximate distance between two substitutions relative to a pattern
    /// 0 means that the substitutions are equivalent, larger number means less similarity
    int distance(expr_ref antiU_result, substitution &s1, substitution &s2);
    expr_ref_vector generate_groups(expr *pattern);
    void with_var_coeff(app *a, expr_ref_vector &out, bool has_var_coeff);

public:
    lemma_cluster(context &ctx, int disT);
    ~lemma_cluster() override {}
    void operator()(lemma_ref &lemma) override;

};
}

#endif
