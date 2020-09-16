/*++
  Copyright (c) 2020 Arie Gurfinkel

  Module Name:

  spacer_expand_bnd_generalizer.cpp

  Abstract:

  Strengthen lemmas by changing numeral constants inside arithmetic literals

  Author:

  Hari Govind V K
  Arie Gurfinkel

--*/
#include "muz/spacer/spacer_expand_bnd_generalizer.h"
#include "ast/rewriter/expr_safe_replace.h"

namespace {
/// Checks whether \p fml is an arithmetic inequality with a numeral \p val on
/// the rhs
bool is_ineq(ast_manager &m, const expr *fml, rational &val) {
    arith_util m_arith(m);
    expr *e1, *e2;
    if (m.is_not(fml, e1)) return is_ineq(m, e1, val);
    // AG: why is strict inequality not handled?
    // AG: why not handle bv case as well?
    if (m_arith.is_le(fml, e1, e2) || m_arith.is_ge(fml, e1, e2))
        return m_arith.is_numeral(e1, val);
    return false;
}

/// Replace RHS of \p fml with \p n
void substitute(rational n, const expr *fml, expr_ref &res) {
    SASSERT(is_app(fml));
    ast_manager &m = res.get_manager();
    arith_util m_arith(m);

    rational val;
    (void)val;
    SASSERT(is_ineq(m, fml, val));

    expr *e1;
    if (m.is_not(fml, e1)) {
        substitute(n, e1, res);
        ::push_not(res);
        return;
    }
    expr *lhs = to_app(fml)->get_arg(0);
    res = m.mk_app(to_app(fml)->get_decl(), lhs,
                   m_arith.mk_numeral(n, n.is_int()));
}

/// Substitute \p lit in \p fml with \p sub
void replace(expr_ref lit, expr_ref sub, expr_ref_vector &fml) {
    for (unsigned i = 0, sz = fml.size(); i < sz; ++i) {
        if (fml.get(i) == lit) {
            fml[i] = sub;
            return;
        }
    }
    // -- if we got here, `lit` is not in fml
    fml.push_back(sub);
}

} // namespace
namespace spacer {
lemma_expand_bnd_generalizer::lemma_expand_bnd_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m) {
    // -- collect numeric constants that appear in transition relation
    for (auto &kv : ctx.get_pred_transformers()) {
        kv.m_value->extract_nums(m_values);
    }
}

void lemma_expand_bnd_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    if (!lemma->get_pob()->expand_bnd()) return;

    // -- try expanding bounds
    const expr_ref_vector &conj = lemma->get_cube();
    // -- new lemma, initially same as conj
    expr_ref_vector updt_conj(conj);

    expr_ref lit(m), new_lit(m);
    rational val;
    for (unsigned i = 0; i < conj.size(); i++) {
        lit = conj.get(i);
        if (!is_ineq(m, lit, val)) continue;
        // AG: unnecessarily expensive. This can be codded better, for example
        // AG: by replacing deleted literals with `true` until the end
        if (!updt_conj.contains(lit)) continue;

        TRACE("expand_bnd", tout << "Attempting to expand " << lit << " inside "
                                 << conj << "\n";);

        for (rational n : m_values) {
            // AG: potentially expensive in a tight loop
            if (!updt_conj.contains(lit)) break;
            if (!should_apply(lit, val, n)) continue;

            TRACE("expand_bnd", tout << "Attempting to expand " << lit
                                     << " with numeral " << n << "\n";);

            // -- update bound on lit
            substitute(n, lit, new_lit);
            SASSERT(new_lit.get() != nullptr);
            // -- update lit to new_lit in new candidate lemma
            replace(lit, new_lit, updt_conj);
            m_st.atmpts++;

            // -- check that candidate is inductive
            if (check_ind_and_update(lemma, updt_conj)) {
                // -- it worked, try another number
                lit = new_lit;
                if (!is_ineq(m, lit, val)) break;
            }
            // AG: if check_ind_and_update fails, why not try another number?
            // AG: why check another number if generalization succeeded? Are the
            // numbers ordered in some way?
        }
    }

    // -- maybe count how many times this worked, and allow for more than one
    // round
    lemma->get_pob()->stop_expand_bnd();
}

/// Check whether \p conj is a possible generalization for \p lemma.
/// update \p lemma if it is.
bool lemma_expand_bnd_generalizer::check_ind_and_update(lemma_ref &lemma,
                                                        expr_ref_vector &cand) {
    unsigned uses_level = 0;
    TRACE("expand_bnd_verb",
          tout << "Attempting to update lemma with " << cand << "\n";);
    bool is_ind = (lemma->get_pob())
                      ->pt()
                      .check_inductive(lemma->level(), cand, uses_level,
                                       lemma->weakness());
    if (is_ind) {
        m_st.success++;
        lemma->update_cube(lemma->get_pob(), cand);
        lemma->set_level(uses_level);
        TRACE("expand_bnd", tout << "expand_bnd succeeded with " << mk_and(cand)
                                 << " at level " << uses_level << "\n";);
    }
    return is_ind;
}
/// Check whether \p n can be used to weaken lit
bool lemma_expand_bnd_generalizer::should_apply(const expr *lit, rational n) {
    rational val;
    if (!is_ineq(m, lit, val)) return false;
    return should_apply(lit, val, n);
}

/// Check whether lit ==> lit[val |--> n] (barring special cases). That is,
/// whether \p lit becomes weaker if \p val is replaced with \p n
///
/// \p lit has to be of the form t <= v where v is a numeral.
/// Special cases:
/// In the trivial case in which \p val == \p n, return false.
/// if lit is an equality or the negation of an equality, return true.
bool lemma_expand_bnd_generalizer::should_apply(const expr *lit, rational val,
                                                rational n) {
    // the only case in which negation and non negation agree
    if (val == n) return false;

    // negation is the actual negation modulo val == n
    expr *e1;
    if (m.is_not(lit, e1)) { return !should_apply(e1, val, n); }

    SASSERT(val != n);
    if (m.is_eq(lit)) return true;
    switch (to_app(lit)->get_decl_kind()) {
    case OP_LE:
    case OP_LT:
        return n > val;
    case OP_GT:
    case OP_GE:
        return n < val;
    default:
        return false;
    }
}

void lemma_expand_bnd_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.expand", m_st.watch.get_seconds());
    st.update("SPACER expand_bnd attmpts", m_st.atmpts);
    st.update("SPACER expand_bnd success", m_st.success);
}
} // namespace spacer
