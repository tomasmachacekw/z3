#include "ast/ast.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "spacer_context.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "util/obj_ref_hashtable.h"
#include "util/rational.h"

typedef obj_ref_map<ast_manager, expr, expr *> expr_expr_map;
typedef obj_ref_map<ast_manager, expr, rational> expr_rat_map;
namespace spacer {
class under_approx {
    ast_manager &m;
    arith_util m_arith;
    // find the coeff of v in expr t
    // t is to be in SOP or -1*SOP form
    void find_coeff(expr_ref t, expr_ref v, rational &k);

    // returns whether lit increases(1), decreases(-1) or doesn't change(0) with
    // var
    int change_with_var(expr_ref lit, expr_ref var);

    // find bounds such that   (\Land_{x \in u_c(lit)} (lb_x <= x <= ub_x)) ==>
    // lit
    void under_approx_lit(model_ref &model, expr_ref lit, expr_rat_map &lb,
                          expr_rat_map &ub, expr_expr_map *sub = nullptr);

    // find bounds such that (\Land_{x \in u_c(lit)} (lb_x <= x <= ub_x)) ==>
    // cube
    void under_approx_cube(const expr_ref_vector &cube, model_ref &model,
                           expr_rat_map &lb, expr_rat_map &ub,
                           expr_expr_map *sub = nullptr);

    // find axis of cube according to pattern
    // find bounds such that (\Land_{x \in axis} (lb_x <= x <= ub_x)) ==> cube
    void grp_under_approx_cube(const expr_ref_vector &cube, expr_ref pattern,
                               model_ref &model, expr_ref_vector &ua);

    // check whether term is to be treated as a separate axis
    bool should_grp(expr *pattern, expr *term);

    // each var*u_c term in pattern is a single axis
    // all the other terms together constitute a single axis
    void grp_terms(expr_ref pattern, expr_ref formula, expr_ref_vector &out,
                   expr_ref_vector &sub_term);

    bool is_constant(expr const *e) {
        return is_uninterp_const(e) || m_arith.is_numeral(e);
    }

    // convert an arith expression lit into t <= c
    bool normalize_to_le(expr *lit, expr_ref &t, expr_ref &c);
    bool not_handled(expr *e) {
        expr *not_chld;
        return is_uninterp_const(e) || m_arith.is_numeral(e) || m.is_eq(e) ||
               has_mode(expr_ref(e, m)) ||
               (m.is_not(e, not_chld) && not_handled(not_chld));
    }

    // check Sum Of Products form
    bool is_sop(expr_ref_vector &e) {
        for (expr *a : e) {
            if (!is_sop(a)) return false;
        }
        return true;
    }
    bool is_sop(expr *e);

  public:
    under_approx(ast_manager &manager) : m(manager), m_arith(m) {}
    bool under_approximate(expr_ref n, model_ref &model, expr_ref_vector &u_a,
                           expr_ref pattern);
};
} // namespace spacer
