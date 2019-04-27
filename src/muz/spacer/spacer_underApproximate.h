#include "ast/ast.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "spacer_context.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "util/rational.h"

typedef obj_map<expr, expr *> expr_expr_map;
namespace spacer {
class under_approx {
    ast_manager &m;
    arith_util m_arith;

    // reference to all bounds that were made
    expr_ref_vector m_refs;

    /// returns true if e is an arithmetic expression
    bool is_arith(expr *e); 

    bool find_coeff(expr *t, expr *v, rational &k, bool negated = false);
    int under_approx_var(expr *t, expr *c, expr *d);
    void under_approx_lit(model_ref &model, expr *t, expr *c,
                          expr_ref_vector &bg,
                          expr_expr_map &lb, expr_expr_map &ub,
                          expr_expr_map *sub = nullptr);


    void under_approx_cube(const expr_ref_vector &cube, model_ref &model,
                           expr_expr_map &lb, expr_expr_map &ub,
                           expr_expr_map *sub = nullptr);


    bool is_disjoint(expr_ref_vector group);
    bool is_disjoint(app *g1, app *g2);
    void group(expr_ref_vector conj, expr_ref_vector groups, model_ref model,
               expr_ref_vector &ua_conj);

    bool is_constant(expr const *e) {
        return is_uninterp_const(e) || m_arith.is_numeral(e);
    }

    bool is_le(expr *lit, expr_ref &t, expr_ref &c); 
    // each literal in e is Sum Of Products form
    bool is_sop(expr_ref_vector const &e) {
        for (expr *a : e) {
            if (!is_sop(a)) return false;
        }
        return true;
    }
    bool is_sop(expr const *e);

    // returns true when each expression in group is either a sub expr of any of
    // the literals in exp or not in any of the literals of exp
    bool can_group(const expr_ref_vector &exp, expr_ref_vector &group) {
        // assuming exp is an and of its arguments.
        for (expr *v : group) {
            if (!can_group(exp, v)) return false;
        }
        return true;
    }
    // TODO : implement this
    bool can_group(const expr_ref_vector &exp, expr *v) { return true; }

  public:
    under_approx(ast_manager &manager) : m(manager), m_arith(m), m_refs(m) {}
    bool under_approximate(expr *n, model_ref &model, expr_ref_vector &u_a);
};
} // namespace spacer
