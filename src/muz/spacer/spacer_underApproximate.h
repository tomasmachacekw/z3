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

    expr *getLHS(const  expr *e) const {
        SASSERT(is_app(e));
        SASSERT(m_arith.is_arith_expr(e));
        return to_app(e)->get_arg(0);
    }
    expr *getRHS(const  expr *e) const {
        SASSERT(is_app(e));
        SASSERT(m_arith.is_arith_expr(e));
        return to_app(e)->get_arg(1);
    }

    void push_not(expr_ref &res);

    /// returns true if e is an arithmetic expression
    bool is_arith(expr *e) {
        // XXX handle equality
        expr *arg;
        if (!is_app(e)) return false;
        return m.is_not(e, arg) ? is_arith(arg) : m_arith.is_arith_expr(e);
    }

    void normalize_le(expr *e, expr_ref &result);
    bool get_coeff(expr* l, const expr *var, rational &coeff);
    int ua_variable(expr_ref l, expr *u_const);
    bool is_less_than(expr const *a, expr const *b);
    void ua_literal(model_ref model, expr_ref l, expr_ref_vector &phi,
                    expr_expr_map &lb, expr_expr_map &ub,
                    expr_expr_map *sub = nullptr);
    void ua_formula(const expr_ref_vector &conj, model_ref model, expr_expr_map &lb,
                    expr_expr_map &ub, expr_expr_map *sub = nullptr);

    bool is_disjoint(expr_ref_vector group);
    bool is_disjoint(app *g1, app *g2);
    void group(expr_ref_vector conj, expr_ref_vector groups, model_ref model,
               expr_ref_vector &ua_conj);

    bool is_constant(expr const *e) {
        return is_uninterp_const(e) || m_arith.is_numeral(e);
    }

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
    pob *under_approximate(pob &n, model_ref model);
};
} // namespace spacer
