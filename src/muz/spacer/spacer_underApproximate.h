#include "ast/ast.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "spacer_context.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "util/rational.h"
#include "util/obj_ref_hashtable.h"

typedef obj_ref_map<ast_manager, expr, expr*> expr_expr_map;
namespace spacer {
class under_approx {
    ast_manager &m;
    arith_util m_arith;


    //find the coeff of v in expr t
    //t is to be in SOP or -1*SOP form
    void find_coeff(expr_ref t, expr_ref v, rational &k);
    int under_approx_var(expr_ref lit, expr_ref var);
    void under_approx_lit(model_ref &model, expr_ref lit,
                          expr_expr_map &lb, expr_expr_map &ub,
                          expr_expr_map *sub = nullptr);


    void under_approx_cube(const expr_ref_vector &cube, model_ref &model,
                           expr_expr_map &lb, expr_expr_map &ub,
                           expr_expr_map *sub = nullptr);

    void grp_under_approx_cube(const expr_ref_vector &cube, expr_ref pattern, model_ref &model,
                           expr_ref_vector &ua);


    bool should_grp(expr *pattern, expr *term);

    void grp_terms(expr_ref pattern, expr_ref formula, expr_ref_vector &out, expr_ref_vector &sub_term);
    bool is_constant(expr const *e) {
        return is_uninterp_const(e) || m_arith.is_numeral(e);
    }

    bool normalize_to_le(expr *lit, expr_ref &t, expr_ref &c);
    // each literal in e is Sum Of Products form
    bool is_sop(expr_ref_vector &e) {
        for (expr *a : e) {
            if (!is_sop(a)) return false;
        }
        return true;
    }
    bool is_sop(expr *e);

  public:
    under_approx(ast_manager &manager) : m(manager), m_arith(m) {}
    bool under_approximate(expr_ref n, model_ref &model, expr_ref_vector &u_a, expr_ref pattern);
};
} // namespace spacer
