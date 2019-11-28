#include "ast/ast.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "spacer_context.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "util/obj_ref_hashtable.h"
#include "util/rational.h"

typedef obj_ref_map<ast_manager, expr, expr *> expr_expr_map;
namespace spacer {
class under_approx {
    ast_manager &m;
    arith_util m_arith;
    bool is_constant(expr const *e) {
        return is_uninterp_const(e) || m_arith.is_numeral(e);
    }

    // convert an arith expression lit into t <= c
    bool normalize_to_le(expr *lit, expr_ref &t, expr_ref &c);

    // check Sum Of Products form
    bool is_sop(expr_ref_vector &e) {
        for (expr *a : e) {
            if (!is_sop(a)) return false;
        }
        return true;
    }
    bool is_sop(expr *e);
};
} // namespace spacer
