#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/ast.h"
#include "muz/spacer/spacer_util.h"

namespace spacer{
class convex_closure{
  ast_manager& m;
  arith_util m_arith;
 public:
 convex_closure(ast_manager& man) : m(man), m_arith(m) {}
  // compute the convex closure in one dimension. data is a set of numbers, cnst
  // is the dimension and conj is the convex closure of the form ( cnst mod k = c )
  // returns false if a convex closure with just one literal cannot be computed.
 bool compute_cls(vector<rational>& data, expr*& cnst, expr_ref& conj);
};
}
