#include "ast/arith_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "muz/spacer/spacer_util.h"

namespace spacer {
class convex_closure {
    ast_manager &m;
    arith_util m_arith;

  public:
    convex_closure(ast_manager &man) : m(man), m_arith(m) {}

    // XXX Replace with an incremental interface suggested below

    // compute the convex closure in one dimension. data is a set of numbers,
    // cnst is the dimension and conj is the convex closure of the form ( cnst
    // mod k = c ) returns false if a convex closure with just one literal
    // cannot be computed.
    bool compute_cls(vector<rational> &data, expr *&cnst, expr_ref &conj);

    /// Incremental interface


    /// \brief Name a dimension
    void set_dimension(unsigned i, expr *v);
    /// \brief Return number of dimensions of each point
    unsigned dims();

    /// \brief add one-dimensional point
    void push_back(rational x);
    /// \brief add two-dimensional point
    void push_back(rational x, rational y);
    /// \brief add three-dimensional point
    void push_back(rational x, rational y, rational z);
    /// \brief add n-dimensional point
    void push_back(vector<rational> &point);

    /// \brief compute convex closure of current set of points
    /// return true if the closure is exact
    bool closure(expr_ref &res);

};
} // namespace spacer
