#include "spacer_convex_closure.h"
namespace {
//rational a < rational b
struct lt_rational {
  bool operator()(rational const& a, rational const& b) const { return a < b; }
};
} // anonymous namespace

namespace spacer {
bool convex_closure::compute_cls(vector<rational>& data, expr*& cnst, expr_ref& cls)
{
  //TODO handle duplicates in data
  //TODO use solver in z3
  lt_rational lt;
  std::sort(data.begin(), data.end(), lt);
  rational cd = data[1] - data[0];
  for(unsigned i = 1; i < data.size() - 1; ++i)
    {
      if (cd != data[i + 1] - data[i])
        return false;
    }
  //progression is (forall i cd*i + offset) where offset is d%cd for any d
  app* cd_expr = m_arith.mk_numeral(cd, true);
  app* d_expr = m_arith.mk_numeral(data.get(0), true);
  app* lhs = m_arith.mk_mod(cnst, cd_expr);
  app* rhs = m_arith.mk_mod(d_expr, cd_expr);
  cls = expr_ref(m.mk_eq(lhs, rhs), m);
  return true;
};
} // spacer namespace
