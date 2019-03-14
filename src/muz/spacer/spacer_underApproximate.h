#include "spacer_context.h"
namespace spacer {
  pob* ua_formula(pob& n,model_ref m)
{
  expr * e = n.post();
  for each literal in e :
  if(is_arith(e))
  SASSERT(is_app(e) && is_le(e))
  return &n;
}
}
