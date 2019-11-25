#include "muz/spacer/spacer_convex_closure.h"

namespace spacer {
void convex_closure::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.merge.cvx_cls",
              m_st.watch.get_seconds());
    st.update("SPACER sage calls", m_kernel->get_sage_calls());
}

} // namespace spacer
