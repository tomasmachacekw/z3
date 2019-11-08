#pragma once
#include "muz/spacer/spacer_context.h"
namespace spacer {
class lemma_cluster_finder {
    struct stats {
        unsigned max_group_size;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            max_group_size = 0;
            watch.reset();
        }
    };
    ast_manager &m;
    arith_util m_arith;
    typedef std::pair<unsigned, unsigned> var_offset;
    bool are_neighbours(expr_ref antiU_result, substitution &s1,
                        substitution &s2);

    bool are_neighbours(const expr_ref &cube, const expr_ref &lcube,
                        expr_ref &pat, substitution &sub1, substitution &sub2);
    stats m_st;

  public:
    lemma_cluster_finder(ast_manager& m);
    void cluster(lemma_ref &lemma);
    void collect_statistics(statistics &st) const;
    void reset_statistics() { m_st.reset(); }
};
}
