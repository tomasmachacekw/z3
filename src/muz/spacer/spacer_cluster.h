
#include "util/chashtable.h"

namespace spacer {
  class lem_cluster{
  protected:
    struct hash_proc {
      unsigned operator()(expr const & e){ return e.hash(); }
    };
    struct eq_proc {
      bool operator()(expr *e1, expr *e2){ return e1 == e2; }
    };

    typedef chashtable<expr, hash_proc, eq_proc> set;

    ast_manager &m;
    expr_ref m_pattern;
    set m_lemmaSet;

  public:
    lem_cluster();
    ~lem_cluster();

    bool contains(expr &lemma);

    void insert(expr &lemma);
    bool insert_if_not_there(expr &lemma);

    // not sure if we want to expose m_lemmaSet
    const set get_lemmas() { return m_lemmaSet; }

    void reset();
  };
}
