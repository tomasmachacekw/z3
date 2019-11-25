#pragma once
#include "ast/arith_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_util.h"
#include "muz/spacer/spacer_arith_kernel.h"
#include "muz/spacer/spacer_matrix.h"
#include "muz/spacer/spacer_sage_interface.h"
#include "muz/spacer/spacer_util.h"
#include "util/statistics.h"
namespace spacer {
class convex_closure {
    ast_manager &m;
    arith_util m_arith;
    unsigned m_dim;
    bool m_use_sage;
    spacer_matrix m_data;
    bool is_int_points() const;
    expr_ref_vector m_dim_vars;
    arith_kernel *m_kernel;
    unsigned reduce_dim();
    void rewrite_lin_deps();
    void add_lin_deps(expr_ref_vector& res_vec);
    var_ref_vector m_nw_vars;
    struct stats {
        stopwatch watch;
        stats() { reset(); }
        void reset() { watch.reset(); }
    };
    void mul_if_not_one(rational coeff, expr *e, expr_ref &res);
    stats m_st;

    //compute one dimensional convex closure
    void do_one_dim_cls(expr_ref var, expr_ref_vector& res);
  public:
    convex_closure(ast_manager &man, bool use_sage)
        : m(man), m_arith(m), m_dim(0), m_use_sage(use_sage), m_data(0, 0),
          m_dim_vars(m), m_nw_vars(m) {
        if (m_use_sage) m_kernel = new Sage_kernel(m_data);
    }
    ~convex_closure() {
        if (m_use_sage) delete m_kernel;
    }
    void reset(unsigned n_cols) {
        m_kernel->reset();
        m_data.reset(n_cols);
        m_dim_vars.reset();
        m_dim = n_cols;
        m_dim_vars.reserve(m_dim);
        m_nw_vars.reset();
    }
    /// Incremental interface

    /// \brief Name a dimension
    void set_dimension(unsigned i, expr *v) {
        SASSERT(i < dims());
        SASSERT(m_dim_vars[i] == nullptr);
        m_dim_vars[i] = v;
    }
    /// \brief Return number of dimensions of each point
    unsigned dims() const { return m_dim; }

    const var_ref_vector &get_nw_vars() const { return m_nw_vars; }
    /// \brief add one-dimensional point
    void push_back(rational x) {
        SASSERT(dims() == 1);
        vector<rational> row;
        row.push_back(x);
        m_data.add_row(row);
    }

    /// \brief add two-dimensional point
    void push_back(rational x, rational y) {
        SASSERT(dims() == 2);
        vector<rational> row;
        row.push_back(x);
        row.push_back(y);
        m_data.add_row(row);
    }

    /// \brief add n-dimensional point
    void push_back(vector<rational> &point) {
        SASSERT(point.size() == dims());
        m_data.add_row(point);
    };

    /// \brief compute convex closure of current set of points
    /// return true if it was possible to compute the closure
    bool closure(expr_ref_vector &res);
    void collect_statistics(statistics &st) const;
    void reset_statistics() { m_st.reset(); }
};
} // namespace spacer
