#ifndef SPACER_ARITH_KERNEL_H_
#define SPACER_ARITH_KERNEL_H_

#include "spacer_matrix.h"
namespace spacer {

/*
  Interface to compute arith_kernel. Computes kernel of m_matrix
 */
class arith_kernel {

  protected:
    const spacer_matrix &m_matrix;
    spacer_matrix m_kernel;
    virtual bool compute_arith_kernel() { return false; };

  public:
    // No default constructor for spacer_matrix. Dummy initialization
    arith_kernel(spacer_matrix &matrix) : m_matrix(matrix), m_kernel(0, 0) {}
    bool compute_kernel() {
        SASSERT(m_matrix.num_rows() > 1);
        if(m_matrix.compute_linear_deps(m_kernel)) {
            //cannot be reduced further
            if(m_matrix.num_cols() - m_kernel.num_rows() <= 1)
            return true;
            //use sage to find ALL linear deps
            m_kernel.reset(m_kernel.num_cols());
            SASSERT(m_matrix.num_cols() > 2);
        }
        TRACE("cvx_dbg_verb", tout << "Calling sage \n";);
        return (m_matrix.num_cols() > 2) && compute_arith_kernel(); }
    void reset() { m_kernel = spacer_matrix(0, 0); }
    const spacer_matrix &get_kernel() const { return m_kernel; }
    virtual ~arith_kernel(){};
};

} // namespace spacer
#endif
