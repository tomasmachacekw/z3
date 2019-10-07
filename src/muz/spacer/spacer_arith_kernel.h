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
    bool compute_kernel() { return compute_arith_kernel(); }
    void reset() { m_kernel = spacer_matrix(0, 0); }
    const spacer_matrix &get_kernel() const { return m_kernel; }
    virtual ~arith_kernel(){};
};

} // namespace spacer
#endif
