#include "spacer_matrix.h"
namespace spacer {

  /*
    Interface to compute arith_kernel. Stores a const reference to the input
    matrix, and the computed kernel.
   */
  class arith_kernel {

  protected:
    const spacer_matrix& m_matrix;
    spacer_matrix m_kernel;
    virtual void compute_arith_kernel() {};

  public:
    //The maximum number of rows in the kernel is (matrix.rows - 1)
    arith_kernel(const spacer_matrix& matrix) : m_matrix(matrix),
      m_kernel(spacer_matrix(m_matrix.num_rows(), m_matrix.num_cols())){
    }
    bool compute_kernel() {
      compute_arith_kernel();
      return m_kernel.num_rows();
    }
    virtual ~arith_kernel() {};
  };

}
