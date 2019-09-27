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
    virtual bool compute_arith_kernel() { return false; };

  public:
    //No default constructor for spacer_matrix. Dummy initialization
    arith_kernel(const spacer_matrix& matrix) : m_matrix(matrix), m_kernel(0, 0){}
    bool compute_kernel() {
      return compute_arith_kernel();
    }
    const spacer_matrix& get_kernel() const { return m_kernel;}
    virtual ~arith_kernel() {};
  };

}
