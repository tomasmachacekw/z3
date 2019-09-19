#include <fstream>
#include <unistd.h>
#include <signal.h>
#include <unistd.h>
#include "util/util.h"
#include "spacer_arith_kernel.h"

namespace spacer {

  /*
    Interface to Sage. Supports initialization and writing to sage. To get
    output from Sage, write to file and read from the file. Could not find
    standard methods to convert file descriptors to streams. Easier to write to
    file and use ifstream
   */
  class Sage {
    FILE* m_out;
    pid_t child_pid;
  public:
    Sage();
    void test();
    ~Sage() {
      kill(child_pid, SIGQUIT);
    }
    FILE*& get_ostream() {
      return m_out;
    }
  };

  /*
    Compute kernel using Sage.
   */
  class Sage_kernel : public arith_kernel {
    Sage m_sage;
    void compute_arith_kernel() override;
  public :
    Sage_kernel(const spacer_matrix& matrix) : arith_kernel(matrix), m_sage() {
      m_sage.test();
    }
    ~Sage_kernel() override { }
  };

}
