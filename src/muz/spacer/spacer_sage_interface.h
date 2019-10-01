#pragma once
#include "spacer_arith_kernel.h"
#include "util/util.h"
#include <fstream>
#include <signal.h>
#include <unistd.h>

namespace spacer {

/*
  Interface to Sage. Supports initialization and writing to sage. To get
  output from Sage, write to file and read from the file. Could not find
  standard methods to convert file descriptors to streams. Easier to write to
  file and use ifstream
 */
class Sage {
    FILE *m_out;
    FILE *m_in;
    std::string tmp_name;
    pid_t child_pid;

  public:
    Sage();
    bool test();
    ~Sage() { kill(child_pid, SIGQUIT); }
    FILE *get_ostream() const { return m_out; }
    FILE *get_istream() const { return m_in; }
};

/*
  Compute kernel using Sage.
 */
class Sage_kernel : public arith_kernel {
    Sage m_sage;
    bool compute_arith_kernel() override;
    std::string print_matrix() const;
    std::string print_kernel() const;

  public:
    Sage_kernel(unsigned n_rows, unsigned n_cols)
        : arith_kernel(n_rows, n_cols), m_sage() {}
    ~Sage_kernel() override {}
};

} // namespace spacer
