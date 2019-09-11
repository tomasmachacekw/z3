#include <fstream>
#include <unistd.h>
#include <signal.h>
#include "util/util.h"

namespace spacer {
  class Sage {
    FILE* m_out;
    FILE* m_in;
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
    FILE*& get_istream() {
      return m_in;
    }
  };
}
