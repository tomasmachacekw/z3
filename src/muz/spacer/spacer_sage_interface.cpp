#include <istream>
#include <sstream>
#include "spacer_sage_interface.h"
namespace spacer {
   Sage::Sage() {
    int to_sage_pipe[2];
    int ok = pipe(to_sage_pipe);
    if (ok) {
      perror("sage pipe");
      exit(1);
    }

    pid_t pid = fork();
    if (pid) {
      m_out = fdopen(to_sage_pipe[1], "w");

      /* parent */
      close(to_sage_pipe[0]);

      child_pid = pid;
      //TODO: replace with something else
      sleep(3);

    } else if (pid == 0) {
      /* child */

      //setup file descriptor
      close(to_sage_pipe[1]);
      close(STDOUT_FILENO);
      dup2(to_sage_pipe[0], STDIN_FILENO);

      //setup arguments
      char* const argv[3] = {
                             (char*)"sage",
                             NULL,
                             NULL
      };
      //TODO: replace this with /proc/self
      // char* const env[1] = {
      //                       (char*)"HOME=/Users/hgvk"
      // };
      execvp("sage", argv);
      perror("execvpe for sage");
    } else {
      perror("fork");
      exit(1);
    }
  }

  void Sage::test() {
    fprintf(m_out, "f = open (\"\%s\", 'w')\n", get_tmp_filename().c_str());
    fprintf(m_out, "print >>f, 2 + 2\n");
    fprintf(m_out, "print >>f, \"ok\"\n");
    fprintf(m_out, "f.close()\n");
    fflush(m_out);
    //read output
    std::ifstream ifs(get_tmp_filename(), std::ifstream::in);
    std::string ok;
    while(!ifs.eof()) {
      std::getline(ifs, ok);
      TRACE ("sage-interface", tout << "reading from sage " << ok << "\n";);
      if(ok.compare(0, 2, "ok")) {
        TRACE ("sage-interface", tout << "got sage output\n";);
        break;
      }
    }
  }

  void Sage_kernel::compute_arith_kernel()  {
    unsigned m = m_matrix.num_cols();
    unsigned n = m_matrix.num_rows();
    auto& out = m_sage.get_ostream();
    fprintf(out, "f = open (\"\%s\", 'w')\n", m_sage.get_tmp_filename().c_str());

    //construct  matrix in sage
    std::stringstream t;
    t << " a = matrix(ZZ,";
    t << std::to_string(m);
    t << (", ");
    t << (std::to_string(n + 1));
    t << (", [");
    for(unsigned i = 0; i < m; i++)
      {
        t << ("[");
        for(unsigned j = 0; j < n; j++)
          {
            // t. << (std::to_string(m_matrix.get(i,j)));
            t << (", ");
          }
        t << ("1");
        t << ("], ");
      }
    t << ("]);\n");
    fprintf(out, "%s", t.str().c_str());
    fprintf(out, "b = a.transpose();\n");
    fprintf(out, "c = b.right_kernel().basis();\n");
    fprintf(out, "print >> f, c\n");
    fprintf(out, "print >> f, \"ok\"\n");
    fprintf(out, "f.close()\n");
    fflush(out);

    //read output
    std::ifstream ifs(m_sage.get_tmp_filename(), std::ifstream::in);
    std::string ok;
    while(!ifs.eof()) {
      std::getline(ifs, ok);
      //TODO read integers instead of characters...
      TRACE ("sage-interface", tout << "reading from sage " << ok << "\n";);
      if(ok.compare(0, 2, "ok")) {
        TRACE ("sage-interface", tout << "got sage output\n";);
        break;
      }
    }
  }
}
