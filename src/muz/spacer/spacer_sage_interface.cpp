#include <istream>
#include <sstream>
#include <stdio.h>
#include "spacer_sage_interface.h"
namespace spacer {
   Sage::Sage() {
    int to_sage_pipe[2];
    int from_sage_pipe[2];
    int ok = pipe(to_sage_pipe);
    if (ok) {
      perror("sage pipe1");
      exit(1);
    }
    ok = pipe(from_sage_pipe);
    if (ok) {
      perror("sage pipe2");
      exit(1);
    }

    pid_t pid = fork();
    if (pid) {
      m_out = fdopen(to_sage_pipe[1], "w");
      m_in = fdopen(from_sage_pipe[0], "r");

      /* parent */
      close(to_sage_pipe[0]);
      close(from_sage_pipe[1]);

      child_pid = pid;
      if(!test()) {
        TRACE ("sage-interface", tout << "Sage test failed \n";);
      }
    } else if (pid == 0) {
      /* child */

      //setup file descriptor
      close(to_sage_pipe[1]);
      close(from_sage_pipe[0]);
      dup2(to_sage_pipe[0], STDIN_FILENO);
      dup2(from_sage_pipe[1], STDOUT_FILENO);
      //setup arguments
      char* const argv[3] = {
                             (char*)"sage",
                             NULL,
                             NULL
      };
      //TODO: sage complains that it can't find $HOME. But sage works without it.
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

  bool Sage::test() {
    char temp_name[] = "/var/tmp/spacersage.XXXXXX";
    int tmp_fd = mkstemp(temp_name);
    if (tmp_fd == -1) {
      //Error: failed to create temp file
      TRACE("sage-interface", tout << "failed to create temp file\n";);
      return false;
    }
    TRACE ("sage-interface", tout << "writing test output to " << temp_name << "\n";);
    fprintf(m_out , "f = open (\"\%s\", 'w')\n", temp_name);
    //Do stuff
    fprintf(m_out, "print >>f, 2 + 2\n");
    fprintf(m_out, "f.close()\n");
    fflush(m_out);
    //indicate that sage is done by printing to pipe
    fprintf(m_out, "print \"\\nok\\n\"\n");
    fprintf(m_out, "sys.stdout.flush()\n");
    fflush(m_out);

    //first wait for sage to write ok
    char *std_ok = nullptr;
    size_t n = 0;
    ssize_t t = 0;
    //read all the lines printed by sage until we get okay
    //will block if Sage not found :(
    do {
      t = getline(&std_ok, &n, m_in);
      if (t == -1 || feof(m_in) || ferror(m_in)) {
        TRACE("sage-interface", tout << "error while reading from sage pipe \n";);
        return false;
      }
      CTRACE("sage-interface-verb", t > 0, tout << "got sage std output " << std_ok << "\n";);
    }while (strcmp(std_ok, "ok\n") != 0);
    //delete object allocated by getline
    delete std_ok;
    TRACE ("sage-interface", tout << "got ok from sage \n";);

    //read output from file
    std::ifstream ifs(temp_name);
    int ok = -1;
    if ( !ifs.is_open() ) {
      TRACE ("sage-interface", tout << "failed to open file\n";);
      return false;
    }

    ifs >> ok;

    if(ifs.bad()) {
      TRACE("sage-interface", tout << "error when reading from file\n";);
      ifs.close();
      return false;
    }

    TRACE ("sage-interface", tout << "got sage output " << ok << "\n";);
    ifs.close();
    return ok == 4;
  }

  void Sage_kernel::compute_arith_kernel()  {
    char temp_name[] = "/tmp/spacersage.XXXXXX";
    int tmp_fd = mkstemp(temp_name);
    if(tmp_fd == -1){
      //Error: failed to create temp file
      perror("temp file create");
      exit(1);
    }
    TRACE ("sage-interface", tout << temp_name << "\n";);
    unsigned m = m_matrix.num_cols();
    unsigned n = m_matrix.num_rows();
    auto& out = m_sage.get_ostream();
    fprintf(out, "f = open (\"\%s\", 'w')\n", temp_name);

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
    std::ifstream ifs(temp_name, std::ifstream::in);
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
