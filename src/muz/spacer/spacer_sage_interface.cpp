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
      sleep(3);
      //read and discard the startup text in sage.
      char t_h[256];
      fgets(t_h, 256, m_in);

    } else if (pid == 0) {
      /* child */

      //setup file descriptors
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
      char* const env[1] = {
                            (char*)"HOME=/Users/hgvk"
      };
      execve("/Users/hgvk/Downloads/UWaterloo/code/sage/sage-8.8/sage", argv, env);
      perror("execvpe for sage");
    } else {
      perror("fork");
      exit(1);
    }
  }

  void Sage::test() {
    char t_h[256];
    fprintf(m_out, "2 + 2\n");
    fflush(m_out);
    fgets(t_h, 256, m_in);
    IF_VERBOSE(1, verbose_stream() << "output from sage " << t_h << "\n");
  }

}
