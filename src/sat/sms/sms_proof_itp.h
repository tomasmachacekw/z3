#pragma once
#include "ast/ast_util.h"
#include "sat/sms/sms_solver.h"
#include "util/sat_literal.h"
#include "util/vector.h"
namespace sat {
  typedef std::tuple<sat::status, literal_vector> pf_clause;
  class sms_proof_itp {
    ast_manager& m;
    sat_mod_sat *m_solver;

    bool_var boolVar(expr *n) {
      return m_solver->get_var(n);
    }

    expr *get_expr(bool_var v) {
      return m_solver->get_expr(v);
    }

    expr_ref get_expr(literal l) {
      expr* e = m_solver->get_expr(l.var());
      SASSERT(e);
      expr_ref ne(m);
      ne = l.sign() ? m.mk_not(e) : e;
      return ne;
    }

    bool is_shared(bool_var v) {
      return m_solver->is_shared(v);
    }
    vector<pf_clause> m_trail;
    void mk_tail(vector<literal_vector> const& lcc, expr_ref& out);
    void mk_clause(literal_vector const& clause, expr_ref& out);
    void add_itp_imp(vector<literal_vector> const& tail, literal_vector const& head, expr_ref_vector& itp);

 public:
      sms_proof_itp(ast_manager& man, sat_mod_sat *s): m(man), m_solver(s) { m_solver->set_itp(this); }
      void interpolate();
      void log_clause(status s, unsigned sz, literal const *c);
};
}
