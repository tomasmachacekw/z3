#include "sat/sms_solver.h"
#include "ast/ast_pp.h"
#include "util/sat_literal.h"

using namespace sat;

void sms_solver::get_antecedents(literal l, ext_justification_idx idx, literal_vector &r, bool probing) {
  SASSERT(m_pSolver);
  m_pSolver->get_reason(l, r);
  m_solver->add_clause(r.size(), r.data(), sat::status::redundant());
  m_itp.push_back(r);
}

void sms_solver::learn_lemma(literal_vector const& c) {
  unsigned dl = 0;
  literal l;
  unsigned hl = 0;
  literal_vector cc;  
  for (unsigned i = 0; i < c.size(); i++) {
    l = c[i];
    if (m_solver->lvl(l) > dl) {
      hl = i;
      dl = m_solver->lvl(l);
    }
    cc.push_back(l);
  }
  std::swap(cc[hl], cc[0]);
  m_solver->set_m_lemma(cc);
}

bool sms_solver::unit_propagate() {
  if (m_pSolver) {
    m_pSolver->reset_asserted();
    bool r = m_pSolver->propagate();
    if (!r) {
      literal_vector lc;
      m_pSolver->get_reason_final(lc);
      learn_lemma(lc);
      m_solver->learn_lemma_and_backjump();      
      return false;
    }
    unsigned lvl = m_solver->scope_lvl();
    m_tx_idx++;
    literal_vector const& t = m_pSolver->get_asserted();
    for (literal l : t) {
      m_solver->assign(l, justification::mk_ext_justification(lvl, m_tx_idx));
    }
  }
  return true;
}


void sms_solver::asserted(literal l) {
  if(m_shared[l.var()]) {
    m_asserted.push_back(l);
    if (m_pSolver)
      m_pSolver->assign_from_other(l);
  }
}

void sms_solver::assign_from_other(literal l) {
  switch(m_solver->value(l)) {
  case l_undef:    
    m_solver->assign(l, justification::mk_ext_justification(m_solver->scope_lvl(), m_tx_idx));
  case l_true:
    return;
  case l_false:
    SASSERT(false);
  }
}

void sms_solver::get_reason_final(literal_vector & rc) {
  SASSERT(m_solver->inconsistent());
  get_reason(m_solver->get_m_not_l(), rc);
}

void sms_solver::get_reason(literal l, literal_vector & rc) {  
  dbg_print_lit("Fetching reason for", l);
  literal_vector todo;
  todo.push_back(l);
  rc.reset();
  while(!todo.empty()) {
    literal t = todo.back();
    todo.pop_back();
    justification js = m_solver->get_justification(t);
    //    TRACE("satmodsat", display_justification(tout, js););
    switch(js.get_kind()) {
    case justification::NONE:
      SASSERT(false);
      break;
    case justification::BINARY:
      todo.push_back(~js.get_literal());
      break;
    case justification::TERNARY:
      todo.push_back(~js.get_literal1());
      todo.push_back(~js.get_literal2());
      break;
    case justification::CLAUSE: {
      clause & c = m_solver->get_clause(js);
      unsigned i   = 0;
      if (c[0].var() == t.var()) {
	i = 1;
      }
      else {
	SASSERT(c[1].var() == t.var());
	todo.push_back(~c[0]);
	i = 2;
      }
      unsigned sz = c.size();
      for (; i < sz; i++) {
	todo.push_back(~c[i]);
      }
      break;
    }
    case justification::EXT_JUSTIFICATION: {
      rc.push_back(~t);
      break;
    }
    default:
      UNREACHABLE();
      break;
    }
  }
}

void sms_solver::push_from_other() {
  m_solver->push();
}

void sms_solver::push() {
  // Synchoronize decision levels between solvers
  if(m_pSolver)
    m_pSolver->push_from_other();
}

void sms_solver::pop_from_other(unsigned num_scopes) {
  m_solver->pop(num_scopes);
}

void sms_solver::resolve_conflict_final(literal_vector &c) {
  literal_vector ac;
  for(literal l: m_solver->get_m_lemma()) {
    ac.reset();
    get_reason(l, ac);
    c.append(ac);
  }  
}

void sms_solver::pop(unsigned num_scopes) {
  if(m_solver->scope_lvl() - num_scopes < m_full_assignment_lvl) {
    m_core.reset();
    resolve_conflict_final(m_core);
  }
  if (m_pSolver)
    m_pSolver->pop_from_other(num_scopes);
}

bool sms_solver::propagate() { return m_solver->propagate(false); }

check_result sms_solver::check() {
  if (!m_pSolver) return check_result::CR_DONE;
  if (m_pSolver->modular_solve())
    return check_result::CR_DONE;
  literal_vector const& c = m_pSolver->get_core();
  unsigned mdl = 0;
  unsigned sdl = 0;
  for(literal l : c) {
    if (m_solver->lvl(l) > mdl) {
      sdl = mdl;
      mdl = m_solver->lvl(l);
    }
  }
  m_solver->add_clause(c.size(), c.data(), status::redundant());
  m_itp.push_back(c);
  m_solver->pop_reinit(sdl);
  return check_result::CR_CONTINUE;
}

bool sms_solver::modular_solve() {
  m_full_assignment_lvl = m_solver->scope_lvl();
  bool r = m_solver->search_above(m_full_assignment_lvl);
  if (!r && m_full_assignment_lvl > 0) {
    SASSERT(m_solver->scope_lvl() < m_full_assignment_lvl);
    for (unsigned i = m_solver->scope_lvl(); i < m_full_assignment_lvl; i++)
      push();
  }
  return r;
}


/*
 Functions to add clauses to solvers
 TODO: replace with standard way of doing it e.g. in euf_solver.h
 */
void sms_solver::add_clause_expr(expr* fml) {
  expr* n;
  SASSERT(m.is_or(fml) || (m.is_bool(fml) && (is_uninterp_const(fml) || (m.is_not(fml, n) && is_uninterp_const(n)))));
  ptr_vector<expr> args;
  if (!m.is_or(fml)) {
    args.push_back(fml);
  }
  else
    for(expr* e: *to_app(fml))
      args.push_back(e);
  literal_vector c;
  bool t;
  bool_var v;
  literal l;
  for(expr* e: args) {
    SASSERT(m.is_bool(e));
    n = e;
    t = m.is_not(e, n);
    SASSERT(is_uninterp_const(n));
    v = boolVar(n);
    l = literal(v, t);
    c.push_back(l);
  }
  m_solver->add_clause(c.size(), c.data(), sat::status::input());
}

void satmodsatcontext::addA(expr_ref fml) {
  add_cnf_expr_to_solver(m_solverA, fml);
}

void satmodsatcontext::addB(expr_ref fml) {
  add_cnf_expr_to_solver(m_solverB, fml);
}

void satmodsatcontext::add_cnf_expr_to_solver(extension* s, expr_ref fml) {
  sms_solver* a = static_cast<sms_solver*>(s);
  SASSERT(m.is_and(fml));
  for(expr* e: *to_app(fml)) {
    a->add_clause_expr(e);
  }
}

void sat_mod_sat::solve(expr_ref A, expr_ref B, expr_ref_vector& shared) {
  TRACE("satmodsat", tout << "A: " << mk_pp(A, m) << " B: " << mk_pp(B, m) << "\n";);
  init(A, B, shared);
  bool res = m_solver.solve();
  const char* s = res? "satisfiable" : "unsatisfiable";
  TRACE("satmodsat", tout << "final result is " << s;);
}

// Ensures that all shared variables have the same index in both solvers.
// That is variable 1 in Solver_A is the same as variable 1 in solver_B
// This is required to reduce the amount of bookkeeping when exchanging lits and clauses between solvers
void sat_mod_sat::init(expr_ref A, expr_ref B, expr_ref_vector const & shared) {
  m_a = A;
  m_b = B;
  m_shared = expr_ref_vector(shared);
  m_solver.addShared(shared);
  m_solver.addA(m_a);
  m_solver.addB(m_b);
}
