#include "sat/sms_solver.h"
#include "ast/ast_pp.h"
#include "util/sat_literal.h"

using namespace sat;

void sms_solver::learn_clause_and_update_justification(literal l, literal_vector const& antecedent) {
  literal_vector cls;
  cls.push_back(l);
  for(literal l : r) cls.push_back(l);
  clause* c = m_solver->mk_clause(cls.size(), cls.data(), sat::status::redundant());
  justification js = m_solver->get_justification(l);
  justification njs(js.level());
  switch(cls.size()) {
  case 2:
    njs = justification(njs.level(), ~cls[1]);
    break;
  case 3:
    njs = justification(njs.level(), ~cls[1], ~cls[2]);
    break;
  default:
    njs = justification(njs.level(), m_solver->get_offset(*c));
    break;
  }
  m_solver->update_assign_uncond(l, njs);
  m_itp.push_back(cls);
}
void sms_solver::get_antecedents(literal l, ext_justification_idx idx, literal_vector &r, bool probing) {
  if (idx == NSOLVER_EXT_IDX) {
    // Literal was asserted by nSolver
    SASSERT(get_mode() == SOLVE);
    SASSERT(m_nSolver);
    m_nSolver->get_reason(l, r);   
  }
  else {
    SASSERT(m_pSolver);
    if(!m_pSolver->get_reason(l, r)) {
      SASSERT(get_mode() = VALIDATE);
      m_validation_failed = true;
      m_validate_failed_lit = l;
      return;
    }
  }
  // when probing is true, sat solver is not doing conflict resolution
  if (probing) return;
  learn_clause_and_update_justification(l, r);
}

void sms_solver::init_search() { unit_propagate(); }

void sms_solver::get_reason_final(literal_vector& lc) { m_solver->resolve_conflict_for_ext_core(lc, NSOLVER_EXT_IDX); }

bool sms_solver::unit_propagate() {
  if (m_pSolver) {
    m_pSolver->reset_asserted();
    bool r = m_pSolver->propagate();
    if (!r) {
      m_pSolver_clause.reset();
      m_pSolver->get_reason_final(m_pSolver_clause);
      m_itp.push_back(m_ext_clause);
      set_conflict();      
      return false;
    }
    literal_vector const& t = m_pSolver->get_asserted();
    for (literal l : t) {
      assign_from_other(l, PSOLVER_EXT_IDX);
    }
  }
  if (get_mode() == LOOKAHEAD && m_nSolver) {
    m_nSolver->reset_asserted();
    bool r = m_nSolver->propagate();
    if (!r) {
      m_nSolver_clause.reset();
      m_nSolver->get_reason_final(m_ext_clause);
      set_conflict();      
      return false;
    }
    literal_vector const& t = m_nSolver->get_asserted();
    for (literal l : t) {
      assign_from_other(l, NSOLVER_EXT_IDX);
    }
  }
  return true;
}

bool sms_solver::decide(bool_var& next, lbool& phase) {
  SASSERT(get_mode() != PROPAGATE);
  if (!m_pSolver || get_mode() != SOLVE) return false;
  if (!switch_to_lam()) return false;
  m_pSolver->set_mode(LOOKAHEAD);  
  set_mode(PROPAGATE);
  m_pSolver->set_core(m_ext_clause);
  bool r = m_pSolver->modular_solve();
  m_pSolver->set_mode(PROPAGATE);
  if (r) {
    // continue making decisions
    set_mode(VALIDATE);
    m_validation_failed = false;
    //TODO: change decision variable if it has already been assigned
    return true;
  }
  // m_pSolver decided for you
  set_mode(SOLVE);
  dbg_print_lv("look ahead returned unsat with", m_ext_clause);
  set_conflict();
  // reverse decision level change
  pop(1);
  // add dummy decision variable
  next = null_bool_var;
  phase = l_true;
  return true;
}

void sms_solver::set_conflict() {
  dbg_print_lv("learning lemma", m_ext_clause);
  literal not_l = null_literal;
  unsigned lvl = 0;
  unsigned hl = 0;
  for(unsigned i = 0; i < m_ext_clause.size(); i++) {
    if (lvl < m_solver->lvl(m_ext_clause[i])) {
      hl = i;
      lvl = m_solver->lvl(m_ext_clause[i]);
    }
  }
  justification js(lvl);
  std::swap(m_ext_clause[0], m_ext_clause[hl]);
  clause* c = m_solver->mk_clause(m_ext_clause.size(), m_ext_clause.data(), sat::status::redundant());
  switch (m_ext_clause.size()) {
  case 0:
    SASSERT(false);
    break;
  case 1:
    js = justification(lvl, m_ext_clause[0]);
    break;
  case 2:
    js = justification(lvl, m_ext_clause[0], m_ext_clause[1]);
    break;
  default:    
    clause_offset co = m_solver->get_offset(*c);
    not_l = m_ext_clause[0];
    js = justification(lvl, co);
    break;
  }
  //force conflict
  m_solver->set_conflict(js, not_l);  
}

void sms_solver::asserted(literal l) {
  dbg_print_lit("asserted lit", l);
  m_solver->display_justification(tout, m_solver->get_justification(l));
  if(m_shared[l.var()]) {
    m_asserted.push_back(l);
    if (m_pSolver)
      m_pSolver->assign_from_other(l, NSOLVER_EXT_IDX);
  }
}

void sms_solver::assign_from_other(literal l, ext_justification_idx idx) {
  justification js = justification::mk_ext_justification(m_solver->scope_lvl(), idx);
  switch(m_solver->value(l)) {
  case l_undef:
    dbg_print_lit("assigning from other", l);
    m_solver->assign(l, js);
    if (m_solver->scope_lvl() == 0)
      m_solver->update_assign_uncond(l, js);
    break;
  case l_true:
    dbg_print_lit("already assigned true", l);
    return;
  case l_false:
    SASSERT(false);
  }
}

void sms_solver::get_reason(literal l, literal_vector & rc) {  
  literal_vector todo;
  literal  t = l;
  todo.push_back(t);
  rc.reset();
  while(!todo.empty()) {
    t = todo.back();
    todo.pop_back();
    dbg_print_lit("Fetching reason for", t);
    justification js = m_solver->get_justification(t);
    TRACE("satmodsat", m_solver->display_justification(tout, js););
    switch(js.get_kind()) {
    case justification::NONE:
      SASSERT(m_finished_lookahead);
      rc.reset();
      return false;
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
  return true;
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

void sms_solver::pop(unsigned num_scopes) {
  dbg_print_stat("popping", num_scopes);
  if(m_solver->scope_lvl() - num_scopes < m_full_assignment_lvl) {
    m_core->reset();
    m_solver->resolve_conflict_for_ext_core(*m_core, NSOLVER_EXT_IDX);
  }
  if (m_pSolver)
    m_pSolver->pop_from_other(num_scopes);
}

bool sms_solver::propagate() { return m_solver->propagate(false); }

check_result sms_solver::check() {
  if (!m_pSolver || get_mode() == VALIDATE) return check_result::CR_DONE;
  SASSERT(get_mode() == SOLVE);
  SASSERT(m_pSolver->get_mode() == PROPAGATE);
  m_pSolver->set_mode(SOLVE);
  dbg_print("got a sat assignment, checking with psolver");
  m_pSolver->set_core(m_ext_clause);
  if (m_pSolver->modular_solve())
    return check_result::CR_DONE;
  dbg_print_lv("modular solve returned unsat with", m_ext_clause);
  set_conflict();
  return check_result::CR_CONTINUE;
}

bool sms_solver::switch_to_lam() {
  return true;
}

bool sms_solver::modular_solve() {
  m_solving_mode = true;
  m_full_assignment_lvl = m_solver->scope_lvl();
  dbg_print_stat("reached modular solve with", m_full_assignment_lvl);
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
