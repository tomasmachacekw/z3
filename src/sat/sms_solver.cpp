#include "sat/sms_solver.h"
using namespace sat;

void sms_solver::get_antecedents(literal l, ext_justification_idx idx, literal_vector &r, bool probing) {
  SASSERT(m_pSolver);
  m_pSolver->get_reason(l, r);
}

// m_to_share passes on what is propagated to the PREVIOUS SOLVER
void sms_solver::unit_propagate() {
  if (m_pSolver) {
    m_pSolver->reset_asserted();
    bool r = m_pSolver->propagate();
    if (!r) {
      m_inconsistent = true;
      return;
    }
    unsigned lvl = m_solver->scope_lvl();
    m_tx_idx++;
    literal_vector const& t = m_solver->get_asserted();
    for (literal l : t) {
      m_solver->assign(l, justification::mk_ext_justification(lvl, m_tx_idx));
    }
  }  
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
    m_solver->assign(l, justification::mk_ext_justification(m_solver->lvl(), m_tx_idx));
  case l_true:
    return;
  case l_false:
    SASSERT(false);
  }
}

void sms_solver::push_from_other() {
  m_solver->push();
}

void sms_solver::push() {
  // Synchoronize decision levels between solvers
  if(m_psolver)
    m_pSolver->push_from_other();
}

void sms_solver::pop_from_other(unsigned num_scopes) {
  m_solver->pop(num_scopes);
}
void sms_solver::pop(unsigned num_scopes) {
  if (m_nSolver && m_in_solving_mode && m_scope_lvl - num_scopes > m_full_assignment_lvl) {
    //trigger a conflict in modular solve
    m_return_false = true;
    store m_lemma somewhere.
    backjump to m_full_assignment_lvl
  }
  if (m_pSolver)
    m_pSolver->pop_from_other(num_scopes);
}

void sms_solver::reset_asserted() {
  m_asserted.reset();
}

literal_vector const& get_asserted() {
  return m_asserted;
}

bool sms_solver::propagate() {
  return m_solver->propagate(false);
}
void sms_solver::get_reason(literal l, literal_vector &r) {
  m_solver.get_reason(l, r);
}

lbool sms_solver::resolve_conflict()
