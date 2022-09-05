#include "sat/sat_mod_sat.h"
#include "ast/ast_pp.h"
#include "util/sat_literal.h"

using namespace sat;
void sat_mod_sat::solve(expr_ref A, expr_ref B, expr_ref_vector& shared) {
  TRACE("satmodsat", tout << "A: " << mk_pp(A, m) << " B: " << mk_pp(B, m) << "\n";);
  init(A, B, shared);
  m_solver.solve();
  return;
}

// Ensures that all shared variables have the same index in both solvers.
// That is variable 1 in Solver_A is the same as variable 1 in solver_B
// This is required to reduce the amount of bookkeeping when exchanging lits and clauses between solvers
void sat_mod_sat::init(expr_ref A, expr_ref B, expr_ref_vector& shared) {
  m_a = A;
  m_b = B;
  m_shared = expr_ref_vector(shared);
  m_solver.reset();
  m_solver.addShared(shared);
  m_solver.addA(m_a);
  m_solver.addB(m_b);
}


bool satmodsatcontext::solve() {
  while(true) {
  bool c = propagateALL();
  // if (!c) {
  //   resolvecc();
  //   learn_lemma_and_backtrack();
  //   if m_solverB.decisionLevel() == 0
  // 		  return unsat;
  // }
  // if B has decisions to take {
  //     solverB->decide();
  //     continue
  //   }
  // A.solve();  
  // TRACE("satmodsat", tout << "sat";);
  // return true;
  }
}

bool smssolver::propagateAndShare(literal_vector & t) {
  t.reset();
  unsigned qhead = m_qhead;
  TRACE("satmodsat", tout << m_idx << " " << qhead << " " << m_trail.size() << "\n";);
  bool r = propagate(false);
  if(!r) {    
    return false;
  }
  for(unsigned i = qhead; i < m_trail.size(); i++) {
    if(m_shared[m_trail[i].var()])
      t.push_back(m_trail[i]);
  }
  return true;
}

//convert b variables into a variables
void satmodsatcontext::varsbtoa(literal_vector const & tb, literal_vector& ta) {
  exchangelits(m_solverB, m_solverA, tb, ta);
}

//convert a variables into b variables
void satmodsatcontext::varsatob(literal_vector const& ta, literal_vector& tb) {
  exchangelits(m_solverA, m_solverB, ta, tb);
}

void satmodsatcontext::exchangelits(scoped_ptr<smssolver>& srcSolver, scoped_ptr<smssolver>& dstSolver, literal_vector const& srcTrail, literal_vector& dstTrail) {
  expr* e;
  bool s;
  bool_var vsrc, vdst;
  dstTrail.reset();
  for(literal l : srcTrail) {
    s = l.sign();
    vsrc = l.var();
    e = srcSolver->get_expr(vsrc);
    vdst = dstSolver->get_var(e);
    dstTrail.push_back(literal(vdst, s));
  }
}

void smssolver::get_reason(literal l, literal_vector& rc) {
  literal_vector todo;
  todo.push_back(l);
  rc.reset();
  while(!todo.empty()) {    
    literal t = todo.back();
    todo.pop_back();
    justification js = m_justification[t.var()];
    switch(js.get_kind()) {
    case justification::NONE:
      assert(false);
    case justification::BINARY:
      todo.push_back(js.get_literal());
      break;
    case justification::TERNARY:
      todo.push_back(js.get_literal1());
      todo.push_back(js.get_literal2());
      break;
    case justification::CLAUSE: {
      clause & c = get_clause(js);
      unsigned i   = 0;
      if (c[0].var() == t.var()) {
	i = 1;
      }
      else {
	SASSERT(c[1].var() == t.var());
	todo.push_back(c[0]);
	i = 2;
      }
      unsigned sz = c.size();
      for (; i < sz; i++) {
	todo.push_back(c[i]);
      }
      break;
    }
    case justification::EXT_JUSTIFICATION: {
      rc.push_back(t);
      break;
    }
    default:
      UNREACHABLE();
      break;
    }
  }
}

clause* smssolver::reasonFromOther(literal l) {
  literal_vector c;
  m_otherSolver->get_reason(l, c);  
  // is asserted the right status here?
  clause* lemma = mk_clause_core(c.size(), c.data(), sat::status::asserted());
  unsigned dl = 0;
  for(literal l : c) {
    dl = std::max(dl, lvl(l));
  }
  clause_offset co = cls_allocator().get_offset(lemma);
  justification js = justification(dl, co);
  m_justification[l.var()] = js;
  return lemma;
}

bool satmodsatcontext::propagateALL() {
  literal_vector tb, ta;
  bool progress, c;
  while(true) {
    ta.reset();
    tb.reset();
    c = m_solverB->propagateAndShare(tb);
    if(!c) {
      return false;
    }
    progress = tb.size() > 0;
    varsbtoa(tb, ta);
    m_tx_idx++;
    m_solverA->assignFromOther(ta, m_tx_idx);
    ta.reset();
    tb.reset();
    c = m_solverA->propagateAndShare(ta);
    if(!c) {
      m_solverA->resolvecc();
      return false;
    }
    varsatob(ta, tb);
    m_tx_idx++;
    m_solverB->assignFromOther(tb, m_tx_idx);
    progress = progress || ta.size() > 0; 
    if (!progress) break;
  }
  return true;
}

void satmodsatcontext::reset() {
  m_solverA->reset();
  m_solverB->reset();
}

void satmodsatcontext::addA(expr_ref fml) {
  add_cnf_expr_to_solver(m_solverA.get(), fml);
}

void satmodsatcontext::addB(expr_ref fml) {
  add_cnf_expr_to_solver(m_solverB.get(), fml);
}

void smssolver::add_clause_expr(expr* fml) {
  assert(m.is_or(fml));
  literal_vector c;
  for(expr* e: *to_app(fml)) {
    assert(m.is_bool(e));
    expr* n = e;
    bool t = m.is_not(e, n);
    assert(is_uninterp_const(n));
    bool_var v = boolVar(n);
    literal l = literal(v, t);
    c.push_back(l);
  }
  add_clause(c.size(), c.data(), sat::status::asserted());
}

void satmodsatcontext::add_cnf_expr_to_solver(smssolver* s, expr_ref fml) {
  assert(m.is_and(fml));
  for(expr* e: *to_app(fml)) {
    s->add_clause_expr(e);
  }
}
