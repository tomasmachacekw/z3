#include "sat/sat_mod_sat.h"
#include "ast/ast_pp.h"
#include "util/sat_literal.h"

using namespace sat;
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

/*
  Assign from other solvers using ext justification
 */
void smssolver::assign_from_other(literal_vector const& t) {
  if (t.size() == 0)
    return;
  if (m_scope_lvl == 0) push();
  for(literal lit : t) {
    if (m_assumption_set.contains(lit))
      continue;
    set_external(lit.var());
    SASSERT(is_external(lit.var()));
    add_assumption(lit);
    assign_scoped(lit);
    if (inconsistent()) return;
  }
  m_search_lvl = scope_lvl();
  dbg_print_state();
}

// remove assumptions to match t
// assumes that m_assumptions and t have a common prefix modulo private symbols in t
// TODO: optimize by using above assumption
void smssolver::rm_assumptions(literal_vector const& t) {
  pop_to_base_level();
  literal_vector tmp;
  bool_var v;
  for(literal l : t) {
    v = l.var();
    if(v < m_shared.size() && m_shared[v])
      tmp.push_back(l);
  }
  init_assumptions(tmp.size(), tmp.data());
  dbg_print_state();
}

bool smssolver::modular_solve() {
  bool c, d;
  while(true) {
    c = propagate_all();
    if (!c) {
      // resolve conflicting literals and put the result into m_lemma
      // uses reason_from_other to resolve literals propagated by other solvers
      // learns lemma and backjumps
      if (!resolve_conflict()) {
	return false;
      }          
      // undo propagations in m_pSolver
      // this step is missing in the sat modulo sat paper
      if (m_pSolver) {
	m_pSolver->rm_assumptions(m_trail);
      }
      continue;
    }
    dbg_print_state();
    d = decide();
    dbg_print_lv("after decide", m_trail);
    if (!d) {
      // All literals assigned
      if (!m_pSolver)
	return true;
      dbg_print_lv("all assignments done. moving to prev solver", m_trail)
      // Solve with assumptions
      if (m_pSolver->modular_solve())
	return true;
      // calls resolve_conflict_for_unsat_core
      m_pSolver->do_analyze_final();
      literal_vector const& clc = m_pSolver->get_core();
      literal_vector lc;
      unsigned dl = 0;
      for(literal l : clc) {
	dl = std::max(lvl(l), dl);
	lc.push_back(~l);
      }
      if (m_construct_itp) itp.push_back(lc);
      dbg_print_lv("learning clause", lc);
      // Previous solver hit a conflict without this solver making any decisions
      if (dl == 0)
	return false;
      mk_clause_core(lc.size(), lc.data(), sat::status::redundant());
      // backjump to decision level dl
      pop_reinit(m_scope_lvl - dl);
      dbg_print_state();
      m_pSolver->rm_assumptions(m_trail);
    }
  } 
}

/*
Methods to propagate literals
 */
bool smssolver::propagate_all() {
  bool progress, c;
  literal_vector th, tp;
  while(true) {
    th.reset();
    c = propagate_and_share(th);
    if (!c) return false;
    progress = th.size() > 0;
    if (!m_pSolver) return progress;
    m_pSolver->assign_from_other(th);
    c = m_pSolver->propagate_and_share(tp);
    if (!c) {
      m_pSolver->do_analyze_final();
      literal_vector const& ccc = m_pSolver->get_core();
      m_lemma.reset();
      unsigned dl = 0;
      for(literal l : ccc) {
	dl = std::max(dl, lvl(l));
	m_lemma.push_back(~l);
	// lrb code assumes that all but the first literal are marked
	mark(l.var());
      }
      if (m_lemma.size() > 0) {
	// lrb code assumes that the first literal is unmarked
	reset_mark(m_lemma[0].var());      
	dbg_print_lv("learning clause after prop hit conflict in other solver", m_lemma);
	if (m_construct_itp) itp.push_back(m_lemma);
      }
      SASSERT(dl <= m_scope_lvl);
      // backtrack till the highest decision level to try and force a conflict
      learn_lemma_and_backjump();
      // mk_clause_core(cc.size(), cc.data(), sat::status::redundant());
      dbg_print_state();
      m_pSolver->rm_assumptions(m_trail);
      if(!propagate_and_share(tp))
	return false;
    }
    assign_from_other(tp); 
    progress = progress || tp.size() > 0; 
    if (!progress) break;    
  }
  return true;
}

bool smssolver::propagate_and_share(literal_vector & t) {
  t.reset();
  unsigned qhead = m_qhead;
  dbg_print_state();
  bool r = propagate(false);
  dbg_print_state();
  if(!r) return false;
  for(unsigned i = qhead; i < m_trail.size(); i++) {
    if(m_shared[m_trail[i].var()])
      t.push_back(m_trail[i]);
  }
  return true;
}

/*
  Conflict analysis
 */
void smssolver::get_reason(literal l, literal_vector& rc) {
  dbg_print_lit("Fetching reason for", l);
  literal_vector todo;
  todo.push_back(l);
  rc.reset();
  while(!todo.empty()) {    
    literal t = todo.back();
    todo.pop_back();
    justification js = m_justification[t.var()];
    TRACE("satmodsat", display_justification(tout, js););
    switch(js.get_kind()) {
    case justification::NONE:
      SASSERT(m_assumption_set.contains(t));
      rc.push_back(~t);
      break;
    case justification::BINARY:
      todo.push_back(~js.get_literal());
      break;
    case justification::TERNARY:
      todo.push_back(~js.get_literal1());
      todo.push_back(~js.get_literal2());
      break;
    case justification::CLAUSE: {
      clause & c = get_clause(js);
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
      SASSERT(false);
      break;
    }
    default:
      UNREACHABLE();
      break;
    }
  }
}

clause* smssolver::reason_from_other(literal l) {
  dbg_print_state();
  literal_vector c;
  SASSERT(m_pSolver);
  m_pSolver->get_reason(l, c);
  literal_vector cc;
  for (literal l : c)
    cc.push_back(~l);
  if (m_construct_itp)
    itp.push_back(cc);
  // is asserted the right status here?
  clause* lemma = mk_clause_core(cc.size(), cc.data(), sat::status::redundant());
  unsigned dl = 0;
  for(literal l : cc) {
    dl = std::max(dl, lvl(l));
  }
  // justification is the negation of conflict clause.
  justification js(dl);
  switch(c.size()) {
  case 1:
    SASSERT(l != c[0]);
    js = justification(dl, c[0]);
    break;
  case 2:
    SASSERT(l != c[0]);
    SASSERT(l != c[1]);
    js = justification(dl, c[0], c[1]);
    break;
  default:
    SASSERT(lemma);
    clause_offset co  = cls_allocator().get_offset(lemma);
    js = justification(dl, co);
  }
  m_justification[l.var()] = js;
  return lemma;
}

void smssolver::do_analyze_final() {
  //SASSERT(inconsistent());
  bool unique_max;
  m_conflict_lvl = get_max_lvl(m_not_l, m_conflict, unique_max);
  resolve_conflict_for_unsat_core();
  pop_to_base_level();
}

/*
 Functions to add clauses to solvers
 TODO: replace with standard way of doing it e.g. in euf_solver.h
 */
void smssolver::add_clause_expr(expr* fml) {
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
  add_clause(c.size(), c.data(), sat::status::input());
}

void satmodsatcontext::addA(expr_ref fml) {
  add_cnf_expr_to_solver(m_solverA.get(), fml);
}

void satmodsatcontext::addB(expr_ref fml) {
  add_cnf_expr_to_solver(m_solverB.get(), fml);
}

void satmodsatcontext::add_cnf_expr_to_solver(smssolver* s, expr_ref fml) {
  SASSERT(m.is_and(fml));
  for(expr* e: *to_app(fml)) {
    s->add_clause_expr(e);
  }
}
