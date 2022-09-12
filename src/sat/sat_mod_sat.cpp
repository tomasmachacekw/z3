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
void smssolver::assign_from_other(literal_vector const& t, size_t lvl) {
  for(literal l : t) {
    if(value(l) == l_undef) {
      dbg_print_lit("propagating from other", l);
      assign_core(l, justification::mk_ext_justification(scope_lvl(), lvl));
    }
  }
  dbg_print_state();
}

bool smssolver::modular_solve() {
  bool d;
  while(true) {
    bool c = propagate_all();
    if (!c) {
      bool unique_max;
      m_conflict_lvl = get_max_lvl(m_not_l, m_conflict, unique_max);
      //TODO: learn lemma from propagations at dl0
      if (m_conflict_lvl == 0) {
	return false;
      }
	    
      // resolve conflicting literals and put the result into m_lemma
      // uses reason_from_other to resolve literals propagated by other solvers
      // learns lemma and backjumps
      resolve_conflict_core();
      
      // undo propagations in m_pSolver
      // this step is missing in the sat modulo sat paper
      if (m_pSolver) {
	dbg_print_state();
	bool no_shared_in_trail = true;
	for(unsigned i = m_qhead; i-- > 0;) {
	  if (m_shared[m_trail[i].var()]) {
	    literal l = m_trail[i];
	    // The problem here is that the literal l is also undone
	    // we should undo all literals above l
	    m_pSolver->undo_lit(l);
	    literal_vector tmp;
	    tmp.push_back(l);
	    m_pSolver->assign_from_other(tmp, m_tx_idx);
	    no_shared_in_trail = false;	    
	    break;
	  }
	}
	if (no_shared_in_trail) {
	  m_pSolver->do_restart(true);
	  m_pSolver->undo_ext_prop();
	}
      }
      continue;
    }
    dbg_print_state();
    d = decide();
    if (!d) {
      // All literals assigned
      if (!m_pSolver)
	return true;
      if (m_pSolver->modular_solve())
	return true;
      // Previous solver hit a conflict without this solver making any decisions
      if (m_scope_lvl == 0)
	return false;
      literal_vector lc;
      m_pSolver->get_reason_final(lc);
      unsigned dl = 0;
      literal pop_lit;
      for(literal l : lc) {
	if (lvl(l) > dl) {
	  pop_lit = ~l;
	}
	dl = std::max(lvl(l), dl);
      }
      itp.push_back(lc);
      dbg_print_lv("learning clause", lc);
      mk_clause_core(lc.size(), lc.data(), sat::status::redundant());
      pop_reinit(m_scope_lvl - dl);
      undo_lit(pop_lit);
      dbg_print_state();
      m_pSolver->do_restart(true);
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
    m_tx_idx++;
    m_pSolver->assign_from_other(th, m_tx_idx);
    c = m_pSolver->propagate_and_share(tp);
    if (!c) {
      tp.clear();
      m_pSolver->get_reason_final(tp);
      unsigned dl = 0;
      for(literal l : tp) {
	dl = std::max(dl, lvl(l));
      }
      dbg_print_lv("learning clause after prop hit conflict in other solver", tp);
      itp.push_back(tp);
      mk_clause_core(tp.size(), tp.data(), sat::status::redundant());
      // backtrack till the highest decision level to try and force a conflict
      pop_reinit(m_scope_lvl - dl);
      tp.reset();
      if(!propagate_and_share(tp))
	return false;
    }
    m_tx_idx++;
    assign_from_other(tp, m_tx_idx);    
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
      SASSERT(false);
      // SASSERT(js.level() == 0);
      // rc.push_back(t);
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
      rc.push_back(~t);
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
  SASSERT(m_pSolver || m_nSolver);
  if (m_pSolver)
    m_pSolver->get_reason(~l, c);
  else
    m_nSolver->get_reason(~l, c);
  itp.push_back(c);
  // is asserted the right status here?
  clause* lemma = mk_clause_core(c.size(), c.data(), sat::status::redundant());
  unsigned dl = 0;
  for(literal l : c) {
    dl = std::max(dl, lvl(l));
  }
  clause_offset co = cls_allocator().get_offset(lemma);
  justification js = justification(dl, co);
  m_justification[l.var()] = js;
  return lemma;
}

//Get all literals from other solver that caused the current conflict
void smssolver::get_reason_final(literal_vector &t) {
  SASSERT(inconsistent());
  get_reason(m_not_l, t);
  dbg_print_lv("reason final", t);
}

/*
  backjumping
 */
void smssolver::undo_lit(literal l) {
  dbg_print_lit("undoing", l);
  dbg_print_state();
  unsigned dl = lvl(l);
  pop_reinit(m_scope_lvl - dl);
  // if level is zero, trail has to be cleared till this literal is unassigned
  unsigned i = dl == 0 ? m_trail.size() : m_scopes[dl - 1].m_trail_lim + 1;
  for(;i-- > 0;)
    if(m_trail[i] == l) {
      undo_ext_prop(i);
      break;
    }
  dbg_print_state();
}
//undo all propagations starting from the first shared variable since index st
void smssolver::undo_ext_prop(unsigned st) {
  SASSERT(m_scope_lvl == 0);
  bool rm = false;
  unsigned sz = st;
  for (unsigned i = st; i < m_trail.size(); i++) {
    rm = rm || m_shared[m_trail[i].var()];
    if (!rm) {
      sz++;
      continue;
    }
    literal l  = m_trail[i];
    bool_var v = l.var();
    m_assignment[l.index()]    = l_undef;
    m_assignment[(~l).index()] = l_undef;
    SASSERT(value(v) == l_undef);
    m_case_split_queue.unassign_var_eh(v);
    if (m_config.m_anti_exploration) {
      m_canceled[v] = m_stats.m_conflict;
    }
  }
  m_trail.shrink(sz);        
  m_qhead = m_trail.size();
  dbg_print_state();
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
