#include "ast/ast_util.h"
#include "ast/ast.h"
#include "sat/sat_solver.h"
namespace sat {
  class smssolver : public solver {
    ast_manager &m;
    obj_map<expr, unsigned> m_expr2var;
    expr_ref_vector m_var2expr;
    bool_vector m_shared;
    unsigned m_idx;
    clause* reasonFromOther(literal l) override;
    void get_reason(literal l, literal_vector& c);
    //Solver for the previous Frame
    smssolver* m_pSolver;
    //Solver for the next Frame
    smssolver* m_nSolver;
    bool_var addVar(expr* n) {
      expr_ref e(n, m);
      unsigned v;
      assert(!m_expr2var.find(n, v));
      v = add_var(false);
      m_expr2var.insert(n, v);
      if (m_var2expr.size() <= v) {
	m_var2expr.resize(v + 1);
      }
      m_var2expr[v] = e;
      return v;
    }   
  public:
    smssolver(ast_manager& am, params_ref const &p, unsigned i): solver(p, am.limit()), m(am), m_var2expr(m), m_idx(i), m_nSolver(nullptr), m_pSolver(nullptr) {}
    void set_nSolver(smssolver* s) {m_nSolver = s;}
    void set_pSolver(smssolver* s) {m_pSolver = s;}
    void resolvecc() { resolve_conflict_core();};
    void assignFromOther(literal_vector const& t, size_t lvl) {
      for(literal l : t) {
	if(value(l) == l_undef) {
	  TRACE("satmodsat", tout << "propagating from other " << m_idx << " " << l  << "\n";);
	  assign_core(l, justification::mk_ext_justification(scope_lvl(), lvl));
	}
      }
      TRACE("satmodsat", tout << m_idx << " qhead " << m_qhead << "\n";);
      for(literal l : m_trail) {
	TRACE("satmodsat", tout << l << " ";);
      }
      TRACE("satmodsat", tout << "\n";);
    }
    
    void add_clause_expr(expr* c);
    bool_var boolVar(expr* n) {
      unsigned v = 0;
      if (m_expr2var.find(n, v))
	return v;
      return addVar(n);
    }
    bool propagateAndShare(literal_vector &t);
    void reset() {
      do_restart(true);
    }
    void addShared(expr_ref_vector& vars) {
      unsigned v;
      bool found;
      for(expr* e: vars) {
	found = m_expr2var.find(e, v);
	if(!found) {
	  v = addVar(e);
	}
	if (m_shared.size() <= v)
	  m_shared.resize(v + 1);
	m_shared[v] = true;
      }
    }
    bool_var get_var(expr* e) {
      bool_var v;
      bool found = m_expr2var.find(e, v); 
      assert(found);
      return v;
    }
    expr* get_expr(bool_var v) {
      assert(m_var2expr.size() > v);
      return m_var2expr[v].get();
    }
  };
  
class satmodsatcontext {
  ast_manager& m;
  scoped_ptr<smssolver> m_solverA;
  scoped_ptr<smssolver> m_solverB;
  size_t m_tx_idx;
  void add_cnf_expr_to_solver(smssolver* s, expr_ref fml);
  bool propagateALL();
  void varsbtoa(literal_vector const& b, literal_vector& a);
  void varsatob(literal_vector const& a, literal_vector& b);
  void exchangelits(scoped_ptr<smssolver>&, scoped_ptr<smssolver>&, literal_vector const&, literal_vector&);
public:
  void addA(expr_ref fml);
  void addB(expr_ref fml);
  void addShared(expr_ref_vector& vars) {
    m_solverA->addShared(vars);
    m_solverB->addShared(vars);
  }
  void reset();
  satmodsatcontext(ast_manager& am): m(am), m_tx_idx(0) {
    params_ref p;
    m_solverA = alloc(smssolver, m, p, 0);
    m_solverB = alloc(smssolver, m, p, 1);
    m_solverA->set_nSolver(m_solverB.get());
    m_solverB->set_pSolver(m_solverA.get());
  }
  bool solve();  
};

class sat_mod_sat {
  ast_manager& m;
  expr_ref_vector m_shared;
  expr_ref m_a;
  expr_ref m_b;
  satmodsatcontext m_solver;
  void init(expr_ref A, expr_ref B, expr_ref_vector& shared);
public:
  sat_mod_sat(ast_manager& am): m(am), m_shared(m), m_a(m), m_b(m), m_solver(m) { }
  void solve(expr_ref A, expr_ref B, expr_ref_vector& shared);
};
  
}
