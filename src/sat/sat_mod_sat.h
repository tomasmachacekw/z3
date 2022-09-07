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
    //Solver for the previous Frame
    smssolver* m_pSolver;
    //Solver for the next Frame
    smssolver* m_nSolver;
    //Keep track of how many times literals have been exchanged.
    //Might be useful for conflict analysis
    size_t m_tx_idx;
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
    bool_var boolVar(expr* n) {
      unsigned v = 0;
      if (m_expr2var.find(n, v))
	return v;
      return addVar(n);
    }
    bool propagate_and_share(literal_vector &t);
    bool propagate_all();
    clause* reason_from_other(literal l) override;
    void get_reason(literal l, literal_vector& c);
    void get_reason_final(literal_vector& c);
    void undo_lit(literal);
    void assign_from_other(literal_vector const&, size_t);
  public:
    smssolver(ast_manager& am, params_ref const &p, unsigned i): solver(p, am.limit()), m(am), m_var2expr(m), m_idx(i), m_pSolver(nullptr), m_nSolver(nullptr), m_tx_idx(0) {}
    void set_nSolver(smssolver* s) {m_nSolver = s;}
    void set_pSolver(smssolver* s) {m_pSolver = s;}
    void add_clause_expr(expr* c);
    bool modular_solve();
    void addShared(expr_ref_vector const& vars) {
      unsigned v;
      for(expr* e: vars) {
	v = boolVar(e);
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
  void add_cnf_expr_to_solver(smssolver* s, expr_ref fml);
public:
  void addA(expr_ref fml);
  void addB(expr_ref fml);
  void addShared(expr_ref_vector const& vars) {
    m_solverA->addShared(vars);
    m_solverB->addShared(vars);
    for(expr* e : vars) {
      SASSERT(m_solverA->get_var(e) == m_solverB->get_var(e));
    }
  }
  satmodsatcontext(ast_manager& am): m(am) {
    params_ref p;
    m_solverA = alloc(smssolver, m, p, 0);
    m_solverB = alloc(smssolver, m, p, 1);
    m_solverA->set_nSolver(m_solverB.get());
    m_solverB->set_pSolver(m_solverA.get());
  }
  bool solve() {
    return m_solverB->modular_solve();
  }
};

class sat_mod_sat {
  ast_manager& m;
  expr_ref_vector m_shared;
  expr_ref m_a;
  expr_ref m_b;
  satmodsatcontext m_solver;
  void init(expr_ref A, expr_ref B, expr_ref_vector const& shared);
public:
  sat_mod_sat(ast_manager& am): m(am), m_shared(m), m_a(m), m_b(m), m_solver(m) { }
  void solve(expr_ref A, expr_ref B, expr_ref_vector& shared);
};
  
}
