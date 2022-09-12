#include "ast/ast_util.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "sat/sat_solver.h"
namespace sat {

#define dbg_print_lit(s, l)					\
  {								\
    TRACE("satmodsat",						\
	  tout << "solver" << m_idx << " " << s;			\
	if (l.sign()) {						\
	  tout <<  " -" << expr_ref(get_expr(l.var()), m);	\
	}							\
	else {							\
	  tout <<  " " << expr_ref(get_expr(l.var()), m);	\
	};);							\
  }

#define dbg_print_lv(s, lv)					\
  {								\
    TRACE("satmodsat",						\
	  tout << "solver" <<  m_idx << " " << s;		\
	  for (literal l : lv) {				\
	    if (l.sign()) {					\
	      tout <<  " -" << expr_ref(get_expr(l.var()), m);	\
	    }							\
	    else {						\
	      tout <<  " " << expr_ref(get_expr(l.var()), m);	\
	    }							\
	  };);							\
  }

#define dbg_print_state()						\
  {									\
    TRACE("satmodsat", tout << "solver" << m_idx			\
	  << " printing stats qhead " << m_qhead << " trail size "	\
	  << m_trail.size() << " scope level " << m_scope_lvl		\
	  << " trail";							\
	  for(literal l: m_trail) {					\
	    if (l.sign()) {						\
	      tout <<  " -" << expr_ref(get_expr(l.var()), m);		\
	    }								\
	    else {							\
	      tout <<  " " << expr_ref(get_expr(l.var()), m);		\
	    }								\
	  }								\
	  ;);								\
  }
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
    vector<literal_vector> itp;
    bool_var addVar(expr* n) {
      expr_ref e(n, m);
      unsigned v;
      SASSERT(!m_expr2var.find(n, v));
      v = add_var(false);
      TRACE("satmodsat", tout << "adding var " << v << " for expr " << expr_ref(n, m););
      m_expr2var.insert(n, v);
      if (m_var2expr.size() <= v) {
	m_var2expr.resize(v + 1);
      }
      m_var2expr[v] = e;
      if (m_shared.size() <= v)
	m_shared.resize(v + 1);
      m_shared[v] = false;
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
    void undo_ext_prop(unsigned st = 0);
    void addShared(expr_ref_vector const& vars) {
      unsigned v;
      for(expr* e: vars) {
	v = boolVar(e);
	m_shared[v] = true;
      }
    }
    void print_itp() {
      TRACE("satmodsat", tout << "Interpolant is \n";
	    for(literal_vector const& lv : itp) {
	      for(literal l : lv) {
		if (l.sign()) {						
		  tout <<  " -" << expr_ref(get_expr(l.var()), m);	
		}						       
		else {							
		  tout <<  " " << expr_ref(get_expr(l.var()), m);      
		}	
	      }
	      tout << "\n";
	    };);
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
    void print_var_map() {
      TRACE("satmodsat", for(unsigned i = 0; i < m_var2expr.size(); i++) {
	  tout << "expr " << expr_ref(m_var2expr[i].get(), m) << " var " << i << "\n";	  
	};);
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
    m_solverA->print_var_map();
    m_solverB->print_var_map();
  }
  satmodsatcontext(ast_manager& am): m(am) {
    params_ref p;
    m_solverA = alloc(smssolver, m, p, 0);
    m_solverB = alloc(smssolver, m, p, 1);
    m_solverA->set_nSolver(m_solverB.get());
    m_solverB->set_pSolver(m_solverA.get());
  }
  bool solve() {
    if(!m_solverB->modular_solve()) {      
      m_solverB->print_itp();
      return false;
    }
    return true;
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
