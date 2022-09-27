#include "ast/ast_util.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "sat/sat_extension.h"
#include "sat/sat_solver.h"
#include "sat/sat_types.h"
namespace sat {

#define dbg_print(s)						\
  {								\
    TRACE("satmodsat",						\
	  tout << "solver" << m_idx << " " << s;);		\
  }

#define dbg_print_stat(s, t)					\
  {								\
    TRACE("satmodsat",						\
	  tout << "solver" << m_idx << " " << s << " " << t;);	\
  }
    
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

#define NSOLVER_EXT_IDX 0
#define PSOLVER_EXT_IDX 1
  
class sms_solver : public extension {
  ast_manager &m;
  obj_map<expr, unsigned> m_expr2var;
  expr_ref_vector m_var2expr;
  bool_vector m_shared;
  unsigned m_idx;
  literal_vector m_pSolver_clause;
  sms_solver* m_pSolver;
  sms_solver* m_nSolver;
  //Keep track of how many times literals have been exchanged.
  //Might be useful for conflict analysis
  size_t m_tx_idx;
  bool m_construct_itp;
  vector<literal_vector> m_itp;  
  bool_var addVar(expr* n) {
    expr_ref e(n, m);
    unsigned v;
    SASSERT(!m_expr2var.find(n, v));
    v = m_solver->add_var(true);
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
  unsigned m_full_assignment_lvl;
  literal_vector m_core;
  literal_vector m_asserted;
public:
  sms_solver(ast_manager& am, symbol const& name, int id): extension(name, id), m(am), m_var2expr(m), m_idx(id), m_pSolver(nullptr), m_nSolver(nullptr), m_tx_idx(0), m_construct_itp(false), m_full_assignment_lvl(0) {
    params_ref p;
  }
  literal_vector const& get_asserted() { return m_asserted; }
  void reset_asserted() { m_asserted.reset(); }
  void set_conflict();
  void construct_itp() { m_construct_itp = true; }
  void set_pSolver(sms_solver* p) { m_pSolver = p;}
  void set_nSolver(sms_solver* n) { m_nSolver = n;}
  void get_reason(literal, literal_vector&);
  void get_reason_final(literal_vector&);
  void get_antecedents(literal, ext_justification_idx, literal_vector&, bool) override;
  bool unit_propagate() override;
  void asserted(literal) override;
  void assign_from_other(literal, ext_justification_idx);
  void push_from_other();
  void init_search() override;
  void push() override;
  void pop(unsigned) override;
  void pop_from_other(unsigned);
  bool propagate();
  literal_vector const &get_core() { return m_core; }
  lbool resolve_conflict() override {
    return l_undef;
  }

  std::ostream& display(std::ostream& out) const override {
    return out <<"display yet to be implemented\n";
  }

  std::ostream& display_justification(std::ostream& out, ext_justification_idx idx) const override {
    switch (idx) {
    case NSOLVER_EXT_IDX:
      return out << "ext literal from NSOLVER\n";
    case PSOLVER_EXT_IDX:
      return out << "ext literal from PSOLVER\n";
    default:
      UNREACHABLE();
      return out;
    }
  }

  std::ostream& display_constraint(std::ostream& out, ext_constraint_idx idx) const override {
        return out << "display constraint yet to be implemented " << idx << "\n";
  }

  check_result check() override;
  bool modular_solve();
  void add_clause_expr(expr* fml);
  void addShared(expr_ref_vector const& vars) {
    unsigned v;
    for(expr* e: vars) {
      v = boolVar(e);
      m_shared[v] = true;
    }
  }
  void print_itp() {
    TRACE("satmodsat", tout << "Interpolant is \n";
	  for(literal_vector const& lv : m_itp) {
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
    SASSERT(found);
    return v;
  }
  expr* get_expr(bool_var v) {
    SASSERT(m_var2expr.size() > v);
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
  extension* m_solverA;
  extension* m_solverB;
  solver* m_satA;
  solver* m_satB;
  void add_cnf_expr_to_solver(extension* s, expr_ref fml);
public:
  void addA(expr_ref fml);
  void addB(expr_ref fml);
  void addShared(expr_ref_vector const& vars) {
    sms_solver* a = static_cast<sms_solver*>(m_solverA);
    sms_solver* b = static_cast<sms_solver*>(m_solverB);
    a->addShared(vars);
    b->addShared(vars);
    for(expr* e : vars) {
      SASSERT(a->get_var(e) == b->get_var(e));
    }
    a->print_var_map();
    b->print_var_map();
  }
  satmodsatcontext(ast_manager& am): m(am) {
    params_ref p;
    m_solverA = alloc(sms_solver, m, symbol("A"), 0);
    m_solverB = alloc(sms_solver, m, symbol("B"), 1);    
    sms_solver* a = static_cast<sms_solver*>(m_solverA);
    sms_solver* b = static_cast<sms_solver*>(m_solverB);
    a->set_nSolver(b);
    b->set_pSolver(a);
    m_satA = alloc(solver, p, m.limit());
    m_satA->set_extension(m_solverA);
    m_satB = alloc(solver, p, m.limit());
    m_satB->set_extension(m_solverB);
    b->construct_itp();
  }
  ~satmodsatcontext(){
    dealloc(m_satA);
    dealloc(m_satB);
  }
  bool solve() {
    sms_solver* b = static_cast<sms_solver*>(m_solverB);
    if(!b->modular_solve()) { 
      b->print_itp();
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
