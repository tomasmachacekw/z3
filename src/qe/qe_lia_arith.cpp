/*++
Copyright (c) 2020

Module Name:

    qe_lia_arith.cpp

Abstract:

    Simple projection function for integer linear arithmetic

Author:

   Arie Gurfinkel
   Grigory Fedyukovich

Revision History:

--*/

#include "qe/qe_lia_arith.h"
#include "ast/ast_util.h"
#include "qe/qe_mbp.h"

namespace qe {

struct lia_project_plugin::imp {
  ast_manager &m;
  arith_util a;

  imp(ast_manager &_m) : m(_m), a(m) {}
  ~imp() {}

  // MAIN PROJECTION FUNCTION
  // if compute_def is true, return witnessing definitions
  vector<def> project(model &model, app_ref_vector &vars, expr_ref_vector &fmls,
                      bool compute_def) {
    // check that all variables are integer, otherwise either fail or fall back
    // to qe_arith plugin
    // give up without even trying
    return vector<def>();
  }

  // project a single variable
  bool operator()(model &model, app *v, app_ref_vector &vars,
                  expr_ref_vector &lits) {
    app_ref_vector vs(m);
    vs.push_back(v);
    project(model, vs, lits, false);
    return vs.empty();
  }

  bool solve(model &model, app_ref_vector &vars, expr_ref_vector &lits) {
    // no pre-processing
    return false;
  }
};

/**********************************************************/
/*  lia_project_plugin implementation                     */
/**********************************************************/
lia_project_plugin::lia_project_plugin(ast_manager &m) {
  m_imp = alloc(imp, m);
}

lia_project_plugin::~lia_project_plugin() { dealloc(m_imp); }

bool lia_project_plugin::operator()(model &model, app *var,
                                    app_ref_vector &vars,
                                    expr_ref_vector &lits) {
  return (*m_imp)(model, var, vars, lits);
}

void lia_project_plugin::operator()(model &model, app_ref_vector &vars,
                                    expr_ref_vector &lits) {
  m_imp->project(model, vars, lits, false);
}

vector<def> lia_project_plugin::project(model &model, app_ref_vector &vars,
                                        expr_ref_vector &lits) {
  return m_imp->project(model, vars, lits, true);
}

void lia_project_plugin::set_check_purified(bool check_purified) {
  UNREACHABLE();
}

bool lia_project_plugin::solve(model &model, app_ref_vector &vars,
                               expr_ref_vector &lits) {
  return m_imp->solve(model, vars, lits);
}

family_id lia_project_plugin::get_family_id() {
  return m_imp->a.get_family_id();
}

opt::inf_eps lia_project_plugin::maximize(expr_ref_vector const &fmls,
                                          model &mdl, app *t, expr_ref &ge,
                                          expr_ref &gt) {
  UNREACHABLE();
  opt::inf_eps value;
  return value;
}

void lia_project_plugin::saturate(model &model,
                                  func_decl_ref_vector const &shared,
                                  expr_ref_vector &lits) {
  UNREACHABLE();
}

} // namespace qe
