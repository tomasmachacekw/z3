/*++
Copyright (c) 2020

Module Name:

    qe_bv_arith.cpp

Abstract:

    Simple projection function for integer linear arithmetic

Author:

    Arie Gurfinkel
    Hari Govind V K
Revision History:

--*/

#include "qe/qe_bv_arith.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/bv_decl_plugin.h"
#include "qe/qe_mbp.h"

namespace qe {

struct bv_project_plugin::imp {
  ast_manager &m;
  bv_util bv;

  imp(ast_manager &_m) : m(_m), bv(m) {}
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

  void mk_add(expr_ref_vector &f, expr_ref &res) {
    if (f.size() == 1)
      res = f.get(0);
    else if (f.size() != 0)
      res = m.mk_app(bv.get_fid(), OP_BADD, f.size(), f.c_ptr());
  }

  void flatten_add(expr_ref t1, expr_ref_vector& res) {
      if (t1.get() == nullptr) return;
      if (!bv.is_bv_add(t1)) {
          res.push_back(t1);
          return;
      }
      rational val, sum = rational::zero();
      unsigned sz = bv.get_bv_size(t1.get());
      expr_ref flt(m);
      for (auto arg : *(to_app(t1))) {
          flatten_term(arg, flt);
          if (bv.is_numeral(flt, val)) sum = sum + val;
          else
              res.push_back(flt);
      }
      if (!sum.is_zero())
          res.push_back(bv.mk_numeral(sum, sz));
  }

    void flatten_term (expr* t, expr_ref& res) {
        expr* neg;
        if (bv.is_bv_neg(t)) {
            neg = to_app(t)->get_arg(0);
            if (bv.is_bv_neg(neg)) {
                res = to_app(neg)->get_arg(0);
                return;
            }
            if (bv.is_numeral(neg)) {
                mk_neg (neg, res);
                return;
            }
        }
        res = t;
        return;
    }

    void mk_add(expr_ref t1, expr_ref t2, expr_ref &res) {
        expr_ref_vector f(m);
        flatten_add(t1, f);
        flatten_add(t2, f);
        mk_add(f, res);
    }

    void mk_neg(expr *f, expr_ref &res) {
        rational val;
        expr *t1, *t2 = nullptr;
        const unsigned sz = bv.get_bv_size(f);
        rational bnd = rational::power_of_two(sz) - 1;

        if (bv.is_numeral(f, val)) {
            if (val == rational::zero())
                res = f;
            else {
                rational neg = rational::power_of_two(sz) - val;
                res = bv.mk_numeral(neg, sz);
            }
        } else if (bv.is_bv_neg(f))
            res = (to_app(f)->get_arg(0));
        else if (bv.is_bv_mul(f, t1, t2)) {
            if (bv.is_numeral(t1, val) && val == bnd)
                res = t2;
            else if (bv.is_numeral(t2, val) && val == bnd)
                res = t1;
            else
                res = bv.mk_bv_neg(f);
        } else if (bv.is_bv_add(f)) {
            expr_ref_vector tmp(m);
            expr_ref tmp1(m);
            for (auto arg : *(to_app(f))) {
                mk_neg(arg, tmp1);
                tmp.push_back(tmp1);
            }
            mk_add(tmp, res);
        } else
            res = bv.mk_bv_neg(f);
    }

    bool rewrite_concat(expr* a, model& model, expr_ref& res, expr_ref& sc) {
        if (bv.is_bv_add(a)) {
            expr_ref a1(m), a1_neg(m), a2(m);
            a1 = to_app(a)->get_arg(0);
            a2 = to_app(a)->get_arg(1);
            if (bv.is_concat(a2)) {
                expr_ref a21(m), a22(m);
                a21 = to_app(a2)->get_arg(0);
                a22 = to_app(a2)->get_arg(1);
                mk_add(a22, a1, res);
                mk_neg(a1, a1_neg);
                sc = bv.mk_ule(a22, a1_neg);
                if (model.is_true(sc)) {
                    return true;
                }
            }
        }
        return false;
    }

   bool solve(model &model, app_ref_vector &vars, expr_ref_vector &lits) {
      expr_ref_vector nw_lits(m);
      expr_ref res(m), sc(m);
      for (auto a: lits) {
          if (rewrite_concat(a, model, res, sc)) {
            TRACE("bv_tmp", tout << "replaced " << mk_pp(a, m) << " with " << res
                             << " and sc " << sc << "\n";);
            nw_lits.push_back(res);
            nw_lits.push_back(sc);
          }
          else nw_lits.push_back(a);
      }
      lits.reset();
      lits.append(nw_lits);
     return false;
  }
};

/**********************************************************/
/*  bv_project_plugin implementation                     */
/**********************************************************/
bv_project_plugin::bv_project_plugin(ast_manager &m) {
  m_imp = alloc(imp, m);
}

bv_project_plugin::~bv_project_plugin() { dealloc(m_imp); }

bool bv_project_plugin::operator()(model &model, app *var,
                                    app_ref_vector &vars,
                                    expr_ref_vector &lits) {
  return (*m_imp)(model, var, vars, lits);
}

void bv_project_plugin::operator()(model &model, app_ref_vector &vars,
                                    expr_ref_vector &lits) {
  m_imp->project(model, vars, lits, false);
}

vector<def> bv_project_plugin::project(model &model, app_ref_vector &vars,
                                        expr_ref_vector &lits) {
  return m_imp->project(model, vars, lits, true);
}

void bv_project_plugin::set_check_purified(bool check_purified) {
  UNREACHABLE();
}

bool bv_project_plugin::solve(model &model, app_ref_vector &vars,
                               expr_ref_vector &lits) {
  return m_imp->solve(model, vars, lits);
}

family_id bv_project_plugin::get_family_id() {
  return m_imp->bv.get_family_id();
}

opt::inf_eps bv_project_plugin::maximize(expr_ref_vector const &fmls,
                                          model &mdl, app *t, expr_ref &ge,
                                          expr_ref &gt) {
  UNREACHABLE();
  opt::inf_eps value;
  return value;
}


} // namespace qe
