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
#include "ast/expr_abstract.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "cmd_context/cmd_context.h"
#include "qe/qe_mbp.h"
#include "smt/smt_solver.h"

namespace qe {

bool contains(expr *e, expr *v) {
  if (e == v)
    return true;
  for (expr *arg : *to_app(e))
    if (contains(arg, v))
      return true;
  return false;
}
void mk_add(expr_ref_vector &f, expr_ref &res) {
  ast_manager &m = res.get_manager();
  bv_util m_bv(m);
  if (f.size() == 1)
    res = f.get(0);
  else if (f.size() != 0)
    res = m.mk_app(m_bv.get_fid(), OP_BADD, f.size(), f.c_ptr());
}
void mk_neg(expr *f, expr_ref &res) {
    ast_manager &m = res.get_manager();
    bv_util m_bv(m);
    rational val;
    expr *t1, *t2 = nullptr;
    const unsigned sz = m_bv.get_bv_size(f);
    rational bnd = rational::power_of_two(sz) - 1;

    if (m_bv.is_numeral(f, val)) {
        if (val == rational::zero())
            res = f;
        else {
            rational neg = rational::power_of_two(sz) - val;
            res = m_bv.mk_numeral(neg, sz);
        }
    } else if (m_bv.is_bv_neg(f))
        res = (to_app(f)->get_arg(0));
    else if (m_bv.is_bv_mul(f, t1, t2)) {
        if (m_bv.is_numeral(t1, val) && val == bnd)
            res = t2;
        else if (m_bv.is_numeral(t2, val) && val == bnd)
            res = t1;
        else
            res = m_bv.mk_bv_neg(f);
    } else if (m_bv.is_bv_add(f)) {
        expr_ref_vector tmp(m);
        expr_ref tmp1(m);
        for (auto arg : *(to_app(f))) {
            mk_neg(arg, tmp1);
            tmp.push_back(tmp1);
        }
        mk_add(tmp, res);
    } else
        res = m_bv.mk_bv_neg(f);
}
void flatten_term(expr *t, expr_ref &res) {
  ast_manager &m = res.get_manager();
  bv_util m_bv(m);
  expr *neg;
  if (m_bv.is_bv_neg(t)) {
    neg = to_app(t)->get_arg(0);
    if (m_bv.is_bv_neg(neg)) {
      res = to_app(neg)->get_arg(0);
      return;
    }
    if (m_bv.is_numeral(neg)) {
      mk_neg(neg, res);
      return;
    }
  }
  res = t;
  return;
}
void flatten_add(expr_ref t1, expr_ref_vector &res) {
  ast_manager &m = t1.get_manager();
  bv_util m_bv(m);
  if (t1.get() == nullptr)
    return;
  if (!m_bv.is_bv_add(t1)) {
    res.push_back(t1);
    return;
  }
  rational val, sum = rational::zero();
  unsigned sz = m_bv.get_bv_size(t1.get());
  expr_ref flt(m);
  for (auto arg : *(to_app(t1))) {
    flatten_term(arg, flt);
    if (m_bv.is_numeral(flt, val))
      sum = sum + val;
    else
      res.push_back(flt);
  }
  if (!sum.is_zero())
    res.push_back(m_bv.mk_numeral(sum, sz));
}

void mk_add(expr_ref t1, expr_ref t2, expr_ref &res) {
  expr_ref_vector f(t1.get_manager());
  flatten_add(t1, f);
  flatten_add(t2, f);
  mk_add(f, res);
}

bool unhandled(expr *f, expr_ref var) {
    bv_util u(var.get_manager());
    SASSERT(contains(f, var));
    if (is_uninterp(f))
        return false;
    if (u.is_bv_sdiv(f) || u.is_bv_udiv(f))
        return true;
    if (u.is_bv_smod(f) || u.is_bv_smodi(f) || u.is_bv_smod0(f))
        return true;
    if (u.is_bv_urem(f) || u.is_bv_urem0(f) || u.is_bv_uremi(f))
        return true;
    if (u.is_extract(f) || u.is_concat(f))
        return true;
    for (auto a : *(to_app(f))) {
        if (!contains(a, var))
            continue;
        return unhandled(a, var);
    }
    return false;
}
bool split(expr *e, expr *var, expr_ref t1, expr_ref t2) {
    ast_manager &m(t2.get_manager());
    bv_util m_bv(m);
    if (!m_bv.is_bv_add(e))
        return false;
    expr_ref_vector nw_args(m);
    for (expr *arg : *to_app(e)) {
        if (contains(arg, var))
            t1 = arg;
        else
            nw_args.push_back(arg);
    }
    mk_add(nw_args, t2);
    return true;
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
        const unsigned sz = m_bv.get_bv_size(f);
        rational bnd = rational::power_of_two(sz) - 1;

        if (m_bv.is_numeral(f, val)) {
            if (val == rational::zero())
                res = f;
            else {
                rational neg = rational::power_of_two(sz) - val;
                res = m_bv.mk_numeral(neg, sz);
            }
        } else if (m_bv.is_bv_neg(f))
            res = (to_app(f)->get_arg(0));
        else if (m_bv.is_bv_mul(f, t1, t2)) {
            if (m_bv.is_numeral(t1, val) && val == bnd)
                res = t2;
            else if (m_bv.is_numeral(t2, val) && val == bnd)
                res = t1;
            else
                res = m_bv.mk_bv_neg(f);
        } else if (m_bv.is_bv_add(f)) {
            expr_ref_vector tmp(m);
            expr_ref tmp1(m);
            for (auto arg : *(to_app(f))) {
                mk_neg(arg, tmp1);
                tmp.push_back(tmp1);
            }
            mk_add(tmp, res);
        } else
            res = m_bv.mk_bv_neg(f);
    }

    bool rewrite_concat(expr* a, expr_ref& res, expr_ref& sc) {
        if (m_bv.is_bv_add(a)) {
            expr_ref a1(m), a1_neg(m), a2(m);
            a1 = to_app(a)->get_arg(0);
            a2 = to_app(a)->get_arg(1);
            rational n;
            expr_ref_vector nw_args(m);
            if (m_bv.is_concat(a2) && m_bv.is_numeral(a1, n)) {
                expr_ref a21(m), a22(m);
                for (unsigned i = 0; i < to_app(a2)->get_num_args() - 1; i++) {
                    nw_args.push_back(to_app(a2)->get_arg(i));
                }
                a22 = to_app(a2)->get_arg(to_app(a2)->get_num_args() - 1);
                unsigned dff = m_bv.get_bv_size(a22);
                if (n > rational::power_of_two(dff - 1) - 1 ||
                    n < -rational::power_of_two(dff - 1)) {
                    return false;
                }
                expr_ref t(m), t_res(m);
                t = m_bv.mk_numeral(n, dff);
                TRACE("bv_tmp", tout << "a22 is " << a22 << " and " << t << "\n";);
                mk_add(a22, t, t_res);
                mk_neg(t, a1_neg);
                nw_args.push_back(t_res);
                sc = m_bv.mk_ule(a22, a1_neg);
                if (!m_mdl->is_true(sc)) {
                  res = m_bv.mk_concat(nw_args.size(), nw_args.c_ptr());
                  return true;
                }
            }
        }
        return false;
    }

    br_status reduce_app(func_decl *f, unsigned num, expr *const *args,
                         expr_ref &result, proof_ref &result_pr) {
        expr_ref sc(m);
        expr *e = m.mk_app(f, num, args);
        TRACE("bv_tmp", tout << "rewriting " << mk_pp(e, m) << "\n";);
        if (rewrite_concat(e, result, sc)) {
            m_sc.push_back(sc);
            TRACE("bv_tmp", tout << "concat rewritten " << result << " and sc " << sc << "\n";);
            return BR_DONE;
        }
        return BR_FAILED;
    }
};

struct bv_project_plugin::imp {
    ast_manager &m;
    bv_util bv;
    vector<rw_rule> m_rw_rules;
    imp(ast_manager &_m) : m(_m), bv(m) {
        m_rw_rules.push_back(addl1(m));
        m_rw_rules.push_back(addl2(m));
        m_rw_rules.push_back(addr1(m));
        m_rw_rules.push_back(addr2(m));
    }
    ~imp() {}

    void reset_rw_rules(model &mdl, expr_ref var) {
        for (rw_rule r : m_rw_rules) {
            r.reset(&mdl, var);
        }
    }
    //var is the only uninterpreted constant on one side of literal
    bool is_normalized(expr_ref b, expr_ref var) {
        if (unhandled(b, var)) return false;
        expr *e;
        if (m.is_not(b, e) && to_app(e)->get_num_args() != 2) return false;
        else e = b;
        if (to_app(e)->get_num_args() != 2) return false;
        expr *chd = to_app(e)->get_arg(0);
        expr *o_chd = to_app(e)->get_arg(1);
        if (!contains(chd, var)) {
            chd = to_app(e)->get_arg(1);
            o_chd = to_app(e)->get_arg(0);
            if (!contains(chd, var)) return false;
        }
        if (contains(o_chd, var)) return false;
        if (chd == var || bv.is_bv_mul(var)) return true;
        return false;
    }

    bool normalize(expr_ref var, expr_ref f, model &mdl, expr_ref_vector &res) {
        expr_ref_vector todo(m);
        todo.push_back(f);
        reset_rw_rules(mdl, var);
        expr_ref_vector out(m);
        expr_ref t(m);
        while (!todo.empty()) {
            t = todo.back();
            bool normalized = false;
            if (is_normalized(t, var)) {
                res.push_back(t);
                todo.pop_back();
                continue;
            }
            for (rw_rule r: m_rw_rules) {
                out.reset();
                if (r.apply(t, out)) {
                    normalized = true;
                    todo.pop_back();
                    todo.append(out);
                    break;
                }
            }
            // t cannot be normalized
            if (!normalized) return false;
        }
        return true;
    }

    // MAIN PROJECTION FUNCTION
    // if compute_def is true, return witnessing definitions
    vector<def> project(model &model, app_ref_vector &vars,
                        expr_ref_vector &fmls, bool compute_def) {
      // check that all variables are integer, otherwise either fail or fall
      // back to qe_arith plugin give up without even trying
      expr_ref_vector res(m);
      res.append(fmls);
      for (unsigned var_num = 0; var_num < vars.size(); var_num++) {
        expr_ref v(vars.get(var_num), m);
        TRACE("bv_tmp", tout << "eliminate " << mk_pp(v, m) << "\n";);

        expr_ref_vector new_fmls(m), norm(m), backg_fmls(m), norm_fmls(m);
        expr_ref_vector pi(m), sig(m);

        for (unsigned f_num = 0; f_num < res.size(); f_num++) {
          expr_ref f(res.get(f_num), m);

          // background fmls
          if (!contains(f, v)) {
            backg_fmls.push_back(f);
            continue;
          }
          norm.reset();
          // normalize and add to pi
          if (normalize(v, f, model, norm)) {
            TRACE("bv_tmp", tout << "Normalized " << f << " into "
                                  << mk_and(norm) << "\n";);
            pi.push_back(f);
          } else {
            TRACE("bv_tmp", tout << "Could not normalize " << f << " at var "
                                  << v << "\n";);
            sig.push_back(f);
          }
        }
        lazy_mbp(backg_fmls, pi, sig, v, new_fmls, model);
        res.reset();
        res.append(new_fmls);
        res.append(backg_fmls);
      }
      return vector<def>();
    }

void mk_exists(expr *f, app_ref_vector &vars, expr_ref &res) {
    svector<symbol> names;
    expr_ref_vector fv(m);
    ptr_vector<sort> sorts;

    for (unsigned i = 0; i < vars.size(); ++i) {
        fv.push_back(vars.get(i));
        sorts.push_back(m.get_sort(vars.get(i)));
        names.push_back(vars.get(i)->get_decl()->get_name());
    }

    expr_ref tmp(m);
    expr_abstract(m, 0, fv.size(), fv.c_ptr(), f, tmp);
    res = m.mk_exists(sorts.size(), sorts.c_ptr(), names.c_ptr(), tmp, 1);
}

void get_subst(model &model, expr *v, expr *f, expr_ref &res) {
  expr_safe_replace sub(m);
  sub.insert(v, model(v));
  sub(f, res);
}

bool is_sat(expr *a, expr *b = nullptr, expr *c = nullptr) {
  params_ref p;
  ref<solver> sol = mk_smt_solver(m, p, symbol::null);
  sol->assert_expr(a);
  if (b != nullptr)
    sol->assert_expr(b);
  if (c != nullptr)
    sol->assert_expr(c);
  return (sol->check_sat(0, nullptr) != l_false);
}

// computes mbp(pi && sig, model, v)
// input: new_fmls ==> bg && \exist v pi
// output: new_fmls ==> bg && \exists v pi && sig
void lazy_mbp(expr_ref_vector &bg, expr_ref_vector &pi, expr_ref_vector &sig, expr_ref v,
              expr_ref_vector &new_fmls, model &model) {
    expr_ref negged_quant_conj(m);
    negged_quant_conj = m.mk_and(mk_and(pi), mk_and(sig), mk_and(bg));
    if (contains(negged_quant_conj, v)) {
        app_ref_vector vec(m);
        vec.push_back(to_app(v.get()));
        mk_exists(negged_quant_conj, vec, negged_quant_conj);
    }
    negged_quant_conj = m.mk_not(negged_quant_conj);

    expr_ref new_fmls_conj(m), r(m);
    new_fmls_conj = m.mk_and(mk_and(new_fmls), mk_and(bg));

    expr_ref_vector substs(m);
    for (auto f : sig) {
        get_subst(model, v, f, r);
        substs.push_back(r);
    }
    unsigned init_sz = substs.size(); // for stats

    if (!is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj)) {
        new_fmls.append(substs);
        TRACE("bv_tmp", tout << "\nLazy MBP completed. sig size " << init_sz
              << " no substitutions in pi \n";);
        return ;
    }

    expr_ref_vector substs_tmp(m); // backup copy
    substs_tmp.append(substs);

    // todo: possibly, optimize with incremental SMT
    for (auto f : pi) {
        // too weak; add missing substs
        get_subst(model, v, f, r);
        substs.push_back(r);

        if (!is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj))
            break;
    }

    TRACE("bv_tmp", tout << "\nLazy MBP completed. sig size " << init_sz << " substitutions in pi " << substs.size() - init_sz << " and pi size " << pi.size()  << "\n";);
    new_fmls.append(substs);
}

      // project a single variable
      bool operator()(model &model, app *v, app_ref_vector &vars,
                      expr_ref_vector &lits) {
        app_ref_vector vs(m);
        vs.push_back(v);
        project(model, vs, lits, false);
        return vs.empty();
      }

      bool solve(model & model, app_ref_vector & vars, expr_ref_vector & lits) {
        expr_ref_vector sc(m);
        expr_ref res(m), lit_and(m);
        lit_and = mk_and(lits);
        bv_mbp_rw_cfg bvr(m, sc);
        bvr.add_model(&model);
        rewriter_tpl<bv_mbp_rw_cfg> bv_rw(m, false, bvr);
        bv_rw(lit_and.get(), lit_and);
        lits.reset();
        flatten_and(lit_and, lits);
        lits.append(sc);
        return false;
      }
      };

      /**********************************************************/
      /*  bv_project_plugin implementation                     */
      /**********************************************************/
      bv_project_plugin::bv_project_plugin(ast_manager & m) {
        m_imp = alloc(imp, m);
      }

      bv_project_plugin::~bv_project_plugin() { dealloc(m_imp); }

      bool bv_project_plugin::operator()(
          model &model, app *var, app_ref_vector &vars, expr_ref_vector &lits) {
        return (*m_imp)(model, var, vars, lits);
      }

      void bv_project_plugin::operator()(model &model, app_ref_vector &vars,
                                         expr_ref_vector &lits) {
        m_imp->project(model, vars, lits, false);
      }

      vector<def> bv_project_plugin::project(
          model & model, app_ref_vector & vars, expr_ref_vector & lits) {
        return m_imp->project(model, vars, lits, true);
      }

      void bv_project_plugin::set_check_purified(bool check_purified) {
        UNREACHABLE();
      }

      bool bv_project_plugin::solve(model & model, app_ref_vector & vars,
                                    expr_ref_vector & lits) {
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

template class rewriter_tpl<qe::bv_mbp_rw_cfg>;
