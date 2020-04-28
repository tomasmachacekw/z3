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

#include "ast/ast_pp.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/ast_counter.h"
#include "ast/rewriter/rewriter.h"
#include "ast/expr_abstract.h"
#include "cmd_context/cmd_context.h"
#include "model/model_smt2_pp.h"
#include "qe/qe_lia_arith.h"
#include "smt/smt_solver.h"

namespace qe {

struct lia_project_plugin::imp {
  ast_manager &m;
  arith_util u;

  imp(ast_manager &_m) : m(_m), u(m) {}
  ~imp() {}

  bool contains(expr* e, expr* v)
  {
    if (e == v) return true;
    else
    {
      bool found = false;
      for (expr* arg : *to_app(e))
      {
        found |= contains(arg, v);
        if (found) break;
      }
      return found;
    }
  }

  expr* mk_neg(expr* term)
  {
    rational a1;
    if (u.is_mul(term))
    {
      expr_ref_vector ops(m);
      app* ap = to_app(term);
      bool changed = false;
      for (expr* arg : *ap)
      {
        if (!changed && u.is_numeral(arg, a1))
        {
          changed = true;
          if (a1 != -rational(1))
            ops.push_back(u.mk_numeral(-a1, 1));
        }
        else
        {
          ops.push_back(arg);
        }
      }
      if (!changed) ops.push_back(u.mk_int(-1));
      if (ops.size() == 1) return ops.get(0);

      return u.mk_mul(ops.size(), ops.c_ptr());
    }

    if (u.is_numeral(term, a1)) return u.mk_numeral(-a1, 1);
    return u.mk_mul(u.mk_int(-1), term);
  }

  expr* mk_add(expr_ref_vector const& ts)
  {
    switch (ts.size())
    {
      case 0:
        return u.mk_int(0);
      case 1:
        return ts.get(0);
      default:
        return u.mk_add(ts.size(), ts.c_ptr());
    }
  }

  expr* mk_and(expr_ref_vector const& ts)
  {
    switch (ts.size())
    {
      case 0:
        return m.mk_true();
      case 1:
        return ts.get(0);
      default:
        return m.mk_and(ts.size(), ts.c_ptr());
    }
  }

  expr* mk_exists(expr* f, app_ref_vector& vars)
  {
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
    return m.mk_exists(sorts.size(), sorts.c_ptr(), names.c_ptr(), tmp, 1);
  }

  void add_num(rational r, expr_ref_vector &ops)
  {
    bool changed = false;
    for (unsigned i = 0; i < ops.size(); i++)
    {
      rational a1;
      if (u.is_numeral(ops.get(i), a1))
      {
        changed = true;
        if (a1+r == rational(0)) ops.erase(i);
        else ops.set(i, u.mk_numeral(a1+r, 1));
        break;
      }
    }
    if (!changed) ops.push_back(u.mk_numeral(r, 1));
  }

  void split(expr* var, expr* term, expr_ref_vector& v, expr_ref_vector& e, bool positive)
  {
    if (u.is_add(term))
    {
      for (expr* arg : *to_app(term)) split(var, arg, v, e, positive);
      return;
    }

    expr* e1, *e2;
    if (u.is_sub(term, e1, e2)) {
      split(var, e1, v, e, positive);
      split(var, e2, v, e, !positive);
      return;
    }

    if (positive)
    {
      if (contains(term, var))
      {
        e.push_back(term);
      }
      else
      {
        v.push_back(term);
      }
    }
    else
    {
      if (contains(term, var))
      {
        e.push_back(mk_neg(term));
      }
      else
      {
        v.push_back(mk_neg(term));
      }
    }
  }

  bool is_positive(expr* term, expr*& e)
  {
    rational a1;
    bool positive = true;
    if (u.is_mul(term))
    {
      expr_ref_vector ops(m);
      app* ap = to_app(term);
      for (expr* arg : *ap)
      {
        if (u.is_numeral(arg, a1) && a1 < rational(0))
        {
          positive = !positive;
          if (a1 != -rational(1))
            ops.push_back(u.mk_numeral(-a1, 1));
        }
        else
        {
          ops.push_back(arg);
        }
      }

      if (ops.size() == 1) e = ops.get(0);
      else e = u.mk_mul(ops.size(), ops.c_ptr());
      return positive;
    }
    return true;
  }

  // MAIN PROJECTION FUNCTION
  // if compute_def is true, return witnessing definitions
  vector<def> project(model &model, app_ref_vector &vars, expr_ref_vector &fmls,
                      bool compute_def)
  {
    expr_ref_vector fmls_tmp(m); // backup
    fmls_tmp.append(fmls);

    for (unsigned var_num = 0; var_num < vars.size(); var_num++)
    {
      expr* v = vars.get(var_num);
      TRACE("qe", tout << "eliminate " << mk_pp(v, m) << "\n";);

      expr_ref_vector new_fmls(m);
      expr_ref_vector old_fmls_1(m);
      expr_ref_vector old_fmls_2(m);
      expr_ref_vector backg_fmls(m);
      expr_ref_vector normalized(m);
      expr_ref_vector substs(m);
      vector<rational> coeffs;
      vector<bool> dirs;

      for (unsigned f_num = 0; f_num < fmls.size(); f_num++)
      {
        expr* f = fmls.get(f_num);
        expr* e1, *e2, *e3, *e4;

        bool all_good = u.is_int(v); // for others (e.g., reals), should just do subst -- to improve

        if (!contains(f, v))
        {
          backg_fmls.push_back(f);
          continue;
        }

        expr_ref_vector all(m);
        expr_ref_vector apps(m);
        expr* e;
        bool dir;
        rational r;

        if (u.is_le(f, e1, e2) || u.is_ge(f, e2, e1) ||
           (m.is_not(f, e3) && (u.is_gt(e3, e1, e2) || u.is_lt(e3, e2, e1))))
        {
          split(v, e1, all, apps, 1);
          split(v, e2, all, apps, 0);

          if (apps.size() > 1)
          {
            all_good = false;
          }
          else
          {
            e = apps.get(0);
            dir = is_positive(e, e4);
            if (dir)
            {
              for (unsigned i = 0; i < all.size(); i++) all.set(i, mk_neg(all.get(i)));
            }
            else
            {
              add_num(rational(-1), all);
              e = e4;
            }
          }
        }

        else if (u.is_lt(f, e1, e2) || u.is_gt(f, e2, e1) ||
            (m.is_not(f, e3) && (u.is_ge(e3, e1, e2) || u.is_le(e3, e2, e1))))
        {
          split(v, e1, all, apps, 1);
          split(v, e2, all, apps, 0);

          if (apps.size() > 1)
          {
            all_good = false;
          }
          else
          {
            e = apps.get(0);
            dir = is_positive(e, e4);
            if (dir)
            {
              for (unsigned i = 0; i < all.size(); i++) all.set(i, mk_neg(all.get(i)));
              add_num(rational(-1), all);
            }
            else
            {
              e = e4;
            }
          }
        }

        else if (m.is_eq(f, e1, e2) && u.is_int(e1))
        {
          fmls.push_back(u.mk_le(e1, e2));
          fmls.push_back(u.mk_ge(e1, e2));
          continue;
        }
        else
        {
          all_good = false;
        }

        if (all_good && normalize(v, e, all, rational(1), r, dir))
        {
          normalized.push_back(mk_add(all));
          dirs.push_back(dir);
          coeffs.push_back(r);

          // sanity check
          TRACE("qe",
            expr_ref new_f(m);
            new_f = dir ? u.mk_le(e, mk_add(all)) : u.mk_gt(e, mk_add(all));
            if (is_sat(m.mk_or(m.mk_and(f, m.mk_not(new_f)), m.mk_and(new_f, m.mk_not(f)))))
            {
              tout << "  failed conversion (sanity) [ " << r << "]: " << mk_pp(f,m) << "\n      >>>     " << mk_pp(new_f,m) << "\n";
            });
          old_fmls_1.push_back(f);
        }
        else
        {
          substs.push_back(get_subst(model, v, f));
          old_fmls_2.push_back(f);
        }
      }

      resolve(model, coeffs, normalized, dirs, new_fmls);

      if (!substs.empty())       // iterative weakening of subst
      {
        expr_ref negged_quant_conj(m);
        negged_quant_conj = m.mk_and(mk_and(old_fmls_1), mk_and(old_fmls_2));
        if (contains(negged_quant_conj, v))
        {
          app_ref_vector vec(m);
          vec.push_back(vars.get(var_num));
          negged_quant_conj = mk_exists(negged_quant_conj, vec);
        }
        negged_quant_conj = m.mk_not(negged_quant_conj);

        expr_ref new_fmls_conj(m);
        new_fmls_conj = mk_and(new_fmls);

        unsigned init_sz = substs.size(); // for stats
        unsigned stren_sz = init_sz;

        if (is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj))
        {
          for (auto & f : old_fmls_1)     // too weak; add missing substs
          {
            expr_ref new_subst = get_subst(model, v, f);
            substs.push_back(new_subst);
          }
          stren_sz = substs.size();
        }

        expr_ref_vector substs_tmp(m); // backup copy
        substs_tmp.append(substs);

        // todo: possibly, optimize with incremental SMT
        for (unsigned k = 0; k < substs.size(); )
        {
          expr_ref_vector tmp(m);
          for (unsigned l = 0; l < substs.size(); l++)
            if (k != l) tmp.push_back(substs.get(l));

          expr_ref tmp_conj(m);
          tmp_conj = mk_and(tmp);

          if (is_sat(new_fmls_conj, tmp_conj, negged_quant_conj)) k++;
          else
          {
            // erase k:
            for (unsigned m = k; m < substs.size() - 1; m++) substs.set(m, substs.get(m+1));
            substs.pop_back();
          }
        }

        unsigned weak_sz = substs.size(); // for stats
        TRACE("qe", tout << "Lazy MBP completed: " << init_sz << " -> " << stren_sz << " -> " << weak_sz << " conjuncts\n";);

        new_fmls.append(substs);
      }

      fmls.reset();
      fmls.append(new_fmls);
      fmls.append(backg_fmls);
    }

    // final sanity check
    expr_ref orig_fla(m);
    orig_fla = mk_exists(mk_and(fmls), vars);
    expr_ref mbp(m);
    mbp = mk_and(fmls);
    if (!model.is_true(mbp) || is_sat(mbp, m.mk_not(orig_fla)))
    {
      TRACE("qe", tout << "  overall MBP sanity failed\n";); // should be unreach
      fmls.reset();
      fmls.append(fmls_tmp);
    }

    return vector<def>();
  }

  expr_ref get_subst(model &model, expr* v, expr* f)
  {
    expr_ref subst(m);
    expr_safe_replace sub(m);
    sub.insert(v, model(v));
    sub(f, subst);
    th_rewriter m_rw(m);
    m_rw(subst);
    return subst;
  }

  bool normalize(expr* var, expr*& head, expr_ref_vector& tail, rational d, rational& r, bool& upper)
  {
    expr* e1, *e2;
    rational d1;

    if (u.is_idiv(head, e1, e2) && u.is_numeral(e2, d1))
    {
      head = e1;
      return normalize(var, head, tail, d*d1, r, upper);
    }
    else
    {
      if (head == var) r = rational(1);
      if (d != rational(1))
      {
        add_num(rational(1), tail);
        expr * tmp = u.mk_mul(u.mk_numeral(d, 1), mk_add(tail));
        tail.reset();
        tail.push_back(tmp);
        tail.push_back(u.mk_int(-1));
      }
      if ((u.is_mul(head, e1, e2) && u.is_numeral(e1, r) && e2 == var) || head == var) return true;
      else if (u.is_add(head))
      {
        expr_ref_vector all(m);
        expr_ref_vector apps(m);

        split(var, head, all, apps, 1);
        if (apps.size() > 1) return false;
        expr * e = apps.get(0);

        for (expr* t : all) tail.push_back(mk_neg(t));

        if (is_positive(e, e1))
        {
          head = e;
          return normalize(var, head, tail, rational(1), r, upper);
        }
        else
        {
          for (unsigned i = 0; i < tail.size(); i++) tail.set(i, mk_neg(tail.get(i)));
          add_num(rational(-1), tail);
          upper = !upper;
          head = e1;
          return normalize(var, head, tail, rational(1), r, upper);
        }
      }
      else // todo: support other constraints, e.g., mod.
      {
        return false;
      }
    }
  }

  void resolve(model &model, vector<rational> &nums, expr_ref_vector& normalized, vector<bool>& dirs,
               expr_ref_vector& new_fmls /* expected to be empty*/, bool order=true)
  {
    rational lcm = rational(1);
    for (auto & r : nums) // naive lcm calculation
    {
      if (lcm % r != 0)
      {
        while (true)
        {
          if (r > lcm) lcm = r;
          else lcm++;
          bool broken = false;
          for (auto & n : nums)
          {
            if (lcm % n != 0)
            {
              broken = true;
              break;
            }
          }
          if (!broken) break;
        }
      }
    }

    expr_ref_vector up(m);
    expr_ref_vector lo(m);

    for (unsigned i = 0; i < dirs.size(); i++)
    {
      if (dirs[i])
      {
        if (lcm == rational(1)) up.push_back(normalized.get(i));
        else
          up.push_back(u.mk_mul(u.mk_numeral(lcm/nums[i], 1), normalized.get(i)));
      }
      else
      {
        if (lcm == rational(1)) lo.push_back(normalized.get(i));
        else
          lo.push_back(u.mk_mul(u.mk_numeral(lcm/nums[i], 1), normalized.get(i)));
      }
    }

    if (up.size() == 0 || lo.size() == 0) return;

    unsigned up_sz = up.size();
    unsigned lo_sz = lo.size();

    if (order) // bounds ordering w.r.t. MBP
    {
      unsigned min_up;
      rational min_up_r;

      for (unsigned i = 0; i < up.size(); i++)
      {
        rational r1;
        if (u.is_numeral(model(up.get(i)), r1))
        {
          if (i == 0 || r1 < min_up_r)
          {
            min_up_r = r1;
            min_up = i;
          }
        }
      }

      unsigned max_lo;
      rational max_lo_r;

      for (unsigned i = 0; i < lo.size(); i++)
      {
        rational r1;
        if (u.is_numeral(model(lo.get(i)), r1))
        {
          if (i == 0 || r1 > max_lo_r)
          {
            max_lo_r = r1;
            max_lo = i;
          }
        }
      }

      for (unsigned i = 0; i < up.size(); i++)
      {
        if (i == min_up) continue;
        expr_ref new_fla(m);
        new_fla = u.mk_le(up.get(min_up), up.get(i));
        new_fmls.push_back(simplify(new_fla));
      }

      for (unsigned i = 0; i < lo.size(); i++)
      {
        if (i == max_lo) continue;
        expr_ref new_fla(m);
        new_fla = u.mk_le(lo.get(i), lo.get(max_lo));
        new_fmls.push_back(simplify(new_fla));
      }

      up.set(0, up.get(min_up));
      lo.set(0, lo.get(max_lo));
      up.resize(1);
      lo.resize(1);
    }

    for (auto & c1 : up)
    {
      for (auto & c2 : lo)
      {
        expr_ref new_fla(m);
        if (lcm == rational(1))
        {
          new_fla = u.mk_gt(c1, c2);
        }
        else
        {
          new_fla = u.mk_gt(u.mk_idiv(c1, u.mk_numeral(lcm, 1)), u.mk_idiv(c2, u.mk_numeral(lcm, 1)));
        }
        new_fmls.push_back(simplify(new_fla));
      }
    }
    TRACE("qe", tout << "resolved: "
          << up_sz << " x " << lo_sz << " = " << new_fmls.size() << "  formulas\n";);
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

  expr_ref simplify(expr_ref e)
  {
    return e;   // gf: very expensive, thus disabled

    expr_ref th_res(m);
    proof_ref pr(m);
    cmd_context m_cmd;

    params_ref p;
    th_rewriter s(m, p);
    s.set_solver(alloc(th_solver, m_cmd));
    s(e, th_res, pr);
    return th_res;
  }

  bool is_sat(expr* a, expr* b = nullptr, expr* c = nullptr)
  {
    params_ref p;
    ref<solver> sol = mk_smt_solver(m, p, symbol::null);
    sol->assert_expr(a);
    if (b != nullptr) sol->assert_expr(b);
    if (c != nullptr) sol->assert_expr(c);
    return (sol->check_sat(0, nullptr) == l_true);
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
  return m_imp->u.get_family_id();
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
