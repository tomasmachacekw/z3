/*++
Copyright (c) 2020

Module Name:

    qe_bv_arith.cpp

Abstract:

    Simple projection function for integer linear arithmetic

Author:

   Arie Gurfinkel
   Grigory Fedyukovich
   Hari Govind

Revision History:

--*/

#include "qe/qe_bv_arith.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/bv_decl_plugin.h" // Tom
#include "ast/for_each_expr.h" // Tom
#include "ast/expr_abstract.h"
#include "ast/rewriter/ast_counter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h" // Tom
#include "ast/rewriter/th_rewriter.h"
#include "cmd_context/cmd_context.h"
#include "qe/qe_mbp.h" // Tom
#include "model/model_smt2_pp.h"
#include "smt/smt_solver.h"

namespace qe {

// contains helper function
bool contains(expr *e, expr *v) {
  if (e == v)
    return true;
  for (expr *arg : *to_app(e))
    if (contains(arg, v))
      return true;
  return false;
}

unsigned contains_num(expr *e, expr *v) {
  if (e == v)
    return 1;
  unsigned count = 0;
  for (expr *arg : *to_app(e))
    count += contains_num(arg, v);
  return count;
}

bool unhandled_legacy(expr *f, expr_ref var) {
    ast_manager &m = var.get_manager();
    bv_util m_bv(m);
    SASSERT(contains(f, var));
    if (is_uninterp(f)) return false;
    if (m_bv.is_bv_sdiv(f) || m_bv.is_bv_udiv(f)) return true;
    if (m_bv.is_bv_smod(f) || m_bv.is_bv_smodi(f) || m_bv.is_bv_smod0(f)) return true;
    if (m_bv.is_bv_urem(f) || m_bv.is_bv_urem0(f) || m_bv.is_bv_uremi(f)) return true;
    if (m_bv.is_extract(f) || m_bv.is_concat(f)) return true;
    for (auto a : *(to_app(f))) {
        if (!contains(a, var)) continue;
        return unhandled_legacy(a, var);
    }
    return false;
}

// smart expression utils
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

void flatten_add_legacy(expr_ref t1, expr_ref_vector& res) {
    ast_manager &m = res.get_manager();
    bv_util m_bv(m);
    if (t1.get() == nullptr) return;
    if (!m_bv.is_bv_add(t1)) {
        res.push_back(t1);
        return;
    }
    rational val, sum = rational::zero();
    unsigned sz = m_bv.get_bv_size(t1.get());
    expr_ref flt(m);
    for (auto arg : *(to_app(t1))) {
        flatten_term(arg, flt);
        if (m_bv.is_numeral(flt, val)) sum = sum + val;
        else
            res.push_back(flt);
    }
    if (!sum.is_zero())
        res.push_back(m_bv.mk_numeral(sum, sz));
}

void flatten_add(expr *t1, expr_ref_vector &res) {
  ast_manager &m = res.get_manager();
  bv_util m_bv(m);
  if (t1 == nullptr)
    return;
  if (!m_bv.is_bv_add(t1)) {
    res.push_back(t1);
    return;
  }
  rational val, sum = rational::zero();
  unsigned sz = m_bv.get_bv_size(t1);
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

// smart expression constructor functions
void mk_add_legacy(expr_ref_vector &f, expr_ref &res) {
  ast_manager &m = res.get_manager();
  bv_util m_bv(m);
  if (f.size() == 1)
    res = f.get(0);
  else if (f.size() != 0)
    res = m.mk_app(m_bv.get_fid(), OP_BADD, f.size(), f.c_ptr());
}

void mk_add(expr_ref_vector &f, expr_ref &res) {
  ast_manager &m = res.get_manager();
  bv_util m_bv(m);
  if (f.size() == 0)
      return;
  expr_ref_vector nw_args(m);
  rational sm = rational::zero(), val;
  unsigned sz = 0;
  for (auto a: f) {
      if (m_bv.is_numeral(a, val)) {
          sz = m_bv.get_bv_size(a);
          sm = sm + val;
      }
      else nw_args.push_back(a);
  }
  if (!sm.is_zero()) {
      expr_ref sm_bv(m);
      sm_bv = m_bv.mk_numeral(sm, sz);
      nw_args.push_back(sm_bv);
  }
  if (nw_args.size() == 1)
      res = nw_args.get(0);
  else
      res = m.mk_app(m_bv.get_fid(), OP_BADD, nw_args.size(), nw_args.c_ptr());
  th_rewriter rw(m);
  rw(res);
}

void mk_add(expr_ref t1, expr_ref t2, expr_ref &res) {
  ast_manager &m = res.get_manager();
  expr_ref_vector f(m);
  flatten_add(t1, f);
  flatten_add(t2, f);
  mk_add(f, res);
}

void mk_add(expr *t1, expr *t2, expr_ref &res) {
  expr_ref_vector f(res.get_manager());
  flatten_add(t1, f);
  flatten_add(t2, f);
  mk_add(f, res);
}

void mk_neg_legacy(expr *f, expr_ref &res) {
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
    }
    else if (m_bv.is_bv_neg(f))
        res = (to_app(f)->get_arg(0));
    else if (m_bv.is_bv_mul(f, t1, t2)) {
        if (m_bv.is_numeral(t1, val) && val == bnd)
            res = t2;
        else if (m_bv.is_numeral(t2, val) && val == bnd)
            res = t1;
        else
            res = m_bv.mk_bv_neg(f);
    }
    else if (m_bv.is_bv_add(f)) {
        expr_ref_vector tmp(m);
        expr_ref tmp1(m);
        for (auto arg : *(to_app(f))) {
            mk_neg(arg, tmp1);
            tmp.push_back(tmp1);
        }
        mk_add(tmp, res);
    }
    else
        res = m_bv.mk_bv_neg(f);
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
        res = m_bv.mk_bv_mul(m_bv.mk_numeral(bnd, sz), f);
}

void mk_mul(expr* a, rational b, expr_ref& res) {
    ast_manager &m = res.get_manager();
    bv_util m_bv(m);
    rational val;
    unsigned sz = m_bv.get_bv_size(a);
    if (b.is_zero()) {
        res = m_bv.mk_numeral(b, sz);
        return;
    }
    if (b.is_one()) {
        res = a;
        return ;
    }
    if (m_bv.is_numeral(a, val)) {
        res = m_bv.mk_numeral(val * b, sz);
        return;
    }
    res = m_bv.mk_bv_mul(m_bv.mk_numeral(b, sz), a);
}

void mk_mul(expr* a, expr* b, expr_ref &c) {
    ast_manager &m(c.get_manager());
    bv_util m_bv(m);
    rational av, bv;
    if (m_bv.is_numeral(a, av) && m_bv.is_numeral(b, bv)) {
        rational cv = av*bv;
        unsigned sz = m_bv.get_bv_size(a);
        c = m_bv.mk_numeral(cv, sz);
        return;
    }
    c = m_bv.mk_bv_mul(a, b);
}

void mk_exists(expr *f, app_ref_vector &vars, expr_ref &res) {
    ast_manager &m = res.get_manager();
    bv_util m_bv(m);
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

// LIA to bv rule utils
bool split(expr *e, expr *var, expr_ref &t1, expr_ref &t2) {
    ast_manager &m(t2.get_manager());
    bv_util m_bv(m);
    if (!m_bv.is_bv_add(e) || !contains(e, var))
        return false;
    expr_ref_vector nw_args(m);
    for (expr *arg : *to_app(e)) {
        if (contains(arg, var))
            t1 = arg;
        else
            nw_args.push_back(arg);
    }
    if (nw_args.size() == 0) return false;
    mk_add(nw_args, t2);
    return true;
}
bool split_exl(expr *e, expr *var, expr_ref &t1, expr_ref &t2) {
  ast_manager &m(t2.get_manager());
  bv_util m_bv(m);
  if (!m_bv.is_bv_add(e) || !contains(e, var))
    return false;
  expr_ref_vector nw_args(m);
  for (expr *arg : *to_app(e)) {
    if (contains(arg, var))
      t2 = arg;
    else
      nw_args.push_back(arg);
  }
  if (nw_args.size() == 0)
    return false;
  mk_add(nw_args, t1);
  return true;
}

// separates lhs, rhs into three parts such that only one contains var
void split_legacy(expr_ref var, expr *lhs, expr *rhs, expr_ref& t1, expr_ref& t2, expr_ref& t2_neg, expr_ref& t3) {
  ast_manager &m = var.get_manager();
  bool lhs_var = contains(lhs, var);
  TRACE("qe", tout << "Trying to split " << mk_pp(lhs, m) << " tilda "
                   << mk_pp(rhs, m) << " wrt var " << var << "\n";);

  if (lhs_var) {
      split_term_legacy(var, lhs, t1, t2, t2_neg);
      t3 = rhs;
  }
  else {
      split_term_legacy(var, rhs, t3, t2, t2_neg);
      t1 = lhs;
  }
  return;
}

// splits exp into terms t and t2 such that exp = t + t2 and t contains var
void split_term_legacy(expr_ref var, expr* exp, expr_ref& t, expr_ref& t2, expr_ref& t2_neg) {
    ast_manager &m = var.get_manager();
    bv_util m_bv(m);
    SASSERT(contains(exp, var));
    if (!m_bv.is_bv_add(exp)) {
        t = exp;
        t2 = m_bv.mk_numeral(rational(0), m_bv.get_bv_size(exp));
        mk_neg(t2, t2_neg);
        return;
    }
    expr_ref neg(m);
    expr_ref_vector t2_vec(m), t2_neg_vec(m);
    bool found = false;
    for (expr *arg : *to_app(exp)) {
        if (contains(arg, var)) {
            SASSERT(!found);
            t = arg;
            found = true;
            continue;
        }
        t2_vec.push_back(arg);
        mk_neg(arg, neg);
        t2_neg_vec.push_back(neg);
    }
    mk_add(t2_neg_vec, t2_neg);
    mk_add(t2_vec, t2);
}


// udiv0, udivi, urem0, uremi handling
void replace_zero_handle_rec(expr* f, model &mdl) {
  ast_manager& m = mdl.get_manager();
  bv_util m_bv(m);
  expr_ref lhs(m), rhs(m), zero(m), exp1(m), exp2(m);
  unsigned sz;
  sz = m_bv.get_bv_size(f);
  zero = m_bv.mk_numeral(rational::zero(), sz);
  if (m_bv.is_bv_urem0(f) || m_bv.is_bv_uremi(f)) {
    exp1 = to_app(lhs)->get_arg(0);
    exp2 = to_app(lhs)->get_arg(1);
    if (!mdl.are_equal(zero, exp2)) {
      f = m_bv.mk_bv_urem(exp1, exp2);
    }
  }
  if (m_bv.is_bv_udiv0(f) || m_bv.is_bv_udivi(f)) {
    exp1 = to_app(lhs)->get_arg(0);
    exp2 = to_app(lhs)->get_arg(1);
    if (!mdl.are_equal(zero, exp2)) {
      f = m_bv.mk_bv_udiv(exp1, exp2);
    }
  }
  unsigned num_arg = to_app(f)->get_num_args();
  for (unsigned i = 0; i < num_arg; i++) {
    replace_zero_handle_rec(to_app(f)->get_arg(i), mdl);
  }
}

void replace_zero_handle_ops(model& mdl, expr_ref_vector& fmls) {
  ast_manager m = mdl.get_manager();
  bv_util m_bv(m);
  for (auto *fml : fmls) {
    if (m_bv.is_bv_sort((m.get_sort(fml))))
      replace_zero_handle_rec(fml, mdl);
  }
}

// rw_rule basic class and utility functions
class rw_rule {
    protected:
        ast_manager &m;
        model_ref m_mdl;
        expr_ref m_var;
        bv_util m_bv;

        expr* create_signed_max(unsigned sz) { // TODO test today
            SASSERT(sz > 0);
            return m_bv.mk_numeral(rational::power_of_two(sz - 1) - 1, sz);
        }

        expr* create_signed_min(unsigned sz) { // TODO test 
            SASSERT(sz > 0);
            return m_bv.mk_bv_neg(m_bv.mk_numeral(rational::power_of_two(sz-1), sz));
        }

        // check for equality and move var to the left
        bool is_eq(expr *e, expr_ref &lhs, expr_ref &rhs) {
          if (!m.is_eq(e))
            return false;
          lhs = to_app(e)->get_arg(0);
          rhs = to_app(e)->get_arg(1);
          bool left_contains = contains(lhs, m_var);
          if (left_contains == contains(rhs, m_var))
            return false;
          if (!left_contains)
            std::swap(lhs, rhs);
          return true;
        }

        // check for diseq, not eq and move var to the left
        bool is_diseq(expr *e, expr_ref &lhs, expr_ref &rhs) {
          expr_ref f(m);
          if (m.is_distinct(e)) {
            lhs = to_app(e)->get_arg(0);
            rhs = to_app(e)->get_arg(1);
          } else if (!is_not(e, f) || !is_eq(f, lhs, rhs))
            return false;
          
          bool left_contains = contains(lhs, m_var);
          if (left_contains == contains(rhs, m_var))
            return false;
          if (!left_contains)
            std::swap(lhs, rhs);
          return true;
        }

        bool is_ule_one_side(expr *e, expr_ref &lhs, expr_ref &rhs) {
          if (!m_bv.is_bv_ule(e))
            return false;
        lhs = to_app(e)->get_arg(0);
        rhs = to_app(e)->get_arg(1);
        if (contains(lhs, m_var) == contains(rhs, m_var))
            return false;
        return true;
        }
        bool is_ule(expr *e, expr_ref &lhs, expr_ref &rhs) {
          if (!m_bv.is_bv_ule(e))
            return false;
          lhs = to_app(e)->get_arg(0);
          rhs = to_app(e)->get_arg(1);
          if (!contains(lhs, m_var) && !contains(rhs, m_var))
            return false;
          return true;
        }
        bool is_sle(expr *e, expr_ref &lhs, expr_ref &rhs) {
          if (!m_bv.is_bv_sle(e))
            return false;
          lhs = to_app(e)->get_arg(0);
          rhs = to_app(e)->get_arg(1);
          if (contains(lhs, m_var) == contains(rhs, m_var))
            return false;
          return true;
        }
        bool is_ult(expr *e, expr_ref &lhs, expr_ref &rhs) {
          if (!m_bv.is_bv_ult(e))
            return false;
          lhs = to_app(e)->get_arg(0);
          rhs = to_app(e)->get_arg(1);
          if (contains(lhs, m_var) == contains(rhs, m_var))
            return false;
          return true;
        }
        bool is_slt(expr *e, expr_ref &lhs, expr_ref &rhs) {
          if (!m_bv.is_bv_slt(e))
            return false;
          lhs = to_app(e)->get_arg(0);
          rhs = to_app(e)->get_arg(1);
          if (contains(lhs, m_var) == contains(rhs, m_var))
            return false;
          return true;
        }

        // TODO check if we need to do contains - prob not
        bool is_udiv(expr* e, expr_ref &exp1, expr_ref &exp2) {
          if (!m_bv.is_bv_udiv(e)) return false;
          exp1 = to_app(e)->get_arg(0);
          exp2 = to_app(e)->get_arg(1);
          if (contains(exp1, m_var) == contains(exp1, m_var))
            return false;
          return true;
        }

        bool is_urem(expr* e, expr_ref &exp1, expr_ref &exp2) {
          if (!m_bv.is_bv_urem(e)) return false;
          exp1 = to_app(e)->get_arg(0);
          exp2 = to_app(e)->get_arg(1);
          if (contains(exp1, m_var) == contains(exp1, m_var))
            return false;
          return true;
        }

        bool is_bvand(expr* e, expr_ref &exp1, expr_ref &exp2) {
          if (!m_bv.is_bv_and(e) || to_app(e)->get_num_args() != 2) return false;
          exp1 = to_app(e)->get_arg(0);
          exp2 = to_app(e)->get_arg(1);
          if (contains(exp1, m_var) == contains(exp1, m_var))
            return false;
          return true;
        }

        bool is_bvor(expr* e, expr_ref &exp1, expr_ref &exp2) {
          if (!m_bv.is_bv_or(e) || to_app(e)->get_num_args() != 2) return false;
          exp1 = to_app(e)->get_arg(0);
          exp2 = to_app(e)->get_arg(1);
          if (contains(exp1, m_var) == contains(exp1, m_var))
            return false;
          return true;
        }

        bool is_add(expr* e, expr_ref &exp1, expr_ref &exp2) {
          if (!m_bv.is_bv_add(e)) return false;
          exp1 = to_app(e)->get_arg(0);
          exp2 = to_app(e)->get_arg(1);
          if (contains(exp1, m_var) == contains(exp1, m_var))
            return false;
          return true;
        }

        bool is_mul(expr* e, expr_ref &exp1, expr_ref &exp2) {
          if (!m_bv.is_bv_mul(e)) return false;
          exp1 = to_app(e)->get_arg(0);
          exp2 = to_app(e)->get_arg(1);
          if (contains(exp1, m_var) == contains(exp1, m_var))
            return false;
          return true;
        }

        bool is_not(expr* e, expr_ref &exp1) {
          if (!m.is_not(e)) return false;
          exp1 = to_app(e)->get_arg(0);
          return true;
        }
        // TODO add same for other bv operations
        expr* mk_bvand(expr* a, expr* b) {
          expr* args[2];
          args[0] = a;
          args[1] = b;
          return m.mk_app(m_bv.get_family_id(), OP_BAND, 2, args);
        }

        expr* mk_bvor(expr* a, expr* b) {
          expr* args[2];
          args[0] = a;
          args[1] = b;
          return m.mk_app(m_bv.get_family_id(), OP_BOR, 2, args);
        }

public:
    rw_rule(ast_manager& m): m(m), m_var(m), m_bv(m) {}
    void reset(model *mdl, expr *x) {
      m_var = x;
      m_mdl = mdl;
    }
    virtual bool apply(expr *exp, expr_ref_vector &out) = 0;
};

// start of LIA bv rules
class sle1 : public rw_rule {
  // a <= 2^(n - 1) - 1 && b <= 2^(n - 1) - 1 && a <= b ==> a <=_s b
public:
    sle1 (ast_manager &m): rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
      expr_ref lhs(m), rhs(m);
      if (!is_sle(e, lhs, rhs))
        return false;
      unsigned sz = m_bv.get_bv_size(lhs);
      expr_ref bnd(m), b1(m), b2(m), rw(m);
      bnd = create_signed_max(sz);
      b1 = m_bv.mk_ule(lhs, bnd);
      b2 = m_bv.mk_ule(rhs, bnd);
      rw = m_bv.mk_ule(lhs, rhs);
      if (m_mdl->is_true(b1) && m_mdl->is_true(b2) && m_mdl->is_true(rw)) {
        out.push_back(b1);
        out.push_back(b2);
        out.push_back(rw);
        return true;
      }
      return false;
    }
};

class sle2 : public rw_rule {
  // a >= 2^(n - 1) && b >= 2^(n - 1) && a <= b ==> a <=_s b
public:
  sle2(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_sle(e, lhs, rhs))
      return false;
    unsigned sz = m_bv.get_bv_size(lhs);
    expr_ref bnd(m), b1(m), b2(m), rw(m);
    bnd = m_bv.mk_numeral(rational::power_of_two(sz - 1), sz);
    b1 = m_bv.mk_ule(bnd, lhs);
    b2 = m_bv.mk_ule(bnd, rhs);
    rw = m_bv.mk_ule(lhs, rhs);
    if (m_mdl->is_true(b1) && m_mdl->is_true(b2) && m_mdl->is_true(rw)) {
      out.push_back(b1);
      out.push_back(b2);
      out.push_back(rw);
      return true;
    }
    return false;
  }
};

class sle3 : public rw_rule {
  // a >= 2^(n - 1) && b <= 2^(n - 1) - 1 ==> a <=_s b
public:
  sle3(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_sle(e, lhs, rhs))
      return false;
    unsigned sz = m_bv.get_bv_size(lhs);
    expr_ref bnd1(m), b1(m), b2(m), bnd2(m);
    bnd1 = create_signed_max(sz);
    bnd2 = m_bv.mk_numeral(rational::power_of_two(sz - 1), sz);
    b1 = m_bv.mk_ule(bnd2, lhs);
    b2 = m_bv.mk_ule(rhs, bnd1);
    if (m_mdl->is_true(b1) && m_mdl->is_true(b2)) {
      out.push_back(b1);
      out.push_back(b2);
      return true;
    }
    return false;
  }
};

class eq : public rw_rule {
  // a <= b && b <= a ==> a = b
public:
  eq(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    expr_ref b1(m), b2(m);
    if (!(is_eq(e, lhs, rhs) &&
          (contains(lhs, m_var) || contains(rhs, m_var))))
      return false;
    b1 = m_bv.mk_ule(rhs, lhs);
    b2 = m_bv.mk_ule(lhs, rhs);
    if (m_mdl->is_true(b1) && m_mdl->is_true(b2)) {
      out.push_back(b1);
      out.push_back(b2);
      return true;
    }
    return false;
  }
};

class neq1 : public rw_rule {
  // a < b ==> a != b
public:
  neq1(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr *f, *lhs, *rhs;
    if (!(m.is_not(e, f) && m.is_eq(f, lhs, rhs) &&
          (contains(lhs, m_var) || contains(rhs, m_var))))
      return false;
    expr_ref b1(m);
    b1 = m.mk_not(m_bv.mk_ule(rhs, lhs));
    if (m_mdl->is_true(b1)) {
      out.push_back(b1);
      return true;
    }
    return false;
  }
};

class neq2 : public rw_rule {
  // a > b ==> a != b
public:
  neq2(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr *f, *lhs, *rhs;
    if (!((m.is_not(e, f)) && m.is_eq(f, lhs, rhs) &&
          (contains(lhs, m_var) || contains(rhs, m_var))))
      return false;
    expr_ref b1(m), nt(m);
    nt = m_bv.mk_ule(lhs, rhs);
    b1 = m.mk_not(nt);
    if (m_mdl->is_true(b1)) {
      out.push_back(b1);
      return true;
    }
    return false;
  }
};

class nule : public rw_rule {
  // b <= a - 1 /\ 1 <= a ==> not(a <= b)
public:
  nule(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref f(m), lhs(m), rhs(m), h1(m), h2(m);
    if (!((is_not(e, f)) && is_ule(f, lhs, rhs) &&
          (contains(lhs, m_var) || contains(rhs, m_var))))
      return false;
    unsigned sz = m_bv.get_bv_size(lhs); // TOM
    expr_ref mone(m), dff(m), one(m);
    one = m_bv.mk_numeral(rational::one(), sz);
    mk_neg(one, mone);
    mk_add(lhs, mone, dff);
    h1 = m_bv.mk_ule(rhs, dff);
    h2 = m_bv.mk_ule(one, lhs);
    if (m_mdl->is_true(h1) && m_mdl->is_true(h2)) {
      out.push_back(h1);
      out.push_back(h2);
      return true;
    }
    return false;
  }
};

class nsle : public rw_rule {
  // b <=_s a - 1 /\ -2^(n - 1) + 1 <=_s a ==> not(a <=_s b)
public:
  nsle(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr *f, *lhs, *rhs;
    if (!((m.is_not(e, f)) && m_bv.is_bv_sle(f, lhs, rhs) &&
          (contains(lhs, m_var) || contains(rhs, m_var)))) {
      return false;
    }
    unsigned sz = m_bv.get_bv_size(lhs);
    expr_ref bnd(m);
    bnd = m_bv.mk_numeral((-1 * rational::power_of_two(sz - 1)) + 1, sz);
    expr_ref mone(m), dff(m), b1(m), b2(m);
    mone = m_bv.mk_numeral(rational::minus_one(), sz);
    mk_add(lhs, mone, dff);
    b1 = m_bv.mk_sle(bnd, lhs);
    b2 = m_bv.mk_sle(rhs, dff);
    if (m_mdl->is_true(b1) && m_mdl->is_true(b2)) {
      out.push_back(b1);
      out.push_back(b2);
      return true;
    }
    return false;
  }
};

class mul_mone1 : public rw_rule {
  //-1*b <= a ==> -1*a <= b
public:
    mul_mone1(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) override {
      expr_ref lhs(m), rhs(m), nw_lhs(m);
      expr *l1, *l2;
      rational val;
      if (!is_ule_one_side(e, lhs, rhs))
        return false;
      if (!(contains(lhs, m_var) && m_bv.is_bv_mul(lhs, l1, l2) && l2 == m_var))
        return false;
      unsigned sz = m_bv.get_bv_size(lhs);
      if (!(m_bv.is_numeral(l1, val) &&
            (val.is_minus_one() || (val == rational::power_of_two(sz) - 1))))
        return false;
      mk_mul(l1, rhs, nw_lhs);
      expr_ref b1(m);
      b1 = m_bv.mk_ule(nw_lhs, l2);
      if (m_mdl->is_true(b1)) {
        out.push_back(b1);
        return true;
      }
      return false;
    }
};

class mul_mone2 : public rw_rule {
  //a <= -1*b ==> b <= -1*a
public:
  mul_mone2(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), nw_rhs(m);
    expr *l1, *l2;
    rational val;
    if (!is_ule_one_side(e, lhs, rhs))
      return false;
    if (!(contains(rhs, m_var) && m_bv.is_bv_mul(rhs, l1, l2) && l2 == m_var))
      return false;
    unsigned sz = m_bv.get_bv_size(lhs);
    if (!(m_bv.is_numeral(l1, val) && (val.is_minus_one() || (val == rational::power_of_two(sz) - 1))))
        return false;
    mk_mul(l1, lhs, nw_rhs);
    expr_ref b1(m);
    b1 = m_bv.mk_ule(l2, nw_rhs);
    if (m_mdl->is_true(b1)) {
        out.push_back(b1);
        return true;
    }
    return false;
  }
};

class ule_zro : public rw_rule {
  // b = 0 ==> b <= x
public:
  ule_zro(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m);
    rational val;
    if (!m_bv.is_bv_ule(e)) return false;
    lhs = to_app(e)->get_arg(0);

    if (m_bv.is_numeral(lhs, val) && val.is_zero())
        return true;
    return false;
  }
};

class addl1: public rw_rule {
  //if {y <= z /\ f(x) <= z - y} then {f(x) + y <= z}
public:
    addl1 (ast_manager& m): rw_rule(m){}
    bool apply(expr *e, expr_ref_vector &out) override {
      expr_ref lhs(m), rhs(m), oth(m), rw(m);
      if (!is_ule_one_side(e, lhs, rhs))
        return false;
      expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
      if (!split(lhs, m_var, t1, t2))
        return false;
      mk_neg(t2, t2_neg);
      oth = m_bv.mk_ule(t2, rhs);
      mk_add(rhs, t2_neg, add_t);
      rw = m_bv.mk_ule(t1, add_t);
      if (m_mdl->is_true(oth) && m_mdl->is_true(rw)) {
        out.push_back(oth);
        out.push_back(rw);
        return true;
      }
      return false;
    };
};

class addl2: public rw_rule {
  // if {-y <= f(x) /\ f(x) <= z - y} then {f(x) + y <= z}
public:
  addl2 (ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), oth(m), rw(m);
    if (!is_ule_one_side(e, lhs, rhs))
      return false;
    expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
    if (!split(lhs, m_var, t1, t2))
      return false;
    mk_neg(t2, t2_neg);
    oth = m_bv.mk_ule(t2_neg, t1);
    mk_add(rhs, t2_neg, add_t);
    rw = m_bv.mk_ule(t1, add_t);
    if (m_mdl->is_true(oth) && m_mdl->is_true(rw)) {
      out.push_back(oth);
      out.push_back(rw);
      return true;
    }
    return false;
  };
};

class addl3 : public rw_rule {
  // if {-y <= f(x) /\ y <= z /\ y != 0} then {f(x) + y <= z}
public:
  addl3(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), sc1(m), sc2(m), zro(m), sc3(m);
    if (!is_ule_one_side(e, lhs, rhs))
      return false;
    expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
    if (!split(lhs, m_var, t1, t2))
      return false;
    mk_neg(t2, t2_neg);
    sc1 = m_bv.mk_ule(t2_neg, t1);
    sc2 = m_bv.mk_ule(t2, rhs);
    unsigned sz = m_bv.get_bv_size(rhs);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    sc3 = m.mk_not(m.mk_eq(t2, zro));
    if (m_mdl->is_true(sc1) && m_mdl->is_true(sc2) && m_mdl->is_true(sc3)) {
      out.push_back(sc1);
      out.push_back(sc2);
      out.push_back(sc3);
      return true;
    }
    return false;
  };
};

class addbx4 : public rw_rule {
  // if {x <= 2^n/k2/k1} then {k1*x <= k2*x}
  // TODO: handle other cases as well
public:
  addbx4(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), nw_rhs(m), bnd_e(m), sc1(m);
    if (!is_ule(e, lhs, rhs))
      return false;
    expr *k1_e, *k2_e, *var;
    rational k1, k2;
    if (!m_bv.is_bv_mul(lhs, k1_e, var)) return false;
    if (var != m_var) return false;
    if (!m_bv.is_numeral(k1_e, k1)) return false;

    if (!m_bv.is_bv_mul(rhs, k2_e, var)) return false;
    if (var != m_var) return false;
    if (!m_bv.is_numeral(k2_e, k2)) return false;
    if (k1 == k2) return true;
    rational k3 = k2/k1;
    unsigned sz = m_bv.get_bv_size(m_var);
    rational bnd = rational::power_of_two(sz)/k3;
    bnd_e = m_bv.mk_numeral(bnd, sz);
    sc1 = m_bv.mk_ule(m_var, bnd_e);
    if (m_mdl->is_true(sc1)) {
      out.push_back(sc1);
      return true;
    }
    TRACE("bv_tmp", tout << "model not good enough for bx4 " << mk_pp(sc1, m) << "\n";);
    return false;
  };
};

class addbx1 : public rw_rule {
  // if {f1(x) <= f2(x) /\ y <= f2(x) - f1(x)} then {f1(x) + y <= f2(x)}
public:
  addbx1(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), nw_rhs(m), sc1(m), rw(m);
    if (!is_ule(e, lhs, rhs))
      return false;
    expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
    if (!split_exl(lhs, m_var, t1, t2))
      return false;
    mk_neg(t2, t2_neg);
    sc1 = m_bv.mk_ule(t2, rhs);
    mk_add(rhs, t2_neg, nw_rhs);
    rw = m_bv.mk_ule(t1, nw_rhs);
    TRACE("bv_tmp",
          tout << "checking mdl bx1 with " << mk_pp(sc1, m)<< " and " << mk_pp(rw, m) << "\n";);
    if (m_mdl->is_true(sc1) && m_mdl->is_true(rw)) {
      out.push_back(sc1);
      out.push_back(rw);
      return true;
    }
    TRACE("bv_tmp", tout << "checking mdl bx1 with " << mk_pp(sc1, m) << " and "
                         << mk_pp(rw, m) << "\n";);
    return false;
  };
};

class addbx2 : public rw_rule {
  // if {-f1(x) <= y /\ y <= f2(x) - f1(x)} then {f1(x) + y <= f2(x)}
public:
  addbx2(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), nw_rhs(m), rw(m), sc1(m);
    if (!is_ule(e, lhs, rhs))
      return false;
    expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
    if (!split_exl(lhs, m_var, t1, t2))
      return false;
    mk_neg(t2, t2_neg);
    sc1 = m_bv.mk_ule(t2_neg, t1);
    mk_add(rhs, t2_neg, nw_rhs);
    rw = m_bv.mk_ule(t1, nw_rhs);
    TRACE("bv_tmp", tout << "checking mdl bx2 with " << mk_pp(sc1, m) << " and "
                         << mk_pp(rw, m) << "\n";);
    if (m_mdl->is_true(sc1) && m_mdl->is_true(rw)) {
      out.push_back(sc1);
      out.push_back(rw);
      return true;
    }
    return false;
  };
};

class addbx3 : public rw_rule {
  // if {-f1(x) <= y /\ f1(x) <= f2(x) /\ f1(x) != 0} then {f1(x) + y <= f2(x)}
public:
  addbx3(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), nw_rhs(m), sc1(m), sc2(m), sc3(m), zro(m);
    if (!is_ule(e, lhs, rhs))
      return false;
    expr_ref t1(m), t2(m), t2_neg(m), add_t(m);
    if (!split_exl(lhs, m_var, t1, t2))
      return false;
    mk_neg(t2, t2_neg);
    sc1 = m_bv.mk_ule(t2_neg, t1);
    sc2 = m_bv.mk_ule(t2, rhs);
    unsigned sz = m_bv.get_bv_size(t2);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    sc3 = m.mk_not(m.mk_eq(t2, zro));

    TRACE("bv_tmp", tout << "checking mdl bx3 with " << mk_pp(sc1, m) << " and "
                         << mk_pp(sc2, m) << "\n";);
    if (m_mdl->is_true(sc1) && m_mdl->is_true(sc2) && m_mdl->is_true(sc3)) {
      out.push_back(sc1);
      out.push_back(sc2);
      out.push_back(sc3);
      return true;
    }
    return false;
  };
};

class addr1 : public rw_rule {
  // if {z <= y - 1 /\ y != 0 /\ z - y <= f(x)} then {z <= f(x) + y}
public:
  addr1(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ule(e, lhs, rhs))
      return false;
    expr_ref t1(m), t2(m), t2_neg(m);
    if (!split(rhs, m_var, t1, t2))
      return false;
    mk_neg(t2, t2_neg);
    unsigned sz = m_bv.get_bv_size(t2);
    expr_ref one(m), minus_one(m), zro(m), add_t1(m), add_mo(m), oth(m),
        no_zro(m);
    one = m_bv.mk_numeral(rational::one(), sz);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    mk_neg(one, minus_one);
    mk_add(t2, minus_one, add_mo);
    oth = m_bv.mk_ule(lhs, add_mo);
    no_zro = m.mk_not(m.mk_eq(t2, zro));
    mk_add(lhs, t2_neg, add_t1);
    expr *rw = m_bv.mk_ule(add_t1, t1);
    if (m_mdl->is_true(oth) && m_mdl->is_true(rw) && m_mdl->is_true(no_zro)) {
      out.push_back(oth);
      out.push_back(no_zro);
      out.push_back(rw);
      return true;
    }
    return false;
  };
};

class addr2 : public rw_rule {
  // if { f(x) <= -y - 1 /\ y != 0  /\ z - y <= f(x)} then { z <= f(x) + y}
public:
  addr2(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ule(e, lhs, rhs)) return false;
    expr_ref t1(m), t2(m), t2_neg(m);
    if (!split(rhs, m_var, t1, t2)) return false;
    mk_neg(t2, t2_neg);
    unsigned sz = m_bv.get_bv_size(t2);
    expr_ref one(m), minus_one(m), zro(m), add_t2(m), add_lhs(m), rw(m), oth(m),
        no_zro(m);
    one = m_bv.mk_numeral(rational::one(), sz);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    mk_neg(one, minus_one);
    mk_add(t2_neg, minus_one, add_t2);
    oth = m_bv.mk_ule(t1, add_t2);
    no_zro = m.mk_not(m.mk_eq(t2, zro));
    mk_add(lhs, t2_neg, add_lhs);
    rw = m_bv.mk_ule(add_lhs, t1);
    if (m_mdl->is_true(oth) && m_mdl->is_true(rw) && m_mdl->is_true(no_zro)) {
        out.push_back(oth);
        out.push_back(no_zro);
        out.push_back(rw);
        return true;
    }
    return false;
  };
};

class addr3 : public rw_rule {
  // if { y == 0  /\ z <= f(x)} then { z <= f(x) + y}
public:
  addr3(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ule(e, lhs, rhs))
      return false;
    expr_ref t1(m), t2(m);
    if (!split(rhs, m_var, t1, t2))
      return false;
    unsigned sz = m_bv.get_bv_size(t2);
    expr_ref zro(m), oth(m), t2_zro(m);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    oth = m_bv.mk_ule(lhs, t1);
    t2_zro = m.mk_eq(t2, zro);
    if (m_mdl->is_true(t2_zro) && m_mdl->is_true(oth)) {
      out.push_back(oth);
      out.push_back(t2_zro);
      return true;
    }
    return false;
  };
};

class addr4 : public rw_rule {
  // if { y != 0  /\ z <= y - 1 && x <= -y - 1 } then { z <= f(x) + y}
public:
  addr4(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ule(e, lhs, rhs))
      return false;
    expr_ref t1(m), t2(m), t2_neg(m);
    if (!split(rhs, m_var, t1, t2))
      return false;
    mk_neg(t2, t2_neg);
    unsigned sz = m_bv.get_bv_size(t2);
    expr_ref one(m), zro(m), mone(m), add_t2(m), add_negt2(m), t2_zro(m),
        oth(m), oth2(m);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    mone = m_bv.mk_numeral(rational::minus_one(), sz);
    mk_add(t2, mone, add_t2);
    mk_add(t2_neg, mone, add_negt2);
    t2_zro = m.mk_not(m.mk_eq(t2, zro));
    oth = m_bv.mk_ule(lhs, add_t2);
    oth2 = m_bv.mk_ule(t1, add_negt2);
    if (m_mdl->is_true(t2_zro) && m_mdl->is_true(oth) && m_mdl->is_true(oth2)) {
      out.push_back(oth);
      out.push_back(oth2);
      out.push_back(t2_zro);
      return true;
    }
    return false;
  };
};

// end of BV rules based on LIA
// start of Invertibility condition rules
// Solve basic rules x ?? t, -x ?? t, ~x ?? t, x+s ?? t 
// for ?? in <u, <s, (prob later add ≤u, ≤s) TODO

class inv_ineq_basic_op : public rw_rule {
  public :
    inv_ineq_basic_op(ast_manager &m) : rw_rule(m) {}
    bool apply(expr *e, expr_ref_vector &out) {
      if (contains_num(e, m_var) != 1) {
        return false;
      }
      expr_ref lhs(m), rhs(m), res(m), exp1(m), exp2(m), zero(m);
      unsigned sz = m_bv.get_bv_size(m_var);
      zero = m_bv.mk_numeral(rational::zero(),sz);
      if (is_ult(e, rhs, lhs)) {
        if (lhs == m_var || ((m_bv.is_bv_neg(lhs) || 
        m_bv.is_bv_not(lhs)) && to_app(lhs)->get_arg(0) == m_var) ||
        (is_add(lhs, exp1, exp2) && (exp1 == m_var || exp2 == m_var))) {
          res = m_bv.mk_diseq(zero,rhs);
          out.push_back(res);
          SASSERT(m_mdl->is_true(out.back()));
          return true;
        }
        if (rhs == m_var || ((m_bv.is_bv_neg(rhs) || 
        m_bv.is_bv_not(rhs)) && to_app(rhs)->get_arg(0) == m_var) ||
        (is_add(rhs, exp1, exp2) && (exp1 == m_var || exp2 == m_var))) {
          res = m_bv.mk_diseq(m_bv.mk_bv_not(zero),lhs);
          out.push_back(res);
          SASSERT(m_mdl->is_true(out.back()));
          return true;
        }
      }
      if (is_slt(e, lhs, rhs)) {
        if (lhs == m_var || ((m_bv.is_bv_neg(lhs) || 
        m_bv.is_bv_not(lhs)) && to_app(lhs)->get_arg(0) == m_var) ||
        (is_add(lhs, exp1, exp2) && (exp1 == m_var || exp2 == m_var))) {
          res = m_bv.mk_diseq(create_signed_min(sz),rhs);
          out.push_back(res);
          SASSERT(m_mdl->is_true(out.back()));
          return true;
        }
        if (rhs == m_var || ((m_bv.is_bv_neg(rhs) || 
        m_bv.is_bv_not(rhs)) && to_app(rhs)->get_arg(0) == m_var) ||
        (is_add(rhs, exp1, exp2) && (exp1 == m_var || exp2 == m_var))) {
          res = m_bv.mk_diseq(lhs, create_signed_max(sz));
          out.push_back(res);
          SASSERT(m_mdl->is_true(out.back()));
          return true;
        }
      }
      // we are losing a lot of info here, should do something about it - TODO
      if (m_bv.is_bv_ule(e) || m_bv.is_bv_sle(e)) {
          out.push_back(m.mk_true());
          return true;
      }
      return false;
    }
};

// ---------- EQ ---------

class inv_eq_mul : public rw_rule {
public:
  inv_eq_mul(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_eq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if (-s | s) & t = t then  Exists x. x * s = t
    if (is_mul(lhs, exp1, exp2)) {
        if (exp1 == m_var) {
          std::swap(exp1, exp2);
        }
        if (exp2 == m_var) {
          mk_neg(exp1, h1);
          h2 = mk_bvor(h1, exp1);
          h3 = mk_bvand(h2, rhs);
          h4 = m_bv.mk_eq(h3, rhs);
          out.push_back(h4);
          SASSERT(m_mdl->is_true(out.back()));
          return true;
        }
    }
    return false;
  }
};

class inv_eq_urem : public rw_rule {
public:
  inv_eq_urem(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_eq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), two(m);
    if (is_urem(lhs, exp1, exp2)) {
      //  if t ≤u ~-s then  Exists x. x mod_u s = t
      if (exp1 == m_var) {
        mk_neg(exp2, h1);
        h2 = m_bv.mk_bv_not(h1);
        h3 = m_bv.mk_ule(rhs, h2);
        out.push_back(h3);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
      //  if t ≤u (t+t-s) & s then  Exists x. s mod_u x = t
      if (exp2 == m_var) {
        unsigned sz = m_bv.get_bv_size(m_var);
        two = m_bv.mk_numeral(rational(2), sz);
        mk_mul(rhs, two, h1);
        h2 = m_bv.mk_bv_sub(h1, exp1);
        h3 = mk_bvand(h2, exp1);
        h4 = m_bv.mk_ule(rhs, h3);
        out.push_back(h4);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

class inv_eq_udiv : public rw_rule {
public:
  inv_eq_udiv(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_eq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    if (is_udiv(lhs, exp1, exp2)) {
      //  if (s*t) udiv s = t then  Exists x. x udiv s = t
      if (exp1 == m_var) {
        mk_mul(exp2, rhs, h1);
        h2 = m_bv.mk_bv_udiv(h1, exp2);
        h3 = m_bv.mk_eq(h2, rhs);
        out.push_back(h3);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
      //  if s udiv (s udiv t) = t then  Exists x. s udiv x = t
      if (exp2 == m_var) {
        h1 = m_bv.mk_bv_udiv(exp1, rhs);
        h2 = m_bv.mk_bv_udiv(exp1, h1);
        h3 = m_bv.mk_eq(h2, rhs);
        out.push_back(h3);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};


class inv_eq_bvand : public rw_rule {
public:
  inv_eq_bvand(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_eq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if t & s = t then Exists x. x & s = t
    if (is_bvand(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h1 = mk_bvand(exp1, rhs);
        h2 = m_bv.mk_eq(h1, rhs);
        out.push_back(h2);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

class inv_eq_bvor : public rw_rule {
public:
  inv_eq_bvor(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_eq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if t | s = t then Exists x. x | s = t
    if (is_bvor(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h1 = mk_bvor(exp1, rhs);
        h2 = m_bv.mk_eq(h1, rhs);
        out.push_back(h2);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

// ---------- DISEQ ---------

class inv_diseq_mul : public rw_rule {
public:
  inv_diseq_mul(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_diseq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    //  if s \= 0 V t \= 0 then  Exists x. x * s \= t
    if (is_mul(lhs, exp1, exp2)) {
        if (exp1 == m_var) {
          std::swap(exp1, exp2);
        }
        if (exp2 == m_var) {
          h1 = m_bv.mk_diseq(exp1, zro);
          if (m_mdl->is_true(h1)) {
            out.push_back(h1);
            return true;
          }
          h1 = m_bv.mk_diseq(rhs, zro);
          if (m_mdl->is_true(h1)) {
            out.push_back(h1);
            return true;
          }
          UNREACHABLE();
        }
    }
    return false;
  }
};

class inv_diseq_urem : public rw_rule {
public:
  inv_diseq_urem(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_diseq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), two(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    if (is_urem(lhs, exp1, exp2)) {
      //  if s \= 1 V t \= 0 then  Exists x. x mod_u s \= t
      if (exp1 == m_var) {
        h2 = m_bv.mk_numeral(rational(1), sz);
        h1 = m_bv.mk_diseq(exp2, h2);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_diseq(rhs, zro);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      }
      //  if s \= 0 V t \= 0 then  Exists x. s mod_u x \= t
      if (exp2 == m_var) {
        h1 = m_bv.mk_diseq(exp1, zro);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_diseq(rhs, zro);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      }
    }
    return false;
  }
};

class inv_diseq_udiv : public rw_rule {
public:
  inv_diseq_udiv(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_diseq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    if (is_udiv(lhs, exp1, exp2)) {
      //  if s \= 0 V t \= 0 then  Exists x. x udiv s \= t
      if (exp1 == m_var) {
        h1 = m_bv.mk_diseq(exp2, zro);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h2 = m_bv.mk_bv_not(zro);
        h1 = m_bv.mk_diseq(rhs, h2);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      } /* if s & t = 0 for Kappa(s) = 1 
              T         otherwise
           then  Exists x. s udiv x \= t*/ 
      if (exp2 == m_var) {
        if (sz == 1) {
          h2 = mk_bvand(exp1, rhs);
          h1 = m_bv.mk_eq(h2, zro);
          if (m_mdl->is_true(h1)) {
            out.push_back(h1);
            return true;
          }
        }
        out.push_back(m.mk_true());
        return true;
      }
    }
    return false;
  }
};


class inv_diseq_bvand : public rw_rule {
public:
  inv_diseq_bvand(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_diseq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    //  if s \= 0 V t \= 0 then Exists x. x & s \= t
    if (is_bvand(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h1 = m_bv.mk_diseq(exp1, zro);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_diseq(rhs, zro);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      }
    }
    return false;
  }
};

class inv_diseq_bvor : public rw_rule {
public:
  inv_diseq_bvor(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_diseq(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    //  if s \= ~0 V t \= ~0 then Exists x. x | s \= t
    if (is_bvor(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h2 = m_bv.mk_bv_not(zro);
        h1 = m_bv.mk_diseq(exp1, h2);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_diseq(rhs, h2);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      }
    }
    return false;
  }
};

// ---------- ULE ---------

class inv_ule_mul : public rw_rule {
public:
  inv_ule_mul(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ule(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if T then  Exists x. x * s ≤u t
    if (m_bv.is_bv_mul(lhs)) {
        out.push_back(m.mk_true());
        return true;
    } //  if t ≤u -s | s  then  Exists x. t ≤u x*s
    if(is_mul(rhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        mk_neg(exp1, h4); // -s
        h3 = mk_bvor(h4, exp1); // -s | s
        h1 = m_bv.mk_ule(lhs, h3);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};


class inv_ule_urem : public rw_rule {
public:
  inv_ule_urem(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ule(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m);
    if (is_urem(lhs, exp1, exp2)) {
      //  if True then  Exists x. x mod_u s ≤u t
      //  if True then  Exists x. s mod_u x ≤u t
      if (exp1 == m_var || exp2 == m_var) {
        out.push_back(m.mk_true());
        return true;
      }
      
    }
    if (is_urem(rhs, exp1, exp2)) {
      //  if t ≤u ∼(−s) then  Exists x. t ≤u x mod_u s
      if (exp1 == m_var) {
        expr_ref new_rhs(m), s_neg(m);
        mk_neg(exp2, s_neg);
        new_rhs = m_bv.mk_bv_not(s_neg);
        out.push_back(m_bv.mk_ule(lhs, new_rhs));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      } //  if {t ≤u s & (t+t-s) or t <u s}  then  Exists x. t ≤u s mod_u x
      if (exp2 == m_var) {
        expr_ref new_rhs(m), s_neg(m), rhs1(m), rhs2(m), new_lit(m);
        mk_add(lhs, lhs, rhs1);
        mk_neg(exp1, s_neg);
        mk_add(rhs1, s_neg, rhs2); // t+t-s
        new_rhs = mk_bvand(exp1, rhs2); // s & (t+t-s)
        if (m_mdl->is_true(new_rhs)) {
          out.push_back(m_bv.mk_ule(lhs, new_rhs)); // t ≤u s & (t+t-s)
          return true;
        }
        // TODO handle a < b by transformation
        new_lit = m_bv.mk_ult(lhs, exp1);
        if (m_mdl->is_true(new_lit)) {
          out.push_back(new_lit);
          return true;
        }
        UNREACHABLE();
      }
    }
    return false;
  }
};


class inv_ule_udiv : public rw_rule {
public:
  inv_ule_udiv(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ule(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    if (is_udiv(lhs, exp1, exp2)) {
      //  if ~(-s) ≤u s|t then  Exists x. x udiv s ≤u t
      if (exp1 == m_var) {
        mk_neg(exp2, h3);
        h1 = m_bv.mk_bv_not(h3); // ~-s
        h2 = mk_bvor(exp2, rhs); // s | t
        out.push_back(m_bv.mk_ule(h1, h2));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      } // if 0 <u ~s | t then  Exists x. s udiv x ≤u t
      if(exp2 == m_var){
        unsigned sz = m_bv.get_bv_size(m_var);
        h1 = m_bv.mk_numeral(rational::zero(),sz);
        h3 = m_bv.mk_bv_not(exp1);
        h2 = mk_bvor(h3, rhs);
        out.push_back(m_bv.mk_ult(h1, h2));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    if (is_udiv(rhs, exp1, exp2)) {
      //  if ((s*t) udiv t) & s = s then  Exists x. t ≤u x udiv s
      if (exp1 == m_var) {
        mk_mul(exp2, lhs, h4); // s*t
        h3 = m_bv.mk_bv_udiv(h4, lhs); //(s*t) udiv t
        h1 = mk_bvand(h3, exp2); // ((s*t) udiv t) & s 
        out.push_back(m.mk_eq(h1, exp2));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      } //  if True then  Exists x. t ≤u s mod_u x
      if (exp2 == m_var) {
        out.push_back(m.mk_true());
        return true;
      }
    }
    return false;
  }
};

class inv_ule_bvand : public rw_rule {
public:
  inv_ule_bvand(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ule(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    // True iff Exists x. x & s ≤u t
    if (m_bv.is_bv_and(lhs)) {
      out.push_back(m.mk_true());
      return true;
    } //  if t ≤u s then  Exists x. t ≤u s & x
    if(is_bvand(rhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        out.push_back(m_bv.mk_ule(lhs, exp1));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

class inv_ule_bvor : public rw_rule {
public:
  inv_ule_bvor(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ule(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if s ≤u t then  Exists x. s | x ≤u t
    if (is_bvor(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        out.push_back(m_bv.mk_ule(exp1, rhs));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    } // True iff Exists x.  t ≤u x | s
    if(m_bv.is_bv_or(rhs)) {
      out.push_back(m.mk_true());
      return true;
    }
    return false;
  }
};

// ----------- ULT -----------
class inv_ult_mul : public rw_rule {
public:
  inv_ult_mul(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ult(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    //  if not t=0 then  Exists x. x * s <u t
    if (is_mul(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h1 = m_bv.mk_diseq(rhs, zro);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    } //  if t <u -s|s  then  Exists x. t <u x*s
    if(is_mul(rhs, exp1, exp2)) {
        if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        mk_neg(exp1, h4); // -s
        h3 = mk_bvor(h4, exp1); // -s | s
        h1 = m_bv.mk_ult(lhs, h3);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

class inv_ult_urem : public rw_rule {
public:
  inv_ult_urem(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ult(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    if (is_urem(lhs, exp1, exp2)) {
      //  if not t = 0 then  Exists x. x umod s < t
      //  if not t = 0 then  Exists x. s umod x < t
      unsigned sz = m_bv.get_bv_size(m_var);
      h1 = m_bv.mk_diseq(rhs, m_bv.mk_numeral(rational::zero(), sz));
      out.push_back(h1);
      SASSERT(m_mdl->is_true(out.back()));
      return true;
    }
    if (is_urem(rhs, exp1, exp2)) {
      //  if t <u ∼(−s) then  Exists x. t < x umod s
      if (exp1 == m_var) {
        mk_neg(exp2, h2);
        h1 = m_bv.mk_bv_not(h2);
        out.push_back(m_bv.mk_ult(lhs, h1));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      } //  if t <u s then  Exists x. t <u s mod_u x
      if (exp2 == m_var) {
        out.push_back(m_bv.mk_ult(lhs, exp1));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};


class inv_ult_udiv : public rw_rule {
public:
  inv_ult_udiv(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    if (!is_ult(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    if (is_udiv(lhs, exp1, exp2)) {
      //  if 0 <u s ∧ 0 <u t then  Exists x. x udiv s <u t
      if (exp1 == m_var) {
        h1 = m_bv.mk_ult(zro, exp2); // 0 <u s
        h2 = m_bv.mk_ult(zro, rhs); // 0 <u t
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        out.push_back(h2);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      } // if 0 <u ∼(−t & s) ∧ 0 <u t then  Exists x. s udiv x <u t
      if(exp2 == m_var){
        mk_neg(rhs, h3);
        h4 = mk_bvand(h3, exp1); // TODO sketchy unifiy
        h1 = m_bv.mk_bv_not(h4);
        out.push_back(m_bv.mk_ult(zro, h1));
        SASSERT(m_mdl->is_true(out.back()));
        h2 = m_bv.mk_ult(zro, rhs); // 0 <u t
        out.push_back(h2);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    if (is_udiv(rhs, exp1, exp2)) {
      //  if t <u ∼0 ÷ s  then  Exists x. t <u x udiv s
      if (exp1 == m_var) {
        h3 = m_bv.mk_bv_not(zro);
        h4 = m_bv.mk_bv_udiv(h3, exp2); //~0 udiv s
        h1 = m_bv.mk_ult(lhs, h4);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      } //  if t <u ∼0 then  Exists x. t <u s udiv x
      if (exp2 == m_var) {
        h2 = m_bv.mk_bv_not(zro);
        h1 = m_bv.mk_ult(lhs, h2);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

class inv_ult_bvand : public rw_rule {
public:
  inv_ult_bvand(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ult(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    //  if not t = 0 then  Exists x. s & x <u t
    if (is_bvand(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h1 = m_bv.mk_diseq(rhs, zro);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    //  if t <s s then  Exists x. t <u s & x
    if(is_bvand(rhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h1 = m_bv.mk_slt(lhs, exp1);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

class inv_ult_bvor : public rw_rule {
public:
  inv_ult_bvor(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_ult(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    //  if s <u t then  Exists x. s | x <u t
    if (is_bvor(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h1 = m_bv.mk_ult(exp1, rhs);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    //  if t <u ~0 then  Exists x. t <u s | x
    if(is_bvor(rhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h2 = m_bv.mk_bv_not(zro);
        h1 = m_bv.mk_ult(lhs, h2);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

// -------- SLE -------
// TODO - check rule correctness
class inv_sle_mul : public rw_rule {
public:
  inv_sle_mul(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_sle(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), h5(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    // if ~(s = 0 and t <s s) then Exists x. x * s ≤s t TODO check typo
    if (is_mul(lhs, exp1, exp2)) {
      return false; // TODO -- check rule fix
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h3 = m.mk_eq(rhs, zro);
        h1 = m.mk_not(h3);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    } // if t ≤s (-s | s) & maxs then t ≤s x*s
    if(is_mul(rhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h5 = create_signed_max(sz);
        mk_neg(exp1, h4); // -s
        h2 = mk_bvor(h4, exp1); // -s | s
        h1 = mk_bvand(h5, h2);
        out.push_back(m_bv.mk_sle(lhs, h1));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

class inv_sle_urem : public rw_rule {
public:
  inv_sle_urem(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_sle(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), h5(m), h6(m), h7(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    if (is_urem(lhs, exp1, exp2)) {
      //  if ~0 <s -s & t then  Exists x. x umod s ≤s t
      if (exp1 == m_var) {
        mk_neg(exp2, h4);
        h3 = mk_bvand(h4, rhs);
        h2 = m_bv.mk_bv_not(zro);
        h1 = m_bv.mk_slt(h2, h3);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
      //  if t <u mins ∨ s ≤s t then  Exists x. s umod x ≤s t
      if (exp2 == m_var) {
        h1 = m_bv.mk_ult(rhs, create_signed_min(sz));
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_sle(exp1, rhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      }
      
    }
    if (is_urem(rhs, exp1, exp2)) {
      //  if t <s 0 V s ≤s 0 then  Exists x. t ≤s x umod s
      if (exp1 == m_var) {
        h1 = m_bv.mk_slt(lhs, zro);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_sle(exp2, zro);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      } //  if (0 ≤s s ⇒ t ≤s s) ∧ ((s <s 0 ∧ 0 ≤s t) ⇒ t <u s − t) then  Exists x. t ≤s s mod_u x
      if (exp2 == m_var) {
        bool handled = false;
        // Handle  (0 ≤s s ⇒ t ≤s s) as ( t ≤s s V s <s 0)
        h1 = m_bv.mk_sle(lhs, exp1);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          handled = true;
        }
        else {
          h1 = m_bv.mk_slt(exp1, zro);
          if (m_mdl->is_true(h1)) {
            out.push_back(h1);
            handled = true;
          }
        }
        if (!handled) {
          // should not be unhandled since the implication has to be true, otherwise x would not exist
          UNREACHABLE(); 
        }
        handled = false;
        // Handle ((s <s 0 ∧ 0 ≤s t) ⇒ t <u s − t) as (t <u s-t V 0 ≤s s V t <s 0)
        h2 = m_bv.mk_bv_sub(exp1, lhs);
        h3 = m_bv.mk_ult(lhs, h2);
        if (m_mdl->is_true(h3)) {
            out.push_back(h3);
            handled = true;
        }
        if (!handled) {
          h3 = m_bv.mk_sle(zro, exp1);
          if (m_mdl->is_true(h3)) {
            out.push_back(h3);
            handled = true;
          }
        }
        if (!handled) {
          h3 = m_bv.mk_slt(lhs, zro);
          if (m_mdl->is_true(h3)) {
            out.push_back(h3);
            handled = true;
          }
        }
        if (!handled) {
          // should not be unhandled since the implication has to be true, otherwise x would not exist
          UNREACHABLE(); 
        }
        return true;
      }
    }
    return false;
  }
};

class inv_sle_udiv : public rw_rule {
public:
  inv_sle_udiv(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    if (!is_sle(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    if (is_udiv(lhs, exp1, exp2)) {
      //  if ((s*t) udiv s = t V (t ≤s 0 => mins udiv s <s t)) then  Exists x. x udiv s ≤s t
      if (exp1 == m_var) {
        h3 = m_bv.mk_bv_mul(exp2, rhs); // s*t
        h2 = m_bv.mk_bv_udiv(h3, exp2); // s*t udiv s
        h1 = m_bv.mk_eq(h2, rhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        // Handle (t ≤s 0 => mins udiv s <s t) as (mins udiv s <s t V 0 <s t)
        h3 = create_signed_min(sz);
        h2 = m_bv.mk_bv_udiv(h3, exp2);
        h1 = m_bv.mk_slt(h2, rhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_slt(zro, rhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      } // if ~0 ≤s t V s ≤s t then  Exists x. s udiv x ≤s t
      if(exp2 == m_var){
        h2 = m_bv.mk_bv_not(zro);
        h1 = m_bv.mk_sle(h2, exp1);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_sle(exp1, rhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      }
    }
    if (is_udiv(rhs, exp1, exp2)) {
      //  if (t ≤s ~0 udiv s) V (t ≤s maxs udiv s) then  Exists x. t ≤s x udiv s
      if (exp1 == m_var) {
        h3 = m_bv.mk_bv_not(zro);
        h2 = m_bv.mk_bv_udiv(h3, exp2);
        h1 = m_bv.mk_sle(lhs, h2);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h3 = create_signed_max(sz);
        h2 = m_bv.mk_bv_udiv(h3, exp2);
        h1 = m_bv.mk_sle(lhs, h2);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      } //  if (0 ≤s s -> t ≤s s) and (s <s 0 -> t ≤s s >> 1) then  Exists x. t ≤s s udiv x
      if (exp2 == m_var) {
        bool handled = false;
        // Handle  (0 ≤s s -> t ≤s s) as ( t ≤s s V s <s 0)
        h1 = m_bv.mk_sle(lhs, exp1);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          handled = true;
        }
        else {
          h1 = m_bv.mk_slt(exp1, zro);
          if (m_mdl->is_true(h1)) {
            out.push_back(h1);
            handled = true;
          }
        }
        if (!handled) {
          // should not be unhandled since the implication has to be true, otherwise x would not exist
          UNREACHABLE(); 
        }
        handled = false;
        // Handle (s <s 0 -> t ≤s s >> 1) as (t ≤s s >> 1 V 0 ≤s s)
        h3 = m_bv.mk_numeral(rational::one(), sz);
        h2 = m_bv.mk_bv_lshr(exp1, h3);
        h1 = m_bv.mk_sle(lhs, h2);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          handled = true;
        }
        else {
          h1 = m_bv.mk_sle(zro, exp1);
          if (m_mdl->is_true(h1)) {
            out.push_back(h1);
            handled = true;
          }
        }
        if (!handled) {
          // should not be unhandled since the implication has to be true, otherwise x would not exist
          UNREACHABLE(); 
        }
        return true;
      }
    }
    return false;
  }
};

class inv_sle_bvand : public rw_rule {
public:
  inv_sle_bvand(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_sle(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if t & mins ≤u s then  Exists x. s & x ≤s t
    if (is_bvand(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        unsigned sz = m_bv.get_bv_size(m_var);
        h4 = create_signed_min(sz);
        h3 = mk_bvand(rhs, h4); // t & mins
        h1 = m_bv.mk_ule(h3, exp1);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    //  if s & t = t V t <s (t-s)&s then  Exists x. t ≤s s & x
    if(is_bvand(rhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h2 = mk_bvand(exp1, lhs);
        h1 = m_bv.mk_eq(h2, lhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h4 = m_bv.mk_bv_sub(lhs, exp1);
        h3 = mk_bvand(h4, exp1);
        h1 = m_bv.mk_slt(lhs, h3);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      }
    }
    return false;
  }
};

// TODO code part
class inv_sle_bvor : public rw_rule {
public:
  inv_sle_bvor(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_sle(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if s | mins ≤s t then  Exists x. x | s ≤s t
    if (is_bvor(lhs, exp1, exp2)) {
       if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        unsigned sz = m_bv.get_bv_size(m_var);
        h3 = create_signed_min(sz);
        h2 = mk_bvor(exp1, h3);
        h1 = m_bv.mk_sle(h2, rhs);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    } //  if s & t ? then  Exists x. t ≤s x | s TODO check if not done
    if(is_bvor(rhs, exp1, exp2)) {
      return false; // TODO
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        h3 = mk_bvand(exp1, lhs); // s & t
        h1 = h3;
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

// -------- SLT-------
class inv_slt_mul : public rw_rule {
public:
  inv_slt_mul(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_slt(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), h5(m), h6(m);
    // if ~(-t) & (-s | s) <s t then Exists x. s*x <s t
    if (is_mul(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        mk_neg(exp1, h4); // -s
        h3 = mk_bvor(h4, exp1); // -s | s
        mk_neg(rhs, h5);
        h1 = m_bv.mk_bv_not(h5);
        h6 = mk_bvand(h6, h3);
        out.push_back(m_bv.mk_slt(h6 ,rhs));
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    } // if t <s t - ((s|t)| -s) then Exists x. t <s x * s
    if(is_mul(rhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        mk_neg(exp1, h6); // -s
        h5 = mk_bvor(lhs, exp1);
        h4 = mk_bvor(h5, h6); // s | t | -s
        h3 = m_bv.mk_bv_sub(lhs, h4);
        h2 = m_bv.mk_slt(lhs, h3);
        out.push_back(h2);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

class inv_slt_urem : public rw_rule {
public:
  inv_slt_urem(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_slt(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m), h5(m), h6(m), h7(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    if (is_urem(lhs, exp1, exp2)) {
      //  if  ~t <s (-s | -t) then  Exists x. x umod s <s t
      if (exp1 == m_var) {
        h4 = m_bv.mk_bv_not(rhs);
        mk_neg(rhs, h3);
        mk_neg(exp2, h2);
        h5 = mk_bvor(h3, h2);
        h1 = m_bv.mk_slt(h4, h5);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      } //  if  s <s t ∨ 0 <s t then  Exists x. s umod x <s t
      if (exp2 == m_var) {
        h1 = m_bv.mk_slt(exp1, lhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_slt(zro, rhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      }
    }
    if (is_urem(rhs, exp1, exp2)) {
      //  if (0 <s s ⇒ t <s ∼(−s)) ∧ (s ≤s 0 ⇒ not (t = maxs)) ∧ (not t = 0 ∨ not s = 1) then  Exists x. t <s x umod s
      if (exp1 == m_var) {
        bool handled = false;
        // Handle (0 <s s ⇒ t <s ∼(−s)) as (t <s ~(-s) V s ≤s 0)
        mk_neg(exp2, h1);
        h2 = m_bv.mk_bv_not(h1); // ~-s
        h3 = m_bv.mk_slt(lhs, h2);
        if (m_mdl->is_true(h3)) {
          out.push_back(h3);
          handled = true;
        }
        else {
          h1 = m_bv.mk_sle(exp2, zro);
          if (m_mdl->is_true(h1)) {
            out.push_back(h1);
            handled = true;
          }
        }
        if (!handled) {
          // should not be unhandled since the implication has to be true, otherwise x would not exist
          UNREACHABLE(); 
        }
        handled = false;
        // Handle (s ≤s 0 ⇒ not (t = maxs)) as ( not (t = maxs) V 0 <s s)
        h4 = create_signed_max(sz);
        h5 = m_bv.mk_diseq(lhs, h4);
        if (m_mdl->is_true(h5)) {
          out.push_back(h5);
          handled = true;
        }
        else {
          h4 = m_bv.mk_slt(zro, exp2);
          if (m_mdl->is_true(h4)) {
            out.push_back(h4);
            handled = true;
          }
        }
        if (!handled) {
          // should not be unhandled since the implication has to be true, otherwise x would not exist
          UNREACHABLE(); 
        } // Handle (not t = 0 ∨ not s = 1) as usual
        h6 = m_bv.mk_diseq(lhs, zro);
        if (m_mdl->is_true(h6)) {
          out.push_back(h6);
          return true;
        }
        h6 = m_bv.mk_numeral(rational::one(), sz);
        h7 = m_bv.mk_diseq(exp2, h6);
        if (m_mdl->is_true(h7)) {
          out.push_back(h7);
          return true;
        }
        UNREACHABLE();
      } //  if (0 ≤s s ⇒ t <s s) ∧ (s <s 0 ⇒ (t <s (s − 1) >> 1)) then  Exists x. t <u s mod_u x
      if (exp2 == m_var) {
        bool handled = false;
        // Handle  (0 ≤s s ⇒ t <s s) as ( t ≤s s V s <s 0)
        h1 = m_bv.mk_sle(lhs, exp1);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          handled = true;
        }
        else {
          h1 = m_bv.mk_slt(exp1, zro);
          if (m_mdl->is_true(h1)) {
            out.push_back(h1);
            handled = true;
          }
        }
        if (!handled) {
          // should not be unhandled since the implication has to be true, otherwise x would not exist
          UNREACHABLE(); 
        }
        // Handle (s <s 0 ⇒ (t <s (s − 1) >> 1)) as (t <s (s − 1) >> 1 V 0 ≤s s)
        h2 = m_bv.mk_numeral(rational::one(), sz);
        h3 = m_bv.mk_bv_sub(exp1, h2);
        h4 = m_bv.mk_bv_lshr(h3, h2); // (s − 1) >> 1
        h5 = m_bv.mk_slt(lhs, h4);
        if (m_mdl->is_true(h5)) {
          out.push_back(h5);
          return true;
        }
        else {
          h5 = m_bv.mk_sle(zro, exp1);
          if (m_mdl->is_true(h5)) {
            out.push_back(h5);
            return true;
          }
        }
        UNREACHABLE(); 
      }
    }
    return false;
  }
};

class inv_slt_udiv : public rw_rule {
public:
  inv_slt_udiv(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m), zro(m);
    unsigned sz = m_bv.get_bv_size(m_var);
    zro = m_bv.mk_numeral(rational::zero(), sz);
    if (!is_slt(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if (t ≤s 0 -> mins udiv s <s t) then  Exists x. x udiv s <s t
    if (is_udiv(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        // Handle  (t ≤s 0 -> mins udiv s <s t) as (mins udiv s <s t V 0 <s t)
        h3 = create_signed_min(sz);
        h2 = m_bv.mk_bv_udiv(h3, exp2);
        h1 = m_bv.mk_slt(h2, rhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_slt(zro, rhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      } // if s <s t V 0 ≤s t then  Exists x. s udiv x <s t
      if(exp2 == m_var){
        h1 = m_bv.mk_slt(exp1, lhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h1 = m_bv.mk_sle(zro, rhs);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      }
    }
    if (is_udiv(rhs, exp1, exp2)) {
      //  if (t <s ~0 udiv s) V t <s maxs udiv s  then  Exists x. t <s x udiv s
      if (exp1 == m_var) {
        h4 = m_bv.mk_bv_not(zro);
        h3 = m_bv.mk_bv_udiv(h4, exp2);
        h1 = m_bv.mk_slt(lhs, h3);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        h4 = create_signed_max(sz);
        h3 = m_bv.mk_bv_udiv(h4, exp2);
        h1 = m_bv.mk_slt(lhs, h3);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          return true;
        }
        UNREACHABLE();
      } /* if t <s s         for Kappa(s) = 1
              (0 ≤s s -> t <s s) and (s <s 0 -> t <s s >> 1) otherwise
           then Exists x. t <s s udiv x 
      */
      if (exp2 == m_var) {
        if (m_bv.get_bv_size(exp1) == 1) {
          h1 = m_bv.mk_ult(lhs, exp1);
          out.push_back(h1);
          SASSERT(m_mdl->is_true(out.back()));
          return true;
        }
        // Handle (0 ≤s s -> t <s s) as (t <s s V s <s 0)
        bool handled = false;
        h1 = m_bv.mk_slt(lhs, exp1);
        if (m_mdl->is_true(h1)) {
          out.push_back(h1);
          handled = true;
        }
        else {
          h1 = m_bv.mk_slt(exp1, zro);
          if (m_mdl->is_true(h1)) {
            out.push_back(h1);
            handled = true;
          }
        }
        if (!handled) {
          // should not be unhandled since the implication has to be true, otherwise x would not exist
          UNREACHABLE(); 
        }
        // Handle (s <s 0 -> t <s s >> 1) as (t <s s >> 1 V 0 ≤s s)
        h2 = m_bv.mk_numeral(rational::one(), sz);
        h3 = m_bv.mk_bv_lshr(exp1, h2);
        h4 = m_bv.mk_slt(lhs, h3);
        if (m_mdl->is_true(h4)) {
          out.push_back(h4);
          return true;
        }
        h4 = m_bv.mk_sle(zro, exp1);
        if (m_mdl->is_true(h4)) {
          out.push_back(h4);
          return true;
        }
        UNREACHABLE();
        }
      }
    return false;
  }
};


class inv_slt_bvand : public rw_rule {
public:
  inv_slt_bvand(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_slt(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if ~(-t)& s <s t then Exists x. x & s <s t
    if (is_bvand(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        mk_neg(rhs, h4);
        h3 = m_bv.mk_bv_not(h4); // ~-t
        h2 = mk_bvand(h3, exp1);
        h1 = m_bv.mk_slt(h2, rhs);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    // if t <s s & maxs then Exists x. t <s x & s
    if(is_bvand(rhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        unsigned sz = m_bv.get_bv_size(m_var);
        h4 = create_signed_max(sz);
        h3 = mk_bvand(exp1, h4); // s & maxs
        h1 = m_bv.mk_slt(lhs, h3);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }   
    return false;
  }
};

class inv_slt_bvor : public rw_rule {
public:
  inv_slt_bvor(ast_manager &m) : rw_rule(m) {}
  bool apply(expr *e, expr_ref_vector &out) override {
    expr_ref lhs(m), rhs(m);
    if (!is_slt(e, lhs, rhs) || contains_num(e, m_var) != 1)
      return false;
    expr_ref exp1(m), exp2(m), h1(m), h2(m), h3(m), h4(m);
    //  if ~(-s) ≤u s|t then  Exists x. x | s <s t
    if (is_bvor(lhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        mk_neg(exp1, h4);
        h3 = m_bv.mk_bv_not(h4); // ~-s
        h2 = mk_bvor(exp1, rhs);
        h1 = m_bv.mk_ule(h3, h2);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    //if t <s (s | maxs) then  Exists x. t <s x | s
    if(is_bvor(rhs, exp1, exp2)) {
      if (exp1 == m_var) {
        std::swap(exp1, exp2);
      }
      if (exp2 == m_var) {
        unsigned sz = m_bv.get_bv_size(m_var);
        h4 = create_signed_max(sz);
        h3 = mk_bvor(exp1, h4); // s | maxs
        h1 = m_bv.mk_slt(lhs, h3);
        out.push_back(h1);
        SASSERT(m_mdl->is_true(out.back()));
        return true;
      }
    }
    return false;
  }
};

// end of Invertibility condition rules

struct bv_project_plugin::imp {
  ast_manager &m;
  bv_util u;
  ptr_buffer<rw_rule> inv_cond_rw_rules;
  ptr_buffer<rw_rule> sep_var_rw_rules;
  ptr_buffer<rw_rule> break_op_rw_rules;

  imp(ast_manager &_m) : m(_m), u(m) {
    // variable separation rules
    sep_var_rw_rules.push_back(alloc(addl1, m));
    sep_var_rw_rules.push_back(alloc(addl2, m));
    sep_var_rw_rules.push_back(alloc(addl3, m));
    sep_var_rw_rules.push_back(alloc(addr1, m));
    sep_var_rw_rules.push_back(alloc(addr2, m));
    sep_var_rw_rules.push_back(alloc(addr3, m));
    sep_var_rw_rules.push_back(alloc(addr4, m));
    sep_var_rw_rules.push_back(alloc(addbx1, m));
    sep_var_rw_rules.push_back(alloc(addbx2, m));
    sep_var_rw_rules.push_back(alloc(addbx3, m));
    sep_var_rw_rules.push_back(alloc(addbx4, m));
    sep_var_rw_rules.push_back(alloc(mul_mone1, m));
    sep_var_rw_rules.push_back(alloc(mul_mone2, m));
    sep_var_rw_rules.push_back(alloc(ule_zro, m));
    sep_var_rw_rules.push_back(alloc(nsle, m));
    sep_var_rw_rules.push_back(alloc(nule, m));
    // rules that change operations
    break_op_rw_rules.push_back(alloc(sle1, m));
    break_op_rw_rules.push_back(alloc(sle2, m));
    break_op_rw_rules.push_back(alloc(sle3, m));
    break_op_rw_rules.push_back(alloc(eq, m));
    break_op_rw_rules.push_back(alloc(neq1, m));
    break_op_rw_rules.push_back(alloc(neq2, m));

    // equalities
    inv_cond_rw_rules.push_back(alloc(inv_eq_mul, m));
    inv_cond_rw_rules.push_back(alloc(inv_eq_urem, m));
    inv_cond_rw_rules.push_back(alloc(inv_eq_udiv, m));
    inv_cond_rw_rules.push_back(alloc(inv_eq_bvand, m));
    inv_cond_rw_rules.push_back(alloc(inv_eq_bvor, m));
    // disequalities
    inv_cond_rw_rules.push_back(alloc(inv_diseq_mul, m));
    inv_cond_rw_rules.push_back(alloc(inv_diseq_urem, m));
    inv_cond_rw_rules.push_back(alloc(inv_diseq_udiv, m));
    inv_cond_rw_rules.push_back(alloc(inv_diseq_bvand, m));
    inv_cond_rw_rules.push_back(alloc(inv_diseq_bvor, m));
    // inequalities
    //  - basic operations
    inv_cond_rw_rules.push_back(alloc(inv_ineq_basic_op, m));
    //  - ule
    inv_cond_rw_rules.push_back(alloc(inv_ule_mul, m));
    inv_cond_rw_rules.push_back(alloc(inv_ule_urem, m));
    inv_cond_rw_rules.push_back(alloc(inv_ule_udiv, m));
    inv_cond_rw_rules.push_back(alloc(inv_ule_bvand, m));
    inv_cond_rw_rules.push_back(alloc(inv_ule_bvor, m));
    // ult
    inv_cond_rw_rules.push_back(alloc(inv_ult_mul, m));
    inv_cond_rw_rules.push_back(alloc(inv_ult_urem, m));
    inv_cond_rw_rules.push_back(alloc(inv_ult_udiv, m));
    inv_cond_rw_rules.push_back(alloc(inv_ult_bvand, m));
    inv_cond_rw_rules.push_back(alloc(inv_ult_bvor, m));
    // sle
    inv_cond_rw_rules.push_back(alloc(inv_sle_mul, m));
    inv_cond_rw_rules.push_back(alloc(inv_sle_urem, m));
    inv_cond_rw_rules.push_back(alloc(inv_sle_udiv, m));
    inv_cond_rw_rules.push_back(alloc(inv_sle_bvand, m));
    inv_cond_rw_rules.push_back(alloc(inv_sle_bvor, m));
    // slt
    inv_cond_rw_rules.push_back(alloc(inv_slt_mul, m));
    inv_cond_rw_rules.push_back(alloc(inv_slt_urem, m));
    inv_cond_rw_rules.push_back(alloc(inv_slt_udiv, m));
    inv_cond_rw_rules.push_back(alloc(inv_slt_bvand, m));
    inv_cond_rw_rules.push_back(alloc(inv_slt_bvor, m));
  }


  ~imp() {
    for (auto *r : inv_cond_rw_rules) {
      dealloc(r);
    }
    for (auto *r : sep_var_rw_rules) {
      dealloc(r);
    }
    for (auto *r : break_op_rw_rules) {
      dealloc(r);
    }
    
  }

  void reset_inv_rw_rules(model &mdl, expr *var) {
    for (auto r : inv_cond_rw_rules) {
       r->reset(&mdl, var);
     }
  }

  void reset_sep_var_rw_rules(model &mdl, expr *var) {
    for (auto r : sep_var_rw_rules) {
      r->reset(&mdl, var);
    }
  }

  void reset_break_op_rw_rules(model &mdl, expr *var) {
    for (auto r : break_op_rw_rules) {
      r->reset(&mdl, var);
    }
  }

  // true iff fml is a bound that is projected true
  bool is_lost_bound(expr* fml, expr* var) {
    bv_util m_bv(m);
    expr_ref rhs(m), lhs(m), exp1(m), exp2(m);
    if (m_bv.is_bv_ule(fml) || m_bv.is_bv_sle(fml)) {
      exp1 = to_app(fml)->get_arg(0);
      exp2 = to_app(fml)->get_arg(1);
      // first basic operations
      if(exp1 == var || exp2 == var || 
         ((m_bv.is_bv_neg(exp1) || m_bv.is_bv_not(exp1)) && to_app(exp1)->get_arg(0) == var) ||
         ((m_bv.is_bv_neg(exp2) || m_bv.is_bv_not(exp2)) && to_app(exp2)->get_arg(0) == var)) {
          return true;
      }
      if (m_bv.is_bv_add(exp1) || m_bv.is_bv_sub(exp1)) {
        for (auto t : *to_app(exp1)) {
          if (t == var)
            return true;
        }
      }
      if (m_bv.is_bv_add(exp2) || m_bv.is_bv_sub(exp2)) {
        for (auto t : *to_app(exp1)) {
          if (t == var)
            return true;
        }
      }
    }
    if (m_bv.is_bv_ule(fml)) {
      exp1 = to_app(fml)->get_arg(0);
      if (m_bv.is_bv_mul(exp1)) {
        for (auto t : *to_app(exp1)) {
          if (t == var)
            return true;
        }
      }
    }
    return false; 
  }

  void atomize_literal(expr* fml, expr_ref &res) {
    expr* exp1;
    bv_util m_bv(m);
    if (!m.is_not(fml)) {
      res = fml;
      return;
    }
    exp1 = to_app(fml)->get_arg(0);
    if (m.is_not(exp1)) {
      //std::cout << "NOT" << std::endl;
      atomize_literal(to_app(exp1)->get_arg(0), res);
    } else if (m_bv.is_bv_ule(exp1)) {
      //std::cout << "ULE" << std::endl;
      res = m_bv.mk_ult(to_app(exp1)->get_arg(1), to_app(exp1)->get_arg(0));
    } else if (m_bv.is_bv_ult(exp1)) {
      //std::cout << "ULT" << std::endl;
      res = m_bv.mk_ule(to_app(exp1)->get_arg(1), to_app(exp1)->get_arg(0));
    } else if (m_bv.is_bv_sle(exp1)) {
      //std::cout << "SLE" << std::endl;
      res = m_bv.mk_slt(to_app(exp1)->get_arg(1), to_app(exp1)->get_arg(0));
    } else if (m_bv.is_bv_slt(exp1)) {
      //std::cout << "SLT" << std::endl;
      res = m_bv.mk_sle(to_app(exp1)->get_arg(1), to_app(exp1)->get_arg(0));
    } else if (m.is_eq(exp1)) {
      //std::cout << "EQ" << std::endl;
      res = m_bv.mk_diseq(to_app(exp1)->get_arg(0), to_app(exp1)->get_arg(1));
    } else if (m.is_distinct(exp1)) {
      //std::cout << "DISTINCT" << std::endl;
      res = m_bv.mk_eq(to_app(exp1)->get_arg(0), to_app(exp1)->get_arg(1));
    } else {
      //std::cout << "ELSE" << std::endl;
      res = fml;
    }
  }

  void atomize_literals(expr_ref_vector &fmls) {
    expr_ref_vector result(m);
    expr_ref res(m);
    for (auto *fml : fmls) {
      std::cout << "Kill me" << mk_pp(fml, m) << std::endl;
      atomize_literal(fml, res);
      result.push_back(res);
      }
    fmls.reset();
    fmls.append(result);
  }

  bool project_linear(expr *f, expr_ref_vector &out) {
    expr_ref atomized(m);
    atomize_literal(f, atomized);
    for (auto r : inv_cond_rw_rules) {
      out.reset();
      if (r->apply(atomized, out)) {
        return true;
      }
    }
    return false;
    }

  // function to project linear formulas 
  void project_all_linear(model &mdl, expr_ref &var, expr_ref_vector &fmls, expr_ref_vector &bckg_fmls,
                        expr_ref_vector &orig_projected, bool project_bounds) { 
    expr_ref_vector iter_res(m), out(m);
    reset_inv_rw_rules(mdl, var);
    for (expr* fml : fmls) {
        // filter non-linear and bounds that could be projected to true
        if (contains_num(fml, var) != 1 || (!project_bounds && is_lost_bound(fml, var))) {
          iter_res.push_back(fml);
          continue;
        }
        if (project_linear(fml, out)) {
          orig_projected.push_back(fml);
          bckg_fmls.append(out);
        }
        else
          iter_res.push_back(fml);
    }
    fmls.reset();
    fmls.append(iter_res);
  }

  void substitute_model_values(model &mdl, expr_ref &var, expr_ref_vector &fmls, expr_ref_vector &res) {
    expr_ref out(m);
    for (auto f : fmls) {
      get_subst(mdl, var, f, out);
      res.push_back(out);
    }
  }

  void fix_soundness(model &mdl, expr_ref &var, expr_ref_vector &backg_fmls, expr_ref_vector &to_project, expr_ref &to_satisfy) {
    expr_ref out(m), neg_satisfy(m);
    neg_satisfy = mk_not(to_satisfy);
    params_ref p;
    ref<solver> sol = mk_smt_solver(m, p, symbol::null);
    sol->assert_expr(neg_satisfy);
    sol->assert_expr(mk_and(backg_fmls));
    for (auto f : to_project) {
      if ((sol->check_sat(0, nullptr) == l_false))
        return;
      get_subst(mdl, var, f, out);
      backg_fmls.push_back(out);
      sol->assert_expr(out);
    }
  }

  // tom project
  vector<def> project(model &mdl, app_ref_vector &vars, expr_ref_vector &fmls, bool useless) {
    std::cout << "In project \n";
    expr_ref_vector res(m);
    app_ref_vector var_vect(m); // vector for 1 variable for later inputs
    // backg_fmls = x-free formulas
    // norm_fmls = formulas with separated variables
    // simpl_fmls = formulas with broken operations
    // bound_fmls = input for resolve
    // new_bounds = result from resolve function
    // bd_fmls = formulas which cannot be reduced to a bound
    // lazy_fmls = formulas that are added by Lazy mbp
    // pi = unnormalized original formulas
    // sig = normalized original formulas
    expr_ref_vector backg_fmls(m), norm_fmls(m), simpl_fmls(m), bound_fmls(m), new_bounds(m), bd_fmls(m), lazy_fmls(m), basic_project(m), lazy_project(m);
    expr_ref_vector part_subst(m);
    expr_ref orig_fla(m), to_satisfy(m);
    expr_ref result(m);
    app_ref_vector vr(m);
    res.append(fmls);
    mk_exists(mk_and(res), vars, orig_fla);
    // Sanity check, if model is trully a model of fmls
    result = mk_and(res);
    SASSERT(mdl.is_true(result));
    for (unsigned var_num = 0; var_num < vars.size(); var_num++) {
      // save original formula so we can check for soundness
      vr.reset(); vr.push_back(vars.get(var_num));
      mk_exists(mk_and(res), vr, to_satisfy);
      // start projection
      expr_ref var(vars.get(var_num), m);
      backg_fmls.reset(); lazy_project.reset(); basic_project.reset(); simpl_fmls.reset();
      // apply invertibility conditions, do not project bounds
      project_all_linear(mdl, var, res, backg_fmls, lazy_project, false);
      // iterate over rest of the formulas
      for (unsigned f_num = 0; f_num < res.size(); f_num++) {
        expr_ref fml(res.get(f_num), m);
        if (!contains(fml, var)) {
          backg_fmls.push_back(fml);
          continue;
        }
        // separate what we can
        norm_fmls.reset();
        separate_var(var, fml, mdl, norm_fmls); 
        std::cout << "In project 2 \n";
        // invert newly created linear formulas
        project_all_linear(mdl, var, norm_fmls, backg_fmls, lazy_project, false); 
        std::cout << "In project 3 \n";
        simplify_operations(var, norm_fmls, mdl, simpl_fmls);
        std::cout << "In project 4 \n";
      }
      std::cout << "In project 5 \n";
      extract_bound_fmls(var, simpl_fmls, mdl, basic_project, bound_fmls, backg_fmls);
      std::cout << "In project 6 with bound formulas : " << bound_fmls << "\n on var" << var << std::endl;
      resolve_boundaries(var, bound_fmls, mdl, new_bounds, bd_fmls);
      std::cout << "In project 6.5 \n";
      if (bd_fmls.size() > 0)
        basic_project.append(bd_fmls);
      else
        backg_fmls.append(new_bounds);
        lazy_project.append(bound_fmls);
      std::cout << "Attempting partial substitution \n";
      // partially substitute in pi, returns unresolved in pi and adds resolved to backg_fmls
      //partial_substitution(var, var_vect, pi, mdl, backg_fmls); -- not an underaproximation
      std::cout << "In project 7 \n";
      SASSERT(!mdl.is_false(mk_and(backg_fmls)));
      // project all formulas where we cannot do anything else
      substitute_model_values(mdl, var, basic_project, backg_fmls);
      // substitute until we fix soundness
      SASSERT(!mdl.is_false(mk_and(backg_fmls)));
      fix_soundness(mdl, var, backg_fmls, lazy_project, to_satisfy);
      std::cout << "In project 8 \n";
      res.reset();
      SASSERT(!mdl.is_false(mk_and(backg_fmls)));
      res.append(backg_fmls);
    }
    vars.shrink(0);
    fmls.reset();
    fmls.append(res);
    std::cout << "Removing true fmls \n";
    flatten_numerical(fmls, mdl);
    std::cout << "Checking validity \n";
    return vector<def>();
   }

  vector<def> project_old_norm(model &mdl, app_ref_vector &vars, expr_ref_vector &fmls, bool useless) {
    std::cout << "In project \n";
    std::cout << "started mbp with formulas" << fmls <<std::endl;
    expr_ref_vector res(m);
    app_ref_vector var_vect(m); // vector for 1 variable for later inputs
    // backg_fmls = x-free formulas
    // norm_fmls = formulas with separated variables
    // simpl_fmls = formulas with broken operations
    // bound_fmls = input for resolve
    // new_bounds = result from resolve function
    // bd_fmls = formulas which cannot be reduced to a bound
    // lazy_fmls = formulas that are added by Lazy mbp
    // pi = unnormalized original formulas
    // sig = normalized original formulas
    expr_ref_vector backg_fmls(m), norm_fmls(m), simpl_fmls(m), bound_fmls(m), new_bounds(m), bd_fmls(m), lazy_fmls(m), basic_project(m), lazy_project(m);
    expr_ref_vector part_subst(m);
    expr_ref orig_fla(m), to_satisfy(m);
    expr_ref result(m);
    app_ref_vector vr(m);
    res.append(fmls);
    mk_exists(mk_and(res), vars, orig_fla);
    // Sanity check, if model is trully a model of fmls
    result = mk_and(res);
    SASSERT(mdl.is_true(result));
    for (unsigned var_num = 0; var_num < vars.size(); var_num++) {
      // save original formula so we can check for soundness
      vr.reset(); vr.push_back(vars.get(var_num));
      mk_exists(mk_and(res), vr, to_satisfy);
      // start projection
      expr_ref var(vars.get(var_num), m);
      backg_fmls.reset(); lazy_project.reset(); basic_project.reset(); simpl_fmls.reset();
      // iterate over rest of the formulas
      for (unsigned f_num = 0; f_num < res.size(); f_num++) {
        expr_ref fml(res.get(f_num), m);
        if (!contains(fml, var)) {
          backg_fmls.push_back(fml);
          continue;
        }
        // separate what we can
        norm_fmls.reset();
        separate_var(var, fml, mdl, norm_fmls); 
        simplify_operations(var, norm_fmls, mdl, simpl_fmls);
        std::cout << "In project 4 \n";
      }
      std::cout << "In project 5 \n";
      extract_bound_fmls(var, simpl_fmls, mdl, basic_project, bound_fmls, backg_fmls);
      std::cout << "In project 6 with bound formulas : " << bound_fmls << "\n on var" << var << std::endl;
      resolve_boundaries(var, bound_fmls, mdl, new_bounds, bd_fmls);
      std::cout << "In project 6.5 \n";
      if (bd_fmls.size() > 0)
        basic_project.append(bd_fmls);
      else
        backg_fmls.append(new_bounds);
      substitute_model_values(mdl, var, basic_project, backg_fmls);
      // substitute until we fix soundness
      SASSERT(!mdl.is_false(mk_and(backg_fmls)));
      fix_soundness(mdl, var, backg_fmls, lazy_project, to_satisfy);
      std::cout << "In project 8 \n";
      res.reset();
      SASSERT(!mdl.is_false(mk_and(backg_fmls)));
      res.append(backg_fmls);
    }
    vars.shrink(0);
    fmls.reset();
    fmls.append(res);
    std::cout << "Removing true fmls \n";
    flatten_numerical(fmls, mdl);
    std::cout << "Checking validity \n";
    std::cout << "ended mbp with formulas" << fmls <<std::endl;
    return vector<def>();
  }

// Tom
// Inputes values lazyli untill it holds that MBP(mdl, var, fmls) => Exists var. fmls
// Input  bckg_fmls ∧ new_fmls => exists var. sig
// Output bckg_fmls ∧ new_fmls ∧ lazy_fmls => exists var. pi ∧ sig (orig fla)
void lazy_mbp_leg(expr_ref_vector &bckg_fmls, expr_ref_vector &sig, expr_ref &exists_sig, expr_ref_vector &pi, expr_ref var,
              expr_ref_vector &new_fmls, model &mdl, expr_ref_vector &lazy_fmls, expr_ref &orig_fla) {
  expr_ref negged_quant_conj(m);
  negged_quant_conj = m.mk_and(mk_and(pi), m.mk_and(mk_and(sig), mk_and(bckg_fmls)));
  app_ref_vector vec(m);
  vec.push_back(to_app(var.get()));
  std::cout << "Before exists: " << mk_pp(negged_quant_conj,m) << std::endl;
  mk_exists(negged_quant_conj, vec, negged_quant_conj);
  std::cout << "Before neg: " << mk_pp(negged_quant_conj,m) << std::endl;
  negged_quant_conj = m.mk_not(negged_quant_conj);
  std::cout << "After neg: " << mk_pp(negged_quant_conj, m) << std::endl;
  SASSERT(!is_sat(negged_quant_conj));
  std::cout << "Sig: " << mk_pp(mk_and(sig), m) << std::endl;
  std::cout << "Ex Sig: " << exists_sig << std::endl;
  std::cout << "bckg_fmls :\n"<< mk_pp(mk_and(bckg_fmls), m) << std::endl;
  std::cout << "new_fmls: \n"<< mk_pp(mk_and(new_fmls), m) << std::endl;
  // sanity check
  std::cout << "Sig size :" <<sig.size() << std::endl;
  SASSERT(!is_sat(mk_and(bckg_fmls), mk_and(new_fmls), m.mk_not(exists_sig)));
  // if there exists a conterexample to bckg_fmls ∧ new_fmls => exists var. sig
  if (!is_sat(mk_and(bckg_fmls), mk_and(new_fmls), m.mk_not(orig_fla))) {
    std::cout << "do not need to strenghten\n";
    return;
  }
  std::cout << "need to strenghten\n";
  expr_ref_vector result_fmls(m);
  result_fmls.append(bckg_fmls);
  result_fmls.append(new_fmls);
  expr_ref r(m);
  for (auto f : pi) {
    get_subst(mdl, var, f, r);
    lazy_fmls.push_back(r);
  }
  if (!is_sat(mk_and(result_fmls), mk_and(lazy_fmls), negged_quant_conj))
      return;
  for (auto f : sig) {
    get_subst(mdl, var, f, r);
    lazy_fmls.push_back(r);
    if (!is_sat(mk_and(result_fmls), mk_and(lazy_fmls), negged_quant_conj))
      return;
  }
  result_fmls.append(lazy_fmls);
  std::cout << "nqc :\n"<< mk_pp(negged_quant_conj, m) << std::endl;
  std::cout << "result: \n"<< mk_pp(mk_and(result_fmls), m) << std::endl;
  SASSERT(!is_sat(mk_and(result_fmls), negged_quant_conj));//m.mk_not(orig_fla)));
  }


//  version from qe_lia_arith
void lazy_mbp(expr_ref_vector &backg, expr_ref_vector &pi, expr_ref_vector &sig,
              expr_ref v, expr_ref_vector &new_fmls, model &model) {
    expr_ref negged_quant_conj(m);
    negged_quant_conj = m.mk_and(mk_and(pi), m.mk_and(mk_and(sig), mk_and(backg)));
    if (contains(negged_quant_conj, v)) {
        app_ref_vector vec(m);
        vec.push_back(to_app(v.get()));
        mk_exists(negged_quant_conj, vec, negged_quant_conj);
    }
    negged_quant_conj = m.mk_not(negged_quant_conj);

    expr_ref new_fmls_conj(m), r(m);
    expr_ref_vector substs(m);
    new_fmls_conj = m.mk_and(mk_and(new_fmls), mk_and(backg));

    for (auto f : sig) {
        get_subst(model, v, f, r);
        substs.push_back(r);
    }

    unsigned init_sz = substs.size(); // for stats
    unsigned stren_sz = init_sz;

    if (is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj)) {
        for (auto & f : pi) {     // too weak; add missing substs
            get_subst(model, v, f, r);
            substs.push_back(r);    // to do: try adding lazily, i.e., based on the model
        }
        stren_sz = substs.size();
    }

    // sanity check
    // SASSERT(!is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj));

    // todo: possibly, optimize with incremental SMT
    for (unsigned k = 0; k < substs.size(); ) {
        expr_ref_vector tmp(m);
        for (unsigned l = 0; l < substs.size(); l++)
        if (k != l) tmp.push_back(substs.get(l));

        expr_ref tmp_conj(m);
        tmp_conj = mk_and(tmp);

        if (is_sat(new_fmls_conj, tmp_conj, negged_quant_conj)) k++;
        else {
            // erase k:
            for (unsigned m = k; m < substs.size() - 1; m++) substs.set(m, substs.get(m+1));
            substs.pop_back();
        }
    }

    unsigned weak_sz = substs.size(); // for stats
    TRACE("qe", tout << "Lazy MBP completed: "
                << init_sz << " -> " << stren_sz << " -> " << weak_sz << " conjuncts\n";);
    new_fmls.append(substs);
}

// computes mbp(pi && sig, model, v)
// input: new_fmls ==> \exist v pi
// output: new_fmls ==> \exists v pi && sig
void lazy_mbp_hari(expr_ref_vector &pi, expr_ref_vector &sig, expr_ref v,
              expr_ref_vector &new_fmls, model &model) {
    expr_ref negged_quant_conj(m);
    negged_quant_conj = m.mk_and(mk_and(pi), mk_and(sig));
    if (contains(negged_quant_conj, v)) {
        app_ref_vector vec(m);
        vec.push_back(to_app(v.get()));
        mk_exists(negged_quant_conj, vec, negged_quant_conj);
    }
    negged_quant_conj = m.mk_not(negged_quant_conj);

    expr_ref new_fmls_conj(m), r(m);
    new_fmls_conj = mk_and(new_fmls);

    expr_ref_vector substs(m);
    for (auto f : sig) {
        get_subst(model, v, f, r);
        substs.push_back(r);
    }
    unsigned init_sz = substs.size(); // for stats

    if (!is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj)) {
        new_fmls.append(substs);
        TRACE("qe", tout << "\nLazy MBP completed. sig size " << init_sz
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

    TRACE("qe", tout << "\nLazy MBP completed. sig size " << init_sz << " substitutions in pi " << substs.size() - init_sz << " and pi size " << pi.size()  << "\n";);
    new_fmls.append(substs);
}

void get_subst(model &model, expr *v, expr *f, expr_ref& res) {
    expr_safe_replace sub(m);
    sub.insert(v, model(v));
    sub(f, res);
}

// top level expression is unhandled, so we are done with this expr
bool unhandled(expr *f) {
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
    return false;
}

// we have moved everything we could to the other side
bool is_separated(expr *f, expr *v) {
  if (!contains(f, v) || unhandled(f))
    return true;
  return false;
}

// separate vars for one formula
void separate_var(expr *var, expr *f, model &mdl, expr_ref_vector &res) {
  expr_ref_vector fmls(m);
  fmls.push_back(f);
  separate_var(var, fmls, mdl, res);
}

// move vars to to other side in all expressions in f
void separate_var(expr *var, expr_ref_vector &fmls, model &mdl, expr_ref_vector &res) {
    expr_ref_vector todo(m);
    todo.append(fmls);
    reset_sep_var_rw_rules(mdl, var);
    expr_ref_vector out(m);
    expr_ref t(m);
    bool normalized;
    while (!todo.empty()) {
      t = todo.back();
      todo.pop_back();
      if (is_separated(t, var)) {
        res.push_back(t);
        continue;
      }
      normalized = false;
      for (auto r : sep_var_rw_rules) {
        out.reset();
        if (r->apply(t, out)) {
          todo.append(out);
          normalized = true;
          break;
        }
      }
      if (!normalized) 
        res.push_back(t);
  }
}

// break operations to other operations and separate vars accordingly
void simplify_operations(expr *var, expr_ref_vector &fmls, model &mdl, expr_ref_vector &res) {
    expr_ref_vector todo(m);
    todo.append(fmls);
    reset_break_op_rw_rules(mdl, var);
    reset_sep_var_rw_rules(mdl, var);
    expr_ref_vector out(m);
    expr_ref t(m);
    unsigned i = 0;
    bool normalized;
    while (!todo.empty()) {
      t = todo.back();
      todo.pop_back();
      if (is_separated(t, var)) {
        res.push_back(t);
        continue;
      }
      normalized = false;
      for (auto r : break_op_rw_rules) {
        out.reset();
        if (r->apply(t, out)) {
          todo.append(out);
          normalized = true;
          break;
        }
      }
      if (!normalized) {
        i = 0;
        for (auto r : sep_var_rw_rules) {
          out.reset();
          //std::cout << "Simpl project 5 and i is: "<< i << "\n";
          i++;
          if (r->apply(t, out)) {
            std::cout << "Changed something in rule " << i << "in looks like \n"<< t << "and out looks like\n" << out << std::endl;
            todo.append(out);
            normalized = true;
            break;
          }
        }
      }
      if (!normalized) 
        res.push_back(t);
    }
}

void extract_bound_fmls(expr *var, expr_ref_vector &fmls, model &mdl, expr_ref_vector &pi,
                      expr_ref_vector &bounds, expr_ref_vector &bckg_fmls) {
  unsigned var_count;
  expr_ref  lhs(m), rhs(m), exp1(m), exp2(m);
  for (auto *f : fmls) {
    var_count = contains_num(f, var);
    if (var_count == 0) {
      bckg_fmls.push_back(f);
      continue;
    }
    if (var_count > 1) {
      pi.push_back(f);
      continue;
    }
    if (u.is_bv_ule(f)) {
      lhs = to_app(f)->get_arg(0);
      rhs = to_app(f)->get_arg(1);
      if ((contains(lhs, var) && (lhs == var || (u.is_bv_mul(lhs) &&
       (to_app(lhs)->get_arg(0) == var || to_app(lhs)->get_arg(1) == var)))) ||
          (contains(rhs, var) && (rhs == var || (u.is_bv_mul(rhs) &&
       (to_app(rhs)->get_arg(0) == var || to_app(rhs)->get_arg(1) == var))))) {
        bounds.push_back(f);
        continue;  
      } 
    }
    pi.push_back(f);
  }
}

bool flatten_expr_rec(expr *f, model &mdl, expr_ref &result) {
  result.reset();
  expr_ref res(m);
  if (u.is_numeral(f)) {
    result = f;
    return true;
  }
  if (to_app(f)->get_num_args() == 0) {
    result = f;
    return false;
  }
  expr_ref_vector new_fmls(m), var_fmls(m);
  new_fmls.reset(); var_fmls.reset();
  bool all_num = true;
  expr_ref out(m);
  for (auto a : *to_app(f)) {
    if(!flatten_expr_rec(a, mdl, out)) {
      all_num = false;
      var_fmls.push_back(out);
    }
    else {
      new_fmls.push_back(out);
    }
  }
  if (new_fmls.size() > 0) {
    res = m.mk_app(u.get_fid(), to_app(f)->get_decl_kind(), to_app(f)->get_num_parameters(), to_app(f)->get_parameters(), new_fmls.size(), new_fmls.c_ptr());
    if (all_num) {
        mdl.eval_expr(res, result);
        SASSERT(u.is_numeral(result));
        return true;
    }
    expr_ref flattened(m);
    mdl.eval_expr(res, flattened);
    SASSERT(u.is_numeral(flattened));
    var_fmls.push_back(flattened);
  }
  result = m.mk_app(u.get_fid(), to_app(f)->get_decl_kind(), to_app(f)->get_num_parameters(), to_app(f)->get_parameters(), var_fmls.size(), var_fmls.c_ptr());
  return false;
}

void flatten_numerical(expr_ref_vector &fmls, model &mdl) {
  expr_ref_vector res(m);
  expr_ref lhs(m), rhs(m), lhsout(m), rhsout(m), new_fml(m), f(m);
  for (auto *k : fmls) {
    bool is_not_op = false;
    new_fml.reset();
    if (m.is_not(k)) {
      is_not_op = true;
      f = to_app(k)->get_arg(0);
    }
    else {
      f = k;
    } 
    if (u.is_bv_ule(f) || u.is_bv_sle(f) || u.is_bv_ult(f) || u.is_bv_slt(f) || m.is_eq(f) || m.is_distinct(f)) {
      lhs = to_app(f)->get_arg(0);
      rhs = to_app(f)->get_arg(1);
      flatten_expr_rec(lhs, mdl, lhsout);
      flatten_expr_rec(rhs, mdl, rhsout);
      rebuild_bool_op(lhsout, rhsout, f, new_fml);
      if (is_not_op) {
        new_fml = mk_not(new_fml);
      }
      if (u.is_numeral(lhsout) && u.is_numeral(rhsout)) {
        // both are values
        SASSERT(mdl.is_true(new_fml));
        continue;
      }
      res.push_back(new_fml);
    } else if (u.is_bit2bool(f)) {
      expr_ref_vector new_args(m);
      new_args.reset();
      lhs = to_app(f)->get_arg(0);
      flatten_expr_rec(lhs, mdl, lhsout);
      new_args.push_back(lhsout);
      new_fml = m.mk_app(u.get_fid(), to_app(f)->get_decl_kind(), to_app(f)->get_num_parameters(), to_app(f)->get_parameters(), new_args.size(), new_args.c_ptr());
      if (is_not_op) {
        new_fml = mk_not(new_fml);
      }
      if (u.is_numeral(lhsout)) {
        SASSERT(mdl.is_true(new_fml));
        continue;
      }
      res.push_back(new_fml);
    } else {
      res.push_back(k);
    }
  }
  fmls.reset();
  fmls.append(res);


}

void rebuild_bool_op(expr_ref &a, expr_ref &b, expr* f, expr_ref &new_fml) {
  new_fml.reset();
  if (m.is_eq(f)) {
    new_fml = m.mk_eq(a, b);
  } else if (m.is_distinct(f)) {
    new_fml = u.mk_diseq(a, b);
  }else {
    new_fml = m.mk_app(u.get_fid() , to_app(f)->get_decl_kind(), a, b);
  }
}

// function to attempt linearization of a formula
/*
bool attempt_linearization(expr *var, app_ref_vector &var_vect, expr *f, model &mdl, expr_ref_vector &out) {
  out.reset();
  expr_ref lhs(m), nlhs(m), nrhs(m),  rhs(m), exp1(m), exp2(m), exp3(m), exp4(m), rebuilt_fml(m), nexp1(m), nexp2(m), new_exp(m);
  expr_ref_vector projected(m);
  bool found, linearized;
  if ((!u.is_bv_ule(f) && !u.is_bv_ult(f) && !u.is_bv_slt(f) && !u.is_bv_sle(f) && !m.is_eq(f) && !m.is_distinct(f)) || to_app(f)->get_num_args() != 2) {
    return false;
  }
  lhs = to_app(f)->get_arg(0);
  rhs = to_app(f)->get_arg(1);
  if (to_app(lhs)->get_num_args() == 2) {
    found = false;
    exp1 = to_app(lhs)->get_arg(0);
    exp2 = to_app(lhs)->get_arg(1);
    if (exp1 == var && exp2 != var) {
      found = true;
      get_subst(mdl, var, exp2, nexp2);
      nexp1 = exp1;
    }
    else if(exp2 == var && exp1 !=var) {
      found = true;
      get_subst(mdl, var, exp1, nexp1);
      nexp2 == exp2;
    }
    // if both var then it is gonna be reduced to trivial exp
    if (found) {
      get_subst(mdl, var, rhs, nrhs);
      nlhs = m.mk_app(u.get_fid(), to_app(lhs)->get_decl_kind(), nexp1, nexp2);
      rebuild_bool_op(nlhs, nrhs, f, new_exp);
      projected.reset();
      projected.push_back(new_exp);
      if (project_all_linear(mdl, var_vect, projected, true)) {
        linearized = true;
        out.append(projected);
      }
    }
  }
  if (to_app(rhs)->get_num_args() == 2) {
    found = false;
    exp1 = to_app(rhs)->get_arg(0);
    exp2 = to_app(rhs)->get_arg(1);
    if (exp1 == var && exp2 != var) {
      found = true;
      get_subst(mdl, var, exp2, nexp2);
      nexp1 = exp1;
    }
    else if(exp2 == var && exp1 !=var) {
      found = true;
      get_subst(mdl, var, exp1, nexp1);
      nexp2 == exp2;
    }
    // if both var then it is gonna be reduced to trivial exp
    if (found) {
      get_subst(mdl, var, lhs, nlhs);
      nrhs = m.mk_app(u.get_fid(), to_app(rhs)->get_decl_kind(), nexp1, nexp2);
      rebuild_bool_op(nlhs, nrhs, f, new_exp);
      projected.reset();
      projected.push_back(new_exp);
      if (project_all_linear(mdl, var_vect, projected, true)) {
        linearized = true;
        out.append(projected);
      }
    }
  }
  return linearized;
}

void partial_substitution(expr *var, app_ref_vector &vars, expr_ref_vector &fmls, model &mdl, expr_ref_vector &backg_fmls) {
  expr_ref_vector out(m), unprocessed(m);
  unprocessed.reset();
  unprocessed.append(fmls);
  fmls.reset();
  // first check if it can be inverted
  for (auto *f : unprocessed) {
    if (attempt_linearization(var, vars, f, mdl, out)) {
      backg_fmls.append(out);
      std :: cout << "Partially substituted :" << mk_pp(f, m) << "\nInto :" << out << std::endl;
    }
    else {
      fmls.push_back(f);
    }
  }
}
*/
// push not inside f
// produces side condition sc satisfied by mdl
bool push_not(expr_ref f, expr_ref &res, expr_ref &sc, model &mdl) {
    expr_ref rw(m);
    expr *lhs, *rhs;
    SASSERT(m.is_not(f));
    rw = to_app(f)->get_arg(0);
    TRACE("qe", tout << "Trying to push not into " << rw << "\n";);

    if (u.is_bv_ule(rw, lhs, rhs)) {
        // not(a <= b) <==> b + 1 <= a && b <= 2^n - 2
        const unsigned sz = u.get_bv_size(lhs);
        expr_ref one = expr_ref(u.mk_numeral(rational::one(), sz), m);
        expr_ref nw_lhs(m);
        rational val;
        if(u.is_numeral(rhs, val))
            nw_lhs = u.mk_numeral(val + rational::one(), sz);
        else
            nw_lhs = u.mk_bv_add(rhs, one);
        res = u.mk_ule(nw_lhs, lhs);
        rational bnd = rational::power_of_two(sz) - 2;
        sc = u.mk_ule(nw_lhs, u.mk_numeral(bnd, sz));
        if(!mdl.is_true(sc)) return false;
        return true;
    }
    if (m.is_eq(rw, lhs, rhs)) {
        res = m.mk_not(u.mk_ule(lhs, rhs));
        if (mdl.is_true(res)) {
            return push_not(res, res, sc, mdl);
        }
        else {
            res = m.mk_not(u.mk_ule(rhs, lhs));
            SASSERT(mdl.is_true(res));
            return push_not(res, res, sc, mdl);
        }
    }
    return false;
}

//void swap_neg_add(expr_ref t, expr_ref& res)
//{
//  if (u.is_bv_neg(t)) {
//    expr_ref neg(m);
//    neg = to_app(t)->get_arg(0);
//    if (!u.is_bv_add(neg)) {
//      res = t;
//      return;
//    }
//    expr_ref_vector tmp(m);
//    expr_ref tmp1(m);
//    for (auto arg : *(to_app(neg))) {
//      mk_neg(arg, tmp1);
//      tmp.push_back(tmp1);
//    }
//    mk_add(tmp, res);
//  }
//  else res = t;
//}

// rewrite lhs <= rhs so that var to the form t <= k * var or k * var <= t
// requires var is either in lhs or rhs but not both
// requires model satisfies sc
bool rewrite_ule(expr_ref var, expr *lhs, expr *rhs, model &mdl,
                 expr_ref_vector &res) {
    expr_ref sc1(m), sc2(m), t1(m), t2(m), t2_neg(m), t3(m), nw_rhs(m), nw_lhs(m);
    if (!(contains(lhs, var) ^ contains(rhs, var))) return false;

    TRACE("qe",
          tout << "Trying to normalize ule " << mk_pp(lhs, m) << " leq " << mk_pp(rhs, m) << " wrt var " << var << "\n";);
    // if already in normal form, return true
    // TODO check whether lhs = c * var
    if (lhs == var || rhs == var) {
        res.push_back(u.mk_ule(lhs, rhs));
        return true;
    }

    split_legacy(var, lhs, rhs, t1, t2, t2_neg, t3);
    bool lhs_var = contains(lhs, var);
    expr_ref r(m), t(m);
    t = m.mk_not(u.mk_ule(t2, t1));
    bool n1 = push_not(t, r, sc1, mdl);
    sc2 = u.mk_ule(t2_neg, t3);
    if (!(n1 && mdl.is_true(r) && mdl.is_true(sc1) && mdl.is_true(sc2))) {
        TRACE("qe", tout << "sc " << sc1 << " and " << sc2  << " and " << r << "not true in model " << mdl << "\n";);
        return false;
    }
    res.push_back(r);
    res.push_back(sc1);
    res.push_back(sc2);
    if (lhs_var) {
        SASSERT(contains(t1, var));
        mk_add(t3, t2_neg, nw_rhs);
        res.push_back(u.mk_ule(t1, nw_rhs));
        return true;
    }
    else {
        SASSERT(contains(t3, var));
        mk_add(t1, t2_neg, nw_lhs);
        res.push_back(u.mk_ule(nw_lhs, t3));
        return true;
    }
}

bool rewrite_ule_alt(expr_ref var, expr *lhs, expr *rhs, model &mdl, expr_ref_vector &res) {
    if (contains_num(lhs, var) + contains_num(rhs, var) != 1) return false;

    expr_ref sc1(m), sc2(m), t1(m), t2(m), t2_neg(m), t3(m), tmp(m), nw_rhs(m), nw_lhs(m), bv_zero(m), bv_one(m);
    unsigned sz = u.get_bv_size(var);
    bv_zero = u.mk_numeral(rational::zero(), sz);
    bv_one = u.mk_numeral(rational::one(), sz);

    TRACE("qe",
          tout << "Trying to normalize ule " << mk_pp(lhs, m) << " <= " << mk_pp(rhs, m) << " wrt var " << var << "\n";);

    if (lhs == var || rhs == var){
        res.push_back(u.mk_ule(lhs, rhs));
        return true;
    }

    // try rule [sub1]: if {1 <= var /\ var <= -y} then {y <= -var}
    if (is_bvneg(rhs, var)) {
        mk_neg(lhs, tmp);
        sc1 = u.mk_ule(bv_one, var);
        sc2 = u.mk_ule(var, tmp);
        if (mdl.is_true(sc1) && mdl.is_true(sc2)) {
            TRACE("qe", tout << " applied rule [sub1]\n";);
            res.push_back(sc1);
            res.push_back(sc2);
            return true;
        }
    }

    // try rule [sub2]: if {1 <= y /\ -y <= var} then {-var <= y}
    if (is_bvneg(lhs, var)) {
        mk_neg(rhs, tmp);
        sc1 = u.mk_ule(bv_one, rhs);
        sc2 = u.mk_ule(tmp, var);
        if (mdl.is_true(sc1) && mdl.is_true(sc2)) {
            TRACE("qe", tout << " applied rule [sub2]\n";);
            res.push_back(sc1);
            res.push_back(sc2);
            return true;
        }
    }

    split_legacy(var, lhs, rhs, t1, t2, t2_neg, t3);
    bool lhs_var = contains(lhs, var);
    if (lhs_var) {
        SASSERT(contains(t1, var));
        mk_add(t3, t2_neg, nw_rhs);
        if (mdl.is_true(u.mk_ule(t1, nw_rhs))) {

            // try rule [add2]:  if {y <= z /\ f(var) <= z - y} then {f(var) + y <= z}
            sc1 = u.mk_ule(t2, rhs);
            if (mdl.is_true(sc1)) {
                TRACE("qe", tout << " applied rule [add2]\n";);
                return rewrite_ule_alt(var, t2, rhs, mdl, res) &&
                       rewrite_ule_alt(var, t1, nw_rhs, mdl, res);
            }

            // try rule [add21]: if {-y <= f(var) /\ f(var) <= z - y} then {f(var) + y <= z}
            sc1 = u.mk_ule(t2_neg, t1);
            if (mdl.is_true(sc1)) {
                TRACE("qe", tout << " applied rule [add21]\n";);
                return rewrite_ule_alt(var, t2_neg, t1, mdl, res) &&
                       rewrite_ule_alt(var, t1, nw_rhs, mdl, res);
            }
        }
        else if (mdl.is_true(u.mk_ule(t1, rhs))) {

            // try rule [add22]: if {y <= z /\ f(var) <= z} then {f(var) + y <= z}
            TRACE("qe", tout << " applied rule [add22]\n";);
            return rewrite_ule_alt(var, t2, rhs, mdl, res) &&
                   rewrite_ule_alt(var, t1, rhs, mdl, res);
        }
    }
    else {
        SASSERT(contains(t3, var));
        mk_add(t1, t2_neg, nw_lhs);
        if (!mdl.is_true(u.mk_ule(nw_lhs, t3))) return false;

        // try rule [add4]:  if {f(var) < -y /\ z - y <= f(var)} then {z <= f(var) + y}
        mk_neg(bv_one, tmp);
        mk_add(t2_neg, tmp, tmp);
        sc1 = u.mk_ule(bv_one, t2_neg);
        sc2 = u.mk_ule(t3, tmp);
        if (mdl.is_true(sc1) && mdl.is_true(sc2)) {
            TRACE("qe", tout << " applied rule [add4]\n";);
            return rewrite_ule_alt(var, bv_one, t2_neg, mdl, res) &&
                   rewrite_ule_alt(var, t3, nw_lhs, mdl, res);
        }

        // try rule [add41]: if {z < y /\ z - y <= f(var)} then {z <= f(var) + y}
        mk_neg(bv_one, tmp);
        mk_add(t2, tmp, tmp);
        sc1 = u.mk_ule(bv_one, t2);
        sc2 = u.mk_ule(lhs, tmp);
        if (mdl.is_true(sc1) && mdl.is_true(sc2)) {
            TRACE("qe", tout << " applied rule [add42]\n";);
            return rewrite_ule_alt(var, bv_one, t2, mdl, res) &&
                   rewrite_ule_alt(var, t3, nw_lhs, mdl, res);
        }
    }
    return false;
}

bool is_bvneg(expr *e, expr_ref v) {
    rational bnd = rational::power_of_two(u.get_bv_size(v)) - 1;
    if (u.is_bv_neg(e))
        return (v == to_app(e)->get_arg(0));
    else {
        expr *t1, *t2;
        rational val;
        if (u.is_bv_mul(e, t1, t2)) {
            if (u.is_numeral(t1, val) && t2 == v && val == bnd) return true;
            if (u.is_numeral(t2, val) && t1 == v && val == bnd) return true;
        }
        return false;
    }
}

void handle_eq(expr_ref var, expr *lhs, expr *rhs, expr_ref_vector &res) {
    expr_ref t1(m), t2(m), t2_neg(m), t3(m), nw_rhs(m), nw_lhs(m);
    if (contains_num(lhs, var) + contains_num(rhs, var) != 1) return;

    if (lhs == var) {
        res.push_back(rhs);
        return;
    } else if (rhs == var) {
        res.push_back(lhs);
        return;
    }

    split_legacy (var, lhs, rhs, t1, t2, t2_neg, t3);

    bool succ = false;
    if (contains(lhs, var)) {
        mk_add (t3, t2_neg, nw_rhs);
        succ = extract_assgn(t1, nw_rhs, var, res);
    } else {
        mk_add (t1, t2_neg, nw_lhs);
        succ = extract_assgn(t3, nw_lhs, var, res);
    }
    if (succ)
    {
        TRACE("qe", tout <<
                  "equality handling:  " << mk_pp(var, m) << " = " << mk_pp(res.back(), m) << "for \n" <<
                                            mk_pp(lhs, m) << " = " << mk_pp(rhs, m) << "\n";);
        SASSERT(!is_sat(m.mk_eq(var, res.back()), m.mk_not(m.mk_eq(lhs,rhs))) &&
                !is_sat(m.mk_not(m.mk_eq(var, res.back())), m.mk_eq(lhs,rhs)));
    }
}

bool extract_assgn(expr *lhs, expr *rhs, expr_ref var, expr_ref_vector &res) {
    if (contains(rhs, var)) return false;

    bool is_neg = is_bvneg(lhs, var);
    if (is_neg) {
        res.push_back(u.mk_bv_neg(rhs));
        return true;
    }
    else if (lhs == var)
    {
        res.push_back(rhs);
        return true;
    }
    return false;
}

// Tom - why not do big equality between tmm?
bool resolve_eqs(expr_ref_vector &res, expr_ref v) {
    expr_ref_vector tmm(m);
    for (unsigned f_num = 0; f_num < res.size(); f_num++) {
        expr_ref f(res.get(f_num), m);
        expr *lhs, *rhs;
        if (m.is_eq(f, lhs, rhs)) handle_eq(v, lhs, rhs, tmm);
    }

    if (tmm.size() > 0) {
        TRACE("qe", tout << "resolve based on equalities " << mk_pp(v, m) << "\n";);
        for (unsigned f_num = 0; f_num < res.size(); f_num++) {
            expr_safe_replace sub(m);
            sub.insert(v, tmm.get(0)); // here, we use only the first elem, but in principle can any other
            expr_ref tmp(m);
            sub(res.get(f_num), tmp);
            res.set(f_num, tmp);
        }
        return true;
    }
    return false;
}

void handle_signed(expr* lhs, expr* rhs, expr_ref_vector &res, model &mdl) {
    //assumes u.is_bv_sle(rw, lhs, rhs), TODO: extend

    unsigned sz = u.get_bv_size(lhs);
    expr_ref sc1(m), sc2(m), sc3(m), sc4(m), b1(m), b2(m);
    b1 = u.mk_numeral(rational::power_of_two(sz-1) - 1, sz);
    b2 = u.mk_numeral(rational::power_of_two(sz-1), sz);
    sc1 = u.mk_ule(lhs, b1);
    sc2 = u.mk_ule(rhs, b1);
    sc3 = u.mk_ule(b2, lhs);
    sc4 = u.mk_ule(b2, rhs);
    if (mdl.is_true(sc1) && mdl.is_true(sc2)) {
        res.push_back(sc1);
        res.push_back(sc2);
        res.push_back(u.mk_ule(lhs, rhs));
    }
    else if (mdl.is_true(sc1) && mdl.is_true(sc4)) {
        res.push_back(sc1);
        res.push_back(sc4);
        res.push_back(u.mk_ule(b2, lhs));
        res.push_back(u.mk_ule(rhs, b2));
    }
    else if (mdl.is_true(sc3) && mdl.is_true(sc2)) {
        res.push_back(sc3);
        res.push_back(sc2);
        res.push_back(u.mk_ule(b2, lhs));
        res.push_back(u.mk_ule(rhs, b2));
    }
    else if (mdl.is_true(sc3) && mdl.is_true(sc4)) {
        res.push_back(sc3);
        res.push_back(sc4);
        res.push_back(u.mk_ule(lhs, rhs));
    }
    else SASSERT(0);
}


bool normalize_legacy(expr_ref var, expr_ref f, model &mdl, expr_ref_vector &res) {
    expr_ref rw(f, m), sc(m);
    expr *lhs, *rhs;
    TRACE("qe",
          tout << "Trying to normalize " << f << " wrt var " << var << "\n";);
    if (!contains(f, var)) {
        res.push_back(f);
        return true;
    }
    if (unhandled_legacy(f, var)) {
        TRACE("qe", tout << "Operation not handled " << f << " on var " << var << "\n";);
        return false;
    }
    if (m.is_not(f)) {
        if (!push_not(f, rw, sc, mdl))
            return false;
        // normalize both the expression inside f and the side condition produced
        bool n1 = normalize_legacy(var, rw, mdl, res);
        if (sc.get() != nullptr)
            n1 = n1 && normalize_legacy(var, sc, mdl, res);
        return n1;
    }
    if (m.is_eq(rw, lhs, rhs)) {
        expr_ref t(m);
        t = u.mk_ule(lhs, rhs);
        bool n1 = normalize_legacy(var, t, mdl, res);
        t = u.mk_ule(rhs, lhs);
        n1 = n1 && normalize_legacy(var, t, mdl, res);
        return n1;
    }
    if (u.is_bv_sle(rw, lhs, rhs)) {
        expr_ref_vector all(m);
        handle_signed(lhs, rhs, all, mdl);
        bool n = true;
        for (auto a : all)
            n &= normalize_legacy(var, expr_ref(a, m), mdl, res);
        return n;
    }
    if (!u.is_bv_ule(rw, lhs, rhs))
        return false;
    return rewrite_ule_alt(var, lhs, rhs, mdl, res);
}

void get_lbs(expr_ref var, expr_ref_vector& f, expr_ref_vector& lbs) {
    expr *lhs, *rhs;
    for (auto a : f) {
        if (contains(a, var)) {
            if (u.is_bv_ule(a, lhs, rhs) && !contains(lhs, var) && contains(rhs, var))
                lbs.push_back(a);
        }
    }
}

void get_ubs(expr_ref var, expr_ref_vector &f, expr_ref_vector &ubs) {
  expr *lhs, *rhs;
  for (auto a : f) {
    if (contains(a, var)) {
      if (u.is_bv_ule(a, lhs, rhs) && contains(lhs, var) && !contains(rhs, var))
        ubs.push_back(a);
    }
  }
}

rational get_coeff(expr* a, expr_ref var) {
    if (!contains(a, var)) return rational::zero();
    if (a == var.get()) return rational::one();
    expr *t1, *t2;
    if (u.is_bv_mul(a, t1, t2)) {
        rational o_coeff;
        SASSERT(u.is_numeral(t1));
        u.is_numeral(t1, o_coeff);
        return o_coeff * get_coeff(t2, var);
    }
    for (auto t : *to_app(a)) {
        if (contains(t, var)) return get_coeff(t, var);
    }
    return rational::zero();
}

//lcm of coefficients of var in f
rational get_lcm(expr_ref_vector& f, expr_ref var) {
    rational l = rational::one();
    for(auto a : f) {
        rational c = get_coeff(a, var);
        l = lcm(l, c);
    }
    return l;
}



expr* find_glb(model &mdl, expr_ref_vector& lbs) {
    expr_ref res(m);
    expr *r = lbs.get(0);
    rational val, glb(0);
    for (auto a : lbs) {
        mdl.eval_expr(to_app(a)->get_arg(0), res);
        SASSERT(u.is_numeral(res));
        if (u.is_numeral(res, val) && glb < val) {
            r = a;
            glb = val;
        }
    }
    return r;
}

expr *find_lub(model &mdl, expr_ref_vector &ubs) {
  expr_ref res(m);
  expr *r = ubs.get(0);
  rational val, lub;
  mdl.eval_expr(to_app(ubs[0].get())->get_arg(1), res);
  if (!u.is_numeral(res, lub))
      return nullptr;
  for (auto a : ubs) {
    mdl.eval_expr(to_app(a)->get_arg(1), res);
    SASSERT(u.is_numeral(res));
    if (u.is_numeral(res, val) && lub > val) {
      r = a;
      lub = val;
    }
  }
  return r;
}


// resolve a1 <= a_c*var with b_c*var <= b2 to get (a_lhs * (lcm/a_c))/lcm <= (b_rhs *(lcm/b_c))/lcm
void resolve(expr* a, expr* b, rational lcm, expr_ref var, expr_ref& res) {
    SASSERT(u.is_bv_ule(a));
    SASSERT(u.is_bv_ule(b));
    rational b_c = get_coeff(b, var);
    rational a_c = get_coeff(a, var);
    SASSERT(!b_c.is_zero() && !a_c.is_zero());
    if (lcm.is_one()) {
        SASSERT(a_c.is_one());
        SASSERT(b_c.is_one());
        res = u.mk_ule(to_app(a)->get_arg(0), to_app(b)->get_arg(1));
    }
    else {
        return;
        NOT_IMPLEMENTED_YET();
    }
}

// generates an under-approximation for some literals in f
// modifies f, res and bd_fmls
void resolve_boundaries(expr_ref var, expr_ref_vector &f, model &mdl,
             expr_ref_vector &res, expr_ref_vector& bd_fmls) {
    if (f.empty())
        return;
    expr_ref_vector lbs(m), ubs(m);
    get_lbs(var, f, lbs); //t <=_u s*x -- in paper this should be < - TODO fix
    get_ubs(var, f, ubs); //s*x <=_u t -- this is ok
    if (ubs.size() == f.size() || lbs.size() == f.size()) {
        bd_fmls.reset();
        res.push_back(m.mk_true());
        return;
    }
    TRACE("qe", tout << "trying to resolve " << mk_and(ubs) << " and " << mk_and(lbs) << "\n";);
    SASSERT(ubs.size() + lbs.size() == f.size());
    expr *ub, *lb;
    expr_ref nw_lhs(m), nw_rhs(m), r(m);
    rational lcm = get_lcm(f, var);
    lb = find_glb(mdl, lbs);
    ub = find_lub(mdl, ubs);
    TRACE("qe", tout << "the upper bound is " << mk_pp(ub, m) << " and the lower bound is " << mk_pp(lb, m) << "\n";);
    rational ub_c = get_coeff(ub, var);
    rational lb_c = get_coeff(lb, var);
    expr_ref_vector sc(m);
    unsigned sz = u.get_bv_size(var);
    if (!lcm.is_one()) {
        // side conditions to ensure no overflow occurs
        for (auto a : lbs) {
            rational a_c = get_coeff(to_app(a)->get_arg(1), var);
            SASSERT(!a_c.is_zero());
            rational bnd = div(rational::power_of_two(sz) - 1, div(lcm, a_c));
            rational val;
            if(u.is_numeral(to_app(a)->get_arg(0), val) && val <= bnd) continue;
            r = u.mk_ule(to_app(a)->get_arg(0), u.mk_numeral(bnd, sz));
            res.push_back(r);
            sc.push_back(r);
            TRACE("qe", tout << "added sc " << r << "\n";);
        }
        for (auto a : ubs) {
            rational a_c = get_coeff(to_app(a)->get_arg(0), var);
            SASSERT(!a_c.is_zero());
            rational bnd = div(rational::power_of_two(sz) - 1, div(lcm, a_c));
            rational val;
            if(u.is_numeral(to_app(a)->get_arg(1), val) && val <= bnd) continue;
            r = u.mk_ule(to_app(a)->get_arg(1), u.mk_numeral(bnd, sz));
            res.push_back(r);
            sc.push_back(r);
            TRACE("qe", tout << "added sc " << r << "\n";);
        }
    }

    //compare all lbs against lb
    mk_mul(to_app(lb)->get_arg(0), div(lcm, lb_c), nw_rhs);
    for (auto a : lbs) {
        if (a == lb) continue;
        rational c = get_coeff(to_app(a)->get_arg(1), var);
        mk_mul(to_app(a)->get_arg(0), div(lcm, c), nw_lhs);
        r = u.mk_ule(nw_lhs, nw_rhs);
        res.push_back(r);
        TRACE("qe", tout << "lb comparison produced " << r << "\n";);
    }

    //resolve all ubs against lb
    for (auto a : ubs) {
        resolve(lb, a, lcm, var, r);
        res.push_back(r);
        TRACE("qe", tout << "resolve produced " << r << "\n";);
    }

    //check if any side conditions failed
    if (!mdl.is_true(mk_and(sc))) {
        bd_fmls.reset(); // Tom
        bd_fmls.append(f);
        //f.reset(); - Tom
        res.reset();
    }
    return;
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
};

/**********************************************************/
/*  bv_project_plugin implementation                     */
/**********************************************************/
bv_project_plugin::bv_project_plugin(ast_manager &m) { m_imp = alloc(imp, m); }

bv_project_plugin::~bv_project_plugin() { dealloc(m_imp); }

bool bv_project_plugin::operator()(model &model, app *var, app_ref_vector &vars,
                                   expr_ref_vector &lits) {
    return (*m_imp)(model, var, vars, lits);
}

void bv_project_plugin::operator()(model &model, app_ref_vector &vars,
                                   expr_ref_vector &lits) {
    // everytime I call mbp for all vars I need to try to remove 0 handling ops
    //replace_zero_handle_ops(model, lits);
    //ast_manager m = model.get_manager();
    //expr_ref sanity(mk_and(lits), m);
    //SASSERT(model.is_true(sanity));
    fp_params const & f = fp_params();
    unsigned projection_mode = f.spacer_use_bv_mbp();
    std::cout << "Projection_mode is "<< projection_mode <<std::endl;
    if (projection_mode == 0)
      m_imp->project(model, vars, lits, false);
    else if (projection_mode == 1) {
      m_imp->project_old_norm(model, vars, lits, false);
    }
}


vector<def> bv_project_plugin::project(model &model, app_ref_vector &vars,
                                       expr_ref_vector &lits) {
    //replace_zero_handle_ops(model, lits);
    //ast_manager m = model.get_manager();
    //expr_ref sanity(mk_and(lits), m);
    //SASSERT(model.is_true(sanity));
    return m_imp->project(model, vars, lits, true);
}

void bv_project_plugin::set_check_purified(bool check_purified) {
    NOT_IMPLEMENTED_YET();
}

bool bv_project_plugin::solve(model &model, app_ref_vector &vars,
                              expr_ref_vector &lits) {
    return m_imp->solve(model, vars, lits);
}

family_id bv_project_plugin::get_family_id() {
    return m_imp->u.get_family_id();
}

opt::inf_eps bv_project_plugin::maximize(expr_ref_vector const &fmls,
                                         model &mdl, app *t, expr_ref &ge,
                                         expr_ref &gt) {
    NOT_IMPLEMENTED_YET();
    opt::inf_eps value;
    return value;
}

void bv_project_plugin::saturate(model &model,
                                 func_decl_ref_vector const &shared,
                                 expr_ref_vector &lits) {
    NOT_IMPLEMENTED_YET();
}

} // namespace qe
