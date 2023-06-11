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

bool unhandled(expr *f, expr_ref var) {
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
        return unhandled(a, var);
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
// separates lhs, rhs into three parts such that only one contains var
void split(expr_ref var, expr *lhs, expr *rhs, expr_ref& t1, expr_ref& t2, expr_ref& t2_neg, expr_ref& t3) {
  ast_manager &m = var.get_manager();
  bool lhs_var = contains(lhs, var);
  TRACE("qe", tout << "Trying to split " << mk_pp(lhs, m) << " tilda "
                   << mk_pp(rhs, m) << " wrt var " << var << "\n";);

  if (lhs_var) {
      split_term(var, lhs, t1, t2, t2_neg);
      t3 = rhs;
  }
  else {
      split_term(var, rhs, t3, t2, t2_neg);
      t1 = lhs;
  }
  return;
}

// splits exp into terms t and t2 such that exp = t + t2 and t contains var
void split_term(expr_ref var, expr* exp, expr_ref& t, expr_ref& t2, expr_ref& t2_neg) {
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
void replace_zero_handle_ops(model& model, expr_ref_vector& fmls) {
  ast_manager& m = model.get_manager();
  bv_util m_bv(m);
  expr_ref_vector new_fmls(m);
  expr_ref lhs(m), rhs(m), exp1(m), exp2(m),  zero(m);
  decl_kind operation;
  unsigned sz;
  new_fmls.reset();
  for (auto *fml : fmls) {
    operation = fml->get_kind();
    if (operation != OP_ULT && operation != OP_ULEQ && operation != OP_SLEQ && operation != OP_SLT && operation != OP_EQ) {
      continue;
    }
    lhs = to_app(fml)->get_arg(0);
    rhs = to_app(fml)->get_arg(1);
    sz = m_bv.get_bv_size(fml);
    zero = m_bv.mk_numeral(rational::zero(), sz);
    if (m_bv.is_bv_urem0(lhs) || m_bv.is_bv_uremi(lhs)) {
      exp1 = to_app(lhs)->get_arg(0);
      exp2 = to_app(lhs)->get_arg(1);
      if (!model.is_true(m.mk_eq(exp2, zero))) {
        new_fmls.push_back(m.mk_app(m_bv.get_family_id(), operation, m_bv.mk_bv_urem(exp1, exp2),rhs));
        continue;
      }
    }
    if (m_bv.is_bv_urem0(rhs) || m_bv.is_bv_uremi(rhs)) {
      exp1 = to_app(rhs)->get_arg(0);
      exp2 = to_app(rhs)->get_arg(1);
      if (!model.is_true(m.mk_eq(exp2, zero))) {
        new_fmls.push_back(m.mk_app(m_bv.get_family_id(), operation, lhs, m_bv.mk_bv_urem(exp1, exp2)));
        continue;
      }
    }
    if (m_bv.is_bv_udiv0(lhs) || m_bv.is_bv_udivi(lhs)) {
      exp1 = to_app(lhs)->get_arg(0);
      exp2 = to_app(lhs)->get_arg(1);
      if (!model.is_true(m.mk_eq(exp2, zero))) {
        new_fmls.push_back(m.mk_app(m_bv.get_family_id(), operation, m_bv.mk_bv_udiv(exp1, exp2),rhs));
        continue;
      }
    } 
    if (m_bv.is_bv_udiv0(rhs) || m_bv.is_bv_udivi(rhs)) {
      exp1 = to_app(rhs)->get_arg(0);
      exp2 = to_app(rhs)->get_arg(1);
      if (!model.is_true(m.mk_eq(exp2, zero))) {
        new_fmls.push_back(m.mk_app(m_bv.get_family_id(), operation, lhs, m_bv.mk_bv_udiv(exp1, exp2)));
        continue;
      }
    }
    new_fmls.push_back(fml);
  }
  fmls.reset();
  fmls.append(new_fmls);
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
            return m_bv.mk_numeral(rational::power_of_two(sz-1) - 1, sz);
        }

        expr* create_signed_min(unsigned sz) { // TODO test 
            SASSERT(sz > 0);
            return m_bv.mk_numeral(-rational::power_of_two(sz-1), sz);
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

        // check for diseq and move var to the left
        bool is_diseq(expr *e, expr_ref &lhs, expr_ref &rhs) {
          if (!m.is_distinct(e))
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
          if (!m_bv.is_bv_and(e)) return false;
          exp1 = to_app(e)->get_arg(0);
          exp2 = to_app(e)->get_arg(1);
          if (contains(exp1, m_var) == contains(exp1, m_var))
            return false;
          return true;
        }

        bool is_bvor(expr* e, expr_ref &exp1, expr_ref &exp2) {
          if (!m_bv.is_bv_or(e)) return false;
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
      //  if t ≤u (t+t-s) & s  = t then  Exists x. s mod_u x = t
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
        if (sz == 1) {
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

imp(ast_manager &_m) : m(_m), u(m) {
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


~imp() {}

// MAIN PROJECTION FUNCTION
// compute_def is unused
vector<def> project(model &model, app_ref_vector &vars, expr_ref_vector &fmls,
                    bool compute_def) {
    expr_ref_vector res(m);
    res.append(fmls);
    for (unsigned var_num = 0; var_num < vars.size(); var_num++) {
        expr_ref v(vars.get(var_num), m);
        TRACE("qe", tout << "eliminate " << mk_pp(v, m) << "\n";);

        expr_ref_vector new_fmls(m), norm(m), backg_fmls(m), norm_fmls(m);
        expr_ref_vector pi(m), sig(m);

        if (resolve_eqs(res, v)) {
            lazy_mbp(backg_fmls, pi, res, v, new_fmls, model);
            res.reset();
            res.append(new_fmls);
            TRACE("qe", tout << "mbp produced after eqs\n";);
            continue;
        }

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
                pi.push_back(f);
                TRACE("qe", tout << "normalized from " << mk_pp(f, m) << " to "
                      << mk_pp(mk_and(norm), m) << "\n";);
                for (auto a : norm) {
                    // normalization can create side conditions not involving v
                    if (contains(a, v))
                        norm_fmls.push_back(a);
                    else
                        backg_fmls.push_back(a);
                }
                // sanity check. normalization should be an under approximation
                SASSERT(is_sat((mk_and(norm), m.mk_not(f))));
                // sanity check. model satisfies normalized formula
                SASSERT(model.is_true(mk_and(norm)));
            } else {
                TRACE("qe", tout << "could not normalize " << f << " in var " << v
                               << "\n";);
              sig.push_back(f);
            }
        }
        expr_ref_vector bd_fmls(m);
        resolve(v, norm_fmls, model, new_fmls, bd_fmls);
        CTRACE("qe", bd_fmls.size() > 0, tout << " could not resolve out " << mk_and(bd_fmls) << " for var " << v << "\n";);

        // TODO maybe do this after projecting all the vars ?
        if (!sig.empty()) {
            TRACE("qe", tout << "calling lazy mbp with pi " << mk_and(pi) << " and sig " << mk_and(sig) << "\n";);
            lazy_mbp(backg_fmls, pi, sig, v, new_fmls, model);
        }

        res.reset();
        res.append(new_fmls);
        res.append(backg_fmls);
        TRACE("qe", tout << "mbp produced " << mk_and(res) << "\n";);
    }

    // final sanity check
    expr_ref orig_fla(m);
    mk_exists(mk_and(fmls), vars, orig_fla);
    expr_ref mbp(mk_and(res), m);
    SASSERT(model.is_true(mbp));
    SASSERT(!is_sat(mbp, m.mk_not(orig_fla)));
    fmls.reset();
    fmls.append(res);
    // Since lazy_mbp guarentees elimination of all vars, reset vars
    vars.shrink(0);
    return vector<def>();
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

    split(var, lhs, rhs, t1, t2, t2_neg, t3);
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

    split(var, lhs, rhs, t1, t2, t2_neg, t3);
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

    split (var, lhs, rhs, t1, t2, t2_neg, t3);

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


bool normalize(expr_ref var, expr_ref f, model &mdl, expr_ref_vector &res) {
    expr_ref rw(f, m), sc(m);
    expr *lhs, *rhs;
    TRACE("qe",
          tout << "Trying to normalize " << f << " wrt var " << var << "\n";);
    if (!contains(f, var)) {
        res.push_back(f);
        return true;
    }
    if (unhandled(f, var)) {
        TRACE("qe", tout << "Operation not handled " << f << " on var " << var << "\n";);
        return false;
    }
    if (m.is_not(f)) {
        if (!push_not(f, rw, sc, mdl))
            return false;
        // normalize both the expression inside f and the side condition produced
        bool n1 = normalize(var, rw, mdl, res);
        if (sc.get() != nullptr)
            n1 = n1 && normalize(var, sc, mdl, res);
        return n1;
    }
    if (m.is_eq(rw, lhs, rhs)) {
        expr_ref t(m);
        t = u.mk_ule(lhs, rhs);
        bool n1 = normalize(var, t, mdl, res);
        t = u.mk_ule(rhs, lhs);
        n1 = n1 && normalize(var, t, mdl, res);
        return n1;
    }
    if (u.is_bv_sle(rw, lhs, rhs)) {
        expr_ref_vector all(m);
        handle_signed(lhs, rhs, all, mdl);
        bool n = true;
        for (auto a : all)
            n &= normalize(var, expr_ref(a, m), mdl, res);
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
        NOT_IMPLEMENTED_YET();
    }
}

// generates an under-approximation for some literals in f
// modifies f, res and bd_fmls
void resolve(expr_ref var, expr_ref_vector &f, model &mdl,
             expr_ref_vector &res, expr_ref_vector& bd_fmls) {
    if (f.empty())
        return;
    expr_ref_vector lbs(m), ubs(m);
    get_lbs(var, f, lbs);
    get_ubs(var, f, ubs);
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
        bd_fmls.append(f);
        f.reset();
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
    m_imp->project(model, vars, lits, false);
}

vector<def> bv_project_plugin::project(model &model, app_ref_vector &vars,
                                       expr_ref_vector &lits) {
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
