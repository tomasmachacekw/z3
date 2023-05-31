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
#include "ast/expr_abstract.h"
#include "ast/rewriter/ast_counter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "cmd_context/cmd_context.h"
#include "model/model_smt2_pp.h"
#include "smt/smt_solver.h"

namespace qe {

struct bv_project_plugin::imp {
ast_manager &m;
bv_util u;

imp(ast_manager &_m) : m(_m), u(m) {}
~imp() {}

bool contains(expr *e, expr *v) {
    if (e == v)
        return true;
    else {
        bool found = false;
        for (expr *arg : *to_app(e)) {
            found |= contains(arg, v);
            if (found)
                break;
        }
        return found;
    }
}

unsigned num_occurs(expr *e, expr *v) {
    if (e == v)
        return 1;
    else {
        int num = 0;
        for (expr *arg : *to_app(e)) {
            num += num_occurs(arg, v);
        }
        return num;
    }
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

void mk_neg(expr *f, expr_ref &res) {
    rational val;
    expr *t1, *t2 = nullptr;
    const unsigned sz = u.get_bv_size(f);
    rational bnd = rational::power_of_two(sz) - 1;

    if (u.is_numeral(f, val)) {
        if (val == rational::zero())
            res = f;
        else {
            rational neg = rational::power_of_two(sz) - val;
            res = u.mk_numeral(neg, sz);
        }
    }
    else if (u.is_bv_neg(f))
        res = (to_app(f)->get_arg(0));
    else if (u.is_bv_mul(f, t1, t2)) {
        if (u.is_numeral(t1, val) && val == bnd)
            res = t2;
        else if (u.is_numeral(t2, val) && val == bnd)
            res = t1;
        else
            res = u.mk_bv_neg(f);
    }
    else if (u.is_bv_add(f)) {
        expr_ref_vector tmp(m);
        expr_ref tmp1(m);
        for (auto arg : *(to_app(f))) {
            mk_neg(arg, tmp1);
            tmp.push_back(tmp1);
        }
        mk_add(tmp, res);
    }
    else
        res = u.mk_bv_neg(f);
}

void mk_add(expr_ref_vector &f, expr_ref &res) {
  if (f.size() == 1)
    res = f.get(0);
  else if (f.size() != 0)
    res = m.mk_app(u.get_fid(), OP_BADD, f.size(), f.c_ptr());
}

void flatten_add(expr_ref t1, expr_ref_vector& res) {
    if (t1.get() == nullptr) return;
    if (!u.is_bv_add(t1)) {
        res.push_back(t1);
        return;
    }
    rational val, sum = rational::zero();
    unsigned sz = u.get_bv_size(t1.get());
    expr_ref flt(m);
    for (auto arg : *(to_app(t1))) {
        flatten_term(arg, flt);
        if (u.is_numeral(flt, val)) sum = sum + val;
        else
            res.push_back(flt);
    }
    if (!sum.is_zero())
        res.push_back(u.mk_numeral(sum, sz));
}

void flatten_term (expr* t, expr_ref& res) {
    expr* neg;
    if (u.is_bv_neg(t)) {
        neg = to_app(t)->get_arg(0);
        if (u.is_bv_neg(neg)) {
            res = to_app(neg)->get_arg(0);
            return;
        }
        if (u.is_numeral(neg)) {
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

// separates lhs, rhs into three parts such that only one contains var
void split(expr_ref var, expr *lhs, expr *rhs, expr_ref& t1, expr_ref& t2, expr_ref& t2_neg, expr_ref& t3) {

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
    SASSERT(contains(exp, var));
    if (!u.is_bv_add(exp)) {
        t = exp;
        t2 = u.mk_numeral(rational(0), u.get_bv_size(exp));
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
    if (num_occurs(lhs, var) + num_occurs(rhs, var) != 1) return false;

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
    if (num_occurs(lhs, var) + num_occurs(rhs, var) != 1) return;

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

bool unhandled(expr *f, expr_ref var) {
    SASSERT(contains(f, var));
    if (is_uninterp(f)) return false;
    if (u.is_bv_sdiv(f) || u.is_bv_udiv(f)) return true;
    if (u.is_bv_smod(f) || u.is_bv_smodi(f) || u.is_bv_smod0(f)) return true;
    if (u.is_bv_urem(f) || u.is_bv_urem0(f) || u.is_bv_uremi(f)) return true;
    if (u.is_extract(f) || u.is_concat(f)) return true;
    for (auto a : *(to_app(f))) {
        if (!contains(a, var)) continue;
        return unhandled(a, var);
    }
    return false;
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

void mk_mul(expr* a, rational b, expr_ref& o) {
    rational val;
    if (b.is_one()) {
        o = a;
        return ;
    }
    unsigned sz = u.get_bv_size(a);
    if (u.is_numeral(a, val)) {
        o = u.mk_numeral(val * b, sz);
        return;
    }
    o = u.mk_bv_mul(u.mk_numeral(b, sz), a);
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
