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

        for (unsigned f_num = 0; f_num < res.size(); f_num++) {
            expr_ref f(res.get(f_num), m);

            // background fmls
            if (!contains(f, v)) {
                backg_fmls.push_back(f);
                continue;
            }

            // normalize and add to pi
            if (normalize(v, f, model, norm)) {
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
        sig.append(bd_fmls);
        pi.append(norm_fmls);

        // TODO maybe do this after projecting all the vars ?
        if (!sig.empty()) {
            TRACE("qe", tout << "calling lazy mbp with pi " << mk_and(pi) << " and sig " << mk_and(sig) << "\n";);
            lazy_mbp(pi, sig, v, new_fmls, model);
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
    return vector<def>();
}

// computes mbp(pi && sig, model, v)
// input: new_fmls ==> \exist v pi
// output: new_fmls ==> \exists v pi && sig
void lazy_mbp(expr_ref_vector &pi, expr_ref_vector &sig, expr_ref v,
              expr_ref_vector &new_fmls, model &model) {
    expr_ref negged_quant_conj(m);
    negged_quant_conj = m.mk_and(mk_and(pi), mk_and(sig));
    if (contains(negged_quant_conj, v)) {
        app_ref_vector vec(m);
        vec.push_back(to_app(v.get()));
        mk_exists(negged_quant_conj, vec, negged_quant_conj);
    }
    negged_quant_conj = m.mk_not(negged_quant_conj);

    expr_ref new_fmls_conj(m);
    new_fmls_conj = mk_and(new_fmls);

    expr_ref_vector substs(m);
    for (auto f : sig) {
        substs.push_back(get_subst(model, v, f));
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
        expr_ref new_subst = get_subst(model, v, f);
        substs.push_back(new_subst);

        if (!is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj))
            break;
    }

    TRACE("qe", tout << "\nLazy MBP completed. sig size " << init_sz << " substitutions in pi " << substs.size() - init_sz << " and pi size " << pi.size()  << "\n";);
    new_fmls.append(substs);
}

expr_ref get_subst(model &model, expr *v, expr *f) {
    expr_ref subst(m);
    expr_safe_replace sub(m);
    sub.insert(v, model(v));
    sub(f, subst);
    th_rewriter m_rw(m);
    m_rw(subst);
    return subst;
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
        SASSERT(mdl.is_true(sc));
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
    if (u.is_numeral(f, val)) {
        if (val == rational::zero())
            res = f;
        else {
            const unsigned sz = u.get_bv_size(f);
            rational neg = rational::power_of_two(sz) - 1 - val;
            res = u.mk_numeral(neg, sz);
        }
    } else
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

// separates lhs, rhs into three parts such that only one contains var
void split(expr_ref var, expr *lhs, expr *rhs, expr_ref& t1, expr_ref& t2, expr_ref& t2_neg, expr_ref& t3) {

  bool lhs_var = contains(lhs, var);
  TRACE("qe", tout << "Trying to split " << mk_pp(lhs, m) << " leq "
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
        t2 = u.mk_numeral(rational(0), u.get_bv_size(var));
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
    sc1 = u.mk_ule(t1, t2);
    sc2 = u.mk_ule(t2_neg, t3);
    if (mdl.is_true(sc1) && mdl.is_true(sc2)) {
        TRACE("qe", tout << "sc not true in model\n";);
        return false;
    }
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

bool normalize(expr_ref var, expr_ref f, model &mdl, expr_ref_vector &res) {
    expr_ref rw(f, m), sc(m);
    expr *lhs, *rhs;
    TRACE("qe",
          tout << "Trying to normalize " << f << " wrt var " << var << "\n";);
    if (!contains(f, var)) {
        res.push_back(f);
        return true;
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
    if (!u.is_bv_ule(rw, lhs, rhs))
        return false;
    return rewrite_ule(var, lhs, rhs, mdl, res);
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
    SASSERT(u.is_bv_add(a));
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
    expr *r = nullptr;
    rational val, glb(0);
    for (auto a : lbs) {
        mdl.eval_expr(to_app(a)->get_arg(0), res);
        if (u.is_numeral(res, val) && glb < val) {
            r = a;
        }
    }
    return r;
}

expr *find_lub(model &mdl, expr_ref_vector &ubs) {
  expr_ref res(m);
  expr *r = ubs.get(0);
  rational val, lub;
  mdl.eval_expr(to_app(ubs[0].get())->get_arg(0), res);
  if (!u.is_numeral(res, lub))
      return nullptr;

  for (auto a : ubs) {
    mdl.eval_expr(to_app(a)->get_arg(0), res);
    if (u.is_numeral(res, val) && lub > val) {
      r = a;
    }
  }
  return r;
}

void mk_mul(expr* a, rational b, expr_ref& o) {
    rational val;
    unsigned sz = u.get_bv_size(a);
    if (u.is_numeral(a, val)) {
        o = u.mk_numeral(val * b, sz);
        return;
    }
    o = u.mk_bv_mul(u.mk_numeral(b, sz), a);
}

// resolve a1 <= a_c*var with b_c*var <= b2 to get a_lhs * (lcm/a_c)/lcm <= b_rhs *(lcm/b_c)/lcm
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
        rational c1 = div(div(lcm, a_c), lcm);
        rational c2 = div(div(lcm, b_c), lcm);
        expr_ref nw_lhs(m), nw_rhs(m);
        mk_mul(to_app(a)->get_arg(0), c1, nw_lhs);
        mk_mul(to_app(b)->get_arg(1), c2, nw_rhs);
        res = u.mk_ule(nw_lhs, nw_rhs);
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
    ub = find_glb(mdl, lbs);
    lb = find_lub(mdl, ubs);
    rational ub_c = get_coeff(ub, var);
    rational lb_c = get_coeff(lb, var);
    expr_ref_vector sc(m);
    expr_ref val(m);
    mdl.eval_expr(var, val);
    unsigned sz = u.get_bv_size(val);

    // side conditions to ensure no overflow occurs
    for (auto a : lbs) {
        rational a_c = get_coeff(to_app(a)->get_arg(1), var);
        SASSERT(!a_c.is_zero());
        rational bnd = div(rational::power_of_two(sz) - 1, div(lcm, a_c));
        r = u.mk_ule(to_app(a)->get_arg(0), u.mk_numeral(bnd, sz));
        res.push_back(r);
        sc.push_back(r);
    }

    for (auto a : ubs) {
      rational a_c = get_coeff(to_app(a)->get_arg(0), var);
      SASSERT(!a_c.is_zero());
      rational bnd = div(rational::power_of_two(sz) - 1, div(lcm, a_c));
      r = u.mk_ule(to_app(a)->get_arg(1), u.mk_numeral(bnd, sz));
      res.push_back(r);
      sc.push_back(r);
    }


    //compare all lbs against lb
    for (auto a : lbs) {
        if (a == lb) continue;
        expr_ref nw_lhs(m);
        rational c = get_coeff(to_app(a)->get_arg(1), var);
        mk_mul(to_app(a)->get_arg(0), div(lcm, c), nw_lhs);
        res.push_back(u.mk_ule(nw_lhs, to_app(a)->get_arg(0)));
    }

    //resolve all ubs against lb
    for (auto a : ubs) {
        resolve(a, lb, lcm, var, r);
        res.push_back(r);
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
    return (sol->check_sat(0, nullptr) == l_true);
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
