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
                // norm_fmls.push_back(mk_and(norm));
                // sanity check. normalization should be an under approximation
                SASSERT(is_sat((mk_and(norm), m.mk_not(f))));
                // sanity check. model satisfies normalized formula
                SASSERT(m.is_true(mk_and(norm)));
                pi.push_back(f);
            } else {
                sig.push_back(f);
            }
        }
        resolve(v, norm_fmls, model, new_fmls);

        // TODO maybe do this after projecting all the vars ?
        if (!sig.empty()) {
            lazy_mbp(pi, sig, v, new_fmls, model);
        }

        res.reset();
        res.append(new_fmls);
        res.append(backg_fmls);
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
    unsigned stren_sz = init_sz;

    if (is_sat(new_fmls_conj, mk_and(substs), negged_quant_conj)) {
        for (auto &f : pi) {
            // too weak; add missing substs
            expr_ref new_subst = get_subst(model, v, f);
            substs.push_back(new_subst);
        }
        stren_sz = substs.size();
    }

    expr_ref_vector substs_tmp(m); // backup copy
    substs_tmp.append(substs);

    // todo: possibly, optimize with incremental SMT
    for (unsigned k = 0; k < substs.size();) {
        expr_ref_vector tmp(m);
        for (unsigned l = 0; l < substs.size(); l++)
            if (k != l)
                tmp.push_back(substs.get(l));

        expr_ref tmp_conj(m);
        tmp_conj = mk_and(tmp);

        if (is_sat(new_fmls_conj, tmp_conj, negged_quant_conj))
            k++;
        else {
            // erase k:
            for (unsigned m = k; m < substs.size() - 1; m++)
                substs.set(m, substs.get(m + 1));
            substs.pop_back();
        }
    }

    verbose_stream() << "\nLazy MBP completed: " << init_sz << " -> "
                     << stren_sz << " -> " << substs.size() << " conjuncts\n";
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

bool push_not(expr_ref f, expr_ref &res, expr_ref &sc, model &mdl) {
    expr_ref rw(m);
    expr *lhs, *rhs;
    SASSERT(m.is_not(f));
    rw = to_app(f)->get_arg(0);
    TRACE("qe", tout << "Trying to push not into " << rw << "\n";);

    if (u.is_bv_ule(rw, rhs, lhs)) {
        // not(a <= b) <==> b <= a && b <= 2^n - 2
        res = u.mk_ule(rhs, lhs);
        const unsigned sz = u.get_bv_size(lhs);
        rational bnd = rational::power_of_two(sz) - 2;
        sc = u.mk_ule(lhs, u.mk_numeral(bnd, sz));
        return true;
    }
    if (m.is_eq(rw, lhs, rhs)) {
        res = m.mk_not(u.mk_ule(lhs, rhs));
        if (mdl.is_true(res))
            return true;
        else {
            res = m.mk_not(u.mk_ule(rhs, lhs));
            SASSERT(mdl.is_true(res));
            return true;
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
    TRACE("qe", tout << "Trying to add "
          << "\n";
          for (auto a
                   : f) tout
                            << " and " << mk_pp(a, m););
    res = m.mk_app(u.get_fid(), OP_BADD, f.size(), f.c_ptr());
}

bool rewrite_ule(expr_ref var, expr *lhs, expr *rhs, model &mdl,
                 expr_ref_vector &res) {
    expr_ref nw_lhs(m), neg(m), sum(m), t2_sum(m), neg_t2_sum(m);
    expr_ref_vector nw_rhs(m), t2(m), neg_t2(m);
    // if already in normal form, return true
    // TODO check whether lhs = c * var
    if (lhs == var) {
        res.push_back(u.mk_ule(lhs, rhs));
        return true;
    }
    TRACE("qe", tout << "Trying to normalize " << mk_pp(lhs, m) << " leq "
          << mk_pp(rhs, m) << " wrt var " << var << "\n";);
    if (!u.is_bv_add(rhs))
        nw_rhs.push_back(rhs);
    else {
        for (expr *arg : *to_app(rhs))
            nw_rhs.push_back(arg);
    }
    if (!u.is_bv_add(lhs)) {
        SASSERT(contains(lhs, var));
        nw_lhs = lhs;
    } else {
        bool found = false;
        for (expr *arg : *to_app(lhs)) {
            if (contains(arg, var)) {
                if (found)
                    return false;
                nw_lhs = arg;
                found = true;
                continue;
            }
            t2.push_back(arg);
            mk_neg(arg, neg);
            neg_t2.push_back(neg);
            nw_rhs.push_back(neg);
        }
    }
    mk_add(nw_rhs, sum);
    mk_add(neg_t2, neg_t2_sum);
    mk_add(t2, t2_sum);
    if (mdl.is_true(u.mk_ule(t2_sum, rhs)))
        res.push_back(u.mk_ule(t2_sum, rhs));
    else if (mdl.is_true(u.mk_ule(neg_t2_sum, lhs)))
        res.push_back(u.mk_ule(neg_t2_sum, lhs));
    else
        return false;
    res.push_back(u.mk_ule(nw_lhs, sum));
    return true;
}

bool normalize(expr_ref var, expr_ref f, model &mdl, expr_ref_vector &res) {
    expr_ref rw(f, m), sc(m);
    expr *lhs, *rhs;
    TRACE("qe",
          tout << "Trying to normalize " << f << " wrt var " << var << "\n";);
    if (m.is_not(f)) {
        if (!push_not(f, rw, sc, mdl))
            return false;
        // normalize both the expression inside f and the side condition produced
        bool n1 = normalize(var, rw, mdl, res);
        if (sc.get() != nullptr)
            n1 = n1 && normalize(var, sc, mdl, res);
        return n1;
    }
    if (!u.is_bv_ule(rw, lhs, rhs))
        return false;
    if ((!contains(lhs, var)) || contains(rhs, var))
        return false;
    if (!rewrite_ule(var, lhs, rhs, mdl, res)) {
        if (sc.get() != nullptr) {
            // normalize and add sc to res
            normalize(var, sc, mdl, res);
        }
        return true;
    }
    return false;
}

void resolve(expr_ref var, expr_ref_vector &f, model &mdl,
             expr_ref_vector &res) {
    if (f.empty())
        return;
    NOT_IMPLEMENTED_YET();
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
