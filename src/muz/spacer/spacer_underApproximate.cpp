#include "spacer_underApproximate.h"
namespace {
  //checks whether f is a binary operator or the negation of one
  bool is_bin_op(expr * f, expr * &lhs, expr * &rhs, ast_manager &m)
  {
    if (!is_app(f)) return false;
    expr * e;
    if (m.is_not(f,e))
      return is_bin_op(e, lhs, rhs, m);
    app * f_app = to_app(f);
    if (f_app->get_num_args() != 2) return false;
    lhs = f_app->get_arg(0);
    rhs = f_app->get_arg(1);
    return true;
  }
} // anonymous namespace

namespace should_grp {
  struct found {};
  struct proc {
    arith_util m_arith;
    expr* m_uc;
    proc(ast_manager &m, expr * uc) : m_arith(m), m_uc(uc){}
    void operator()(var *n) const {}
    void operator()(quantifier *q) const {}
    void operator()(app const *n) const {
      expr *e1, *e2;
      if (m_arith.is_mul(n, e1, e2) && ((is_var(e1) && e2 == m_uc) ||
                                        (is_var(e2) && e1 == m_uc)))
        throw found();
    }
  };
} // namespace should_grp

namespace spacer {

  // Checks whether the uninterp_const in term has a var coeff in pattern
  bool under_approx::should_grp(expr *pattern, expr *term) {
  expr_ref_vector uc(m);
  get_uninterp_consts(term, uc);
  TRACE("under_approximate_verb", tout << "should group " << mk_pp(term, m)
                                       << " according to pattern "
                                       << mk_pp(pattern, m) << "\n";);
  SASSERT(uc.size() == 1);
  should_grp::proc proc(m, uc.get(0));
  try {
    for_each_expr(proc, pattern);
  } catch (const should_grp::found &) { return true; }
  return false;
}

// under approximate proof obligation n using literals of dim 1
// returns false if pob is not an arithmetic fml
  bool under_approx::under_approximate(expr_ref f, model_ref &model, expr_ref_vector &under_approx_vec, expr_ref pattern) {
    SASSERT(is_app(f));

    expr_ref_vector u_consts(m);
    get_uninterp_consts(f, u_consts);

    expr_ref_vector conj(m), conj_la(m);
    flatten_and(f, conj);

    for(auto *e : conj) {
        //separate out boolean u_c
        if(not_handled(e))
            under_approx_vec.push_back(e);
        else
            conj_la.push_back(e);
    }

    expr* e_not;
    // if the literals are not in arithmetic, return false
    for (auto e : conj_la) {
        TRACE("under_approximate_verb", tout << "Literal is " << mk_pp(e, m););
        if (! (m_arith.is_arith_expr(e) || (m.is_not(e, e_not) && m_arith.is_arith_expr(e_not)) )) return false;
    }

    SASSERT(pattern.get() != nullptr);

    grp_under_approx_cube(conj_la, pattern ,model, under_approx_vec);

    TRACE("under_approximate",
          tout << "produced an under approximation : " << mk_and(under_approx_vec) << "\n";);
    SASSERT(!under_approx_vec.empty());
    return true;
}

void under_approx::grp_under_approx_cube(const expr_ref_vector &cube, expr_ref pattern, model_ref &model, expr_ref_vector& ua_conj) {
  expr_ref_vector grps(m);
  expr_ref_vector sub_term(m);
  expr_ref_vector non_lit_cube(m);
  TRACE("under_approximate", tout << "grouping an arithmetic pob : ";
        tout << mk_and(cube) << " and pattern " << mk_pp(pattern, m) << " \n";);
  for (auto lit : cube) {
      grp_terms(pattern, expr_ref(lit, m), grps, sub_term);
  }
  TRACE("under_approximate", tout << "groups are : "; for (expr *e : grps)
                                                        tout << mk_pp(e, m) << " ";
          tout << "\n";);

  expr_ref conj_sub(m);
  // TODO ensure union of groups has all the variables
  expr_safe_replace s(m);
  expr_ref_vector variables(m);
  expr_expr_map sub(m);
  expr_ref_vector fresh_consts(m);
  for (expr *grp : grps) {
    expr_ref eval_ref = (*model)(&(*grp));
    SASSERT(m_arith.is_numeral(eval_ref));
    fresh_consts.push_back(m.mk_fresh_const("sub_temp", m_arith.mk_int()));
    s.insert(grp, fresh_consts.back());
    sub.insert(fresh_consts.back(), grp);
  }
  expr_ref c = mk_and(sub_term);
  s(c , conj_sub);
  TRACE("under_approximate",
        tout << "substituted formula : " << mk_pp(conj_sub, m) << "\n";);
  expr_expr_map lb(m), ub(m);
  expr_ref_vector conj_sub_vec(m), u_consts(m);
  flatten_and(conj_sub, conj_sub_vec);

  under_approx_cube(conj_sub_vec, model, lb, ub, &sub);

  get_uninterp_consts(conj_sub, u_consts);
  for (expr *u_const : u_consts) {
    if (lb.contains(u_const))
      ua_conj.push_back(m_arith.mk_ge(sub[u_const], lb[u_const]));
    if (ub.contains(u_const))
      ua_conj.push_back(m_arith.mk_le(sub[u_const], ub[u_const]));
  }
  fresh_consts.reset();
  TRACE("under_approximate",
        tout << "split pob : " << mk_pp(mk_and(ua_conj), m) << "\n";);

}

// If there are n non linear multiplications in pattern, there are n + 1 axis.
void under_approx::grp_terms(expr_ref pattern, expr_ref formula, expr_ref_vector &out, expr_ref_vector& sub_term) {
  expr * t, *c;
  expr_ref_vector rw_formula(m);
  if(!is_bin_op(formula, t, c, m)) return;
  expr_ref_vector other_trms(m);
  //If the literal cannot be split, just make it a whole group
  if (is_constant(t) || m_arith.is_mul(t)) {
    sub_term.push_back(formula);
    out.push_back(t);
    return;
  }
  SASSERT(is_app(t));
  TRACE("under_approximate_verb", tout << "computing groups in " << formula << "\n";);
  for (auto term : *to_app(t)) {
      if(should_grp(pattern, term)) {
          if(!out.contains(term)) {
              TRACE("under_approximate_verb", tout << "adding " << mk_pp(term , m) << " to groups\n";);
              out.push_back(term);
          }
          rw_formula.push_back(term);
      }
      else
          other_trms.push_back(term);
  }
  if (other_trms.size() > 0) {
      expr_ref sum_term(m);
      sum_term = m_arith.mk_add(other_trms.size(), other_trms.c_ptr());
      if(!out.contains(sum_term)) {
          TRACE("under_approximate_verb", tout << "adding " << sum_term << " to groups\n";);
          out.push_back(sum_term);
      }
      rw_formula.push_back(sum_term);
  }
  expr* e;
  expr_ref t_sub(m);
  // recontruct the formula with the same syntax structure as the substitution
  if(m.is_not(formula,e))
      t_sub = m.mk_not(m.mk_app(to_app(e)->get_decl(),m_arith.mk_add(rw_formula.size(),rw_formula.c_ptr()), c));
  else
      t_sub = m.mk_app(to_app(formula)->get_decl(),m_arith.mk_add(rw_formula.size(),rw_formula.c_ptr()), c);
  TRACE("under_approximate_verb", tout << "re-wrote " << formula << " into " << t_sub << " for substitution\n";);
  sub_term.push_back(t_sub);
}

bool under_approx::is_sop(expr *e) {
    if (is_constant(e)) return true;
    if (!m_arith.is_arith_expr(e)) return false;

    expr *e1, *e2;
    // cannot have a top level operand other than plus
    if (!m_arith.is_add(e) && !is_constant(e)) {
        // all arguments for the product should be constants.
        if (!(m_arith.is_mul(e, e1, e2) && is_constant(e1) && is_constant(e2))) return false;
    }
    // all terms inside have to be either a constant or a product of
    // constants
    for (expr *term : *to_app(e)) {
        // all arguments for the product should be constants.
        if (!( (m_arith.is_mul(term, e1, e2) && is_constant(e1) && is_constant(e2)) || is_constant(term) ))
            return false;
    }
    return true;
}

bool under_approx::normalize_to_le(expr *lit, expr_ref &t, expr_ref &c) {
    expr *e0 = nullptr, *e1 = nullptr, *e2 = nullptr;
    rational n;
    bool is_int = true;
    if (m_arith.is_le(lit, e1, e2) ||
        (m.is_not(lit, e0) && m_arith.is_gt(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n)) {
            t = e1;
            c = e2;
            return true;
        } else {
            // XXX handle if needed
            UNREACHABLE();
            return false;
        }
    } else if (m_arith.is_lt(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_ge(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n, is_int)) {
            // x < k  ==> x <= (k-1)
            t = e1;
            c = m_arith.mk_numeral(n - 1, is_int);
            return true;
        } else {
            UNREACHABLE();
            return false;
        }
    } else if (m_arith.is_gt(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_le(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n, is_int)) {
            // x > k ==> -x < -k ==> -x <= -k - 1
            expr_ref minus_one(m);
            minus_one = m_arith.mk_numeral(rational(-1), is_int);
            t = m_arith.mk_mul(minus_one, e1);
            c = m_arith.mk_numeral(-n - 1, is_int);
            return true;
        } else {
            UNREACHABLE();
            return false;
        }
    } else if (m_arith.is_ge(lit, e1, e2) ||
               (m.is_not(lit, e0) && m_arith.is_lt(e0, e1, e2))) {
        if (m_arith.is_numeral(e2, n, is_int)) {
            // x >= k ==> -x <= -k
            expr_ref minus_one(m);
            minus_one = m_arith.mk_numeral(rational(-1), is_int);
            t = m_arith.mk_mul(minus_one, e1);
            c = m_arith.mk_numeral(-n, is_int);
            return true;
        } else {
            UNREACHABLE();
            return false;
        }
    }

    return false;
}

void under_approx::find_coeff(expr_ref t, expr_ref v, rational &k) {
    if (t == v) {
        k = rational::one();
        return ;
    }

    expr *e1 = nullptr, *e2 = nullptr;
    rational coeff;
    if (m_arith.is_add(t)) {
        for (expr *e : *to_app(t)) {
            if(e == v) {
                k = rational::one();
                return;
            }
            else if (m_arith.is_mul(e, e1, e2) && e2 == v) {
                bool is_num = m_arith.is_numeral(e1, coeff);
                SASSERT(is_num);
                k = coeff;
                return;
            }
        }
        k = rational::zero();
        return;
    }

    if (m_arith.is_mul(t, e1, e2)) {
            m_arith.is_numeral(e1, coeff);
            SASSERT(coeff == rational::minus_one());
            //Depth of recursion is atmost 1
            SASSERT(m_arith.is_add(e2) || is_uninterp_const(e2));
            find_coeff(expr_ref(e2, m), v, k);
            k = k * rational::minus_one();
            return;
    }
    UNREACHABLE();
}

int under_approx::change_with_var(expr_ref l, expr_ref var) {
    rational coeff;
    // lhs is in the sum of products form (ax + by)
    find_coeff(l, var, coeff);

    TRACE("under_approximate_verb", tout << "coefficient of " << mk_pp(var, m)
                                         << " in term " << mk_pp(l, m) << " is "
                                         << coeff << "\n";);
    if (coeff.is_pos())
        return 1;
    else if (coeff.is_neg())
        return -1;
    else
       return 0;
}

// TODO  use bg if we need better bounds. In this
// case, should update background as bounds are discovered!!!!
void under_approx::under_approx_lit(model_ref &model, expr_ref lit, expr_expr_map &lb,
                                    expr_expr_map &ub, expr_expr_map *sub) {
    expr_ref val(m);

    expr_ref_vector dims(m);
    get_uninterp_consts(lit, dims);

    for (expr *var : dims) {
        // compute variation of l along dim d
        int change = change_with_var(lit, expr_ref(var, m));
        SASSERT(!sub || sub->contains(var));
        CTRACE("under_approximate_verb", sub, tout << "computing value of " << mk_pp(var, m) << "\n";);
        val = (*model)(sub ? (*sub)[var] : var);
        CTRACE("under_approximate_verb", sub,
              tout << " value of " << mk_pp(var, m) << " is "
                   << val << "\n";);

        SASSERT(m_arith.is_numeral(val));

        // update bounds
        rational bnd, nw_bnd;
        m_arith.is_numeral(val, nw_bnd);
        if (change > 0) {
            auto &data = ub.insert_if_not_there(var, val.get());
            m_arith.is_numeral(data.m_value, bnd);
            if (nw_bnd < bnd)
                ub[var] = val;
            TRACE("under_approximate_verb", tout << "upper bounds for "
                                                 << mk_pp(var, m) << " is "
                                                 << mk_pp(ub[var], m) << "\n";);
        }

        if (change < 0) {
            auto &data = lb.insert_if_not_there(var, val.get());
            m_arith.is_numeral(data.m_value, bnd);
            if (nw_bnd > bnd) lb[var] = val;
            TRACE("under_approximate_verb", tout << "lower bounds for "
                                                 << mk_pp(var, m) << " is "
                                                 << mk_pp(lb[var], m) << "\n";);
        }
    }
}

void under_approx::under_approx_cube(const expr_ref_vector &conj,
                                     model_ref &model, expr_expr_map &lb,
                                     expr_expr_map &ub, expr_expr_map *sub) {
    SASSERT(ub.size() == 0);
    SASSERT(lb.size() == 0);
    expr_ref t(m), c(m);
    for (expr *lit : conj) {
        if (normalize_to_le(lit, t, c)) {
            TRACE("under_approximate", tout << "literal is " << mk_pp(lit, m)
                                            << "normalized as: " << mk_pp(t, m)
                                            << " <= " << mk_pp(c, m) << "\n";);

            under_approx_lit(model, t, lb, ub, sub);
        }
    }
}

} // namespace spacer
