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
  bool is_disjoint(app *g1, app *g2, ast_manager &m) {
    expr_ref_vector v1(m), v2(m);
    spacer::get_uninterp_consts(g1, v1);
    spacer::get_uninterp_consts(g2, v2);
    for (expr *p : v1) {
      for (expr *q : v2) {
        if (p->get_id() == q->get_id()) return false;
      }
    }
    return true;
  }
  bool is_disjoint(expr_ref_vector &group, ast_manager &m) {
    for (unsigned i = 0; i < group.size(); i++) {
      for (unsigned j = i + 1; j < group.size(); j++) {
        SASSERT(is_app(group.get(i)));
        SASSERT(is_app(group.get(j)));
        if (!is_disjoint(to_app(group.get(i)), to_app(group.get(j)), m))
          return false;
      }
    }
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
  SASSERT(uc.size() == 1);
  should_grp::proc proc(m, uc.get(0));
  try {
    for_each_expr(proc, pattern);
  } catch (const should_grp::found &) { return true; }
  return false;
}

bool under_approx::is_arith(expr *e)
{
    // XXX AG: not sure it returns true for arithmetic uninterpreted constants
    expr *arg;
    if (!is_app(e)) return false;
    expr *e1, *e2;
    if (m.is_eq(e, e1, e2)) return m_arith.is_arith_expr(e1);
    return m.is_not(e, arg) ? is_arith(arg) : m_arith.is_arith_expr(e);
}

// under approximate proof obligation n using literals of dim 1
// returns nullptr if pob is not in LA
  bool under_approx::under_approximate(expr *f, model_ref &model, expr_ref_vector &under_approx_vec, expr *pattern) {
    SASSERT(is_app(f));

    expr_ref_vector u_consts(m);
    get_uninterp_consts(f, u_consts);

    expr_ref_vector conj(m), conj_la(m);
    flatten_and(f, conj);

    expr * e_not;
    for(auto *e : conj)
      {
        if(is_constant(e) || m.is_eq(e) || (m.is_not(e, e_not) && is_constant(e_not)))
          under_approx_vec.push_back(e);
        else
          conj_la.push_back(e);
      }

    // if the literals are not in LA, return nullptr
    for (auto *e : conj_la) {
      if (!is_arith(e)) return false;
    }

    // compute bounds
    if(pattern)
      grp_under_approx_cube(conj_la, pattern ,model, under_approx_vec);
    else
      {
        expr_expr_map lb, ub;
        under_approx_cube(conj_la, model, lb, ub);

        // create under approximation
        for (expr *u : u_consts) {
          if (lb.contains(u)) under_approx_vec.push_back(m_arith.mk_ge(u, lb[u]));
          if (ub.contains(u)) under_approx_vec.push_back(m_arith.mk_le(u, ub[u]));
        }

        TRACE("under_approximate",
              tout << "produced an under approximation : " << mk_and(under_approx_vec) << "\n";);
      }
    m_refs.reset();
    return ( !under_approx_vec.empty() );
}

void under_approx::grp_under_approx_cube(const expr_ref_vector &cube, expr *pattern, model_ref &model, expr_ref_vector& ua_conj)
{
  expr_ref_vector grps(m);
  expr_ref_vector sub_term(m);
  expr_ref_vector non_lit_cube(m);
  TRACE("under_approximate", tout << "grouping an arithmetic pob : ";
        tout << mk_and(cube) << " and pattern " << mk_pp(pattern, m) << " \n";);
  for (expr *lit : cube)
    {
      SASSERT(is_arith(lit));
      grp_terms(pattern, lit, grps, sub_term);
    }
  TRACE("under_approximate", tout << "groups are : "; for (expr *e : grps)
                                                        tout << mk_pp(e, m) << " ";
          tout << "\n";);

  if(!is_disjoint(grps, m))
    {
      //TODO : Handle this case
      TRACE("under_approximate", tout << "intersecting grps. unhandled case \n ";);
      return;
    }

  expr_ref conj_sub(m);
  // TODO ensure union of groups has all the variables
  expr_safe_replace s(m);
  expr_ref_vector variables(m);
  expr_expr_map sub;
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
  expr_expr_map lb, ub;
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

//segregates terms of formula into groups based on pattern
//each uninterpreted constant having a var coefficient in formula is a differnt group
//all uninterpreted constans without a var coefficient belong to the same group
//formula should be in SOP. The sub_term is appended with a recontruction of formula such that it synactically mathces the groups pushed to out
  void under_approx::grp_terms(expr* pattern, expr* formula, expr_ref_vector &out, expr_ref_vector& sub_term)
{
  expr * t, *c;
  expr_ref_vector rw_formula(m);
  if(!is_bin_op(formula, t, c, m)) return;
  SASSERT(is_sop(t));
  expr_ref_vector t_ref(m);
  if (is_constant(t) || (!m_arith.is_add(t))) { out.push_back(t); return; }
  SASSERT(is_app(t));
  for (expr *term : *to_app(t))
    {
      if ( should_grp(pattern, term) )
        {
          if(!out.contains(term))
            out.push_back(term);
          rw_formula.push_back(term);
        }
      else
          t_ref.push_back(term);
    }
  if(t_ref.size() > 0)
    {
      //This will hold since it is SOP
      SASSERT(m_arith.is_add(t));
      expr_ref sum_term(m);
      sum_term = m_arith.mk_add(t_ref.size(), t_ref.c_ptr());
      if(!out.contains(sum_term))
        out.push_back(sum_term);
      rw_formula.push_back(sum_term);
      expr* e;
      expr_ref t_sub(m);
      // recontruct the formula with the same syntax structure as the substitution
      if(m.is_not(formula,e))
        t_sub = m.mk_not(m.mk_app(to_app(e)->get_decl(),m_arith.mk_add(rw_formula.size(),rw_formula.c_ptr()), c));
      else
        t_sub = m.mk_app(to_app(formula)->get_decl(),m_arith.mk_add(rw_formula.size(),rw_formula.c_ptr()), c);
      sub_term.push_back(t_sub);
    }
}

bool under_approx::is_sop(expr *e) {
    // constants are special cases since they don't have children
    if (is_constant(e)) return true;
    if (!m_arith.is_arith_expr(e)) return false;

    // cannot have a top level operand other than plus
    if (!m_arith.is_add(e) && !is_constant(e)) {
        if (!m_arith.is_mul(e)) return false;
        // all arguments for the product should be constants.
        for (expr *term_child : *to_app(e))
            if (!is_constant(term_child)) return false;
    }
    // all terms inside have to be either a constant or a product of
    // constants
    SASSERT(is_app(e));
    for (expr *term : *to_app(e)) {
        if (m_arith.is_mul(term)) {
            // all arguments for the product should be constants.
            for (expr *term_child : *to_app(term)) {
                if (!is_constant(term_child)) return false;
            }
        } else if (!is_constant(term))
            return false;
    }
    return true;
}

bool under_approx::is_le(expr *lit, expr_ref &t, expr_ref &c) {
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

  //Expects t to be in sum of products form or -1*(sum of products) form
bool under_approx::find_coeff(expr *t, expr *v, rational &k, bool negated) {
    expr *e1 = nullptr, *e2 = nullptr;
    rational n;

    if (t == v) {
        k = rational(negated ? -1 : 1);
        return true;
    } else if (m_arith.is_add(t)) {
        bool res = false;
        for (expr *e : *to_app(t)) {
            res = find_coeff(e, v, k, negated);
            if (res) return true;
        }
    } else if (m_arith.is_mul(t, e1, e2)) {
        if (m_arith.is_numeral(e2)) std::swap(e1, e2);
        if (e2 == v) {
            bool res = m_arith.is_numeral(e1, k);
            if (res && negated) k = -1 * k;
            return res;
        } else if (m_arith.is_numeral(e1, n) && n == rational(-1)) {
            return find_coeff(e2, v, k, true /*negated*/);
        }
    }
    return false;
}

// returns whether l increases(1), decreases(-1) or doesn't change(0) with
// var
int under_approx::under_approx_var(expr *t, expr *c, expr *d) {
    rational coeff;
    // lhs is in the sum of products form (ax + by)
    VERIFY(find_coeff(t, d, coeff));
    SASSERT(coeff.is_int());

    TRACE("under_approximate_verb", tout << "coefficient of " << mk_pp(d, m)
                                         << " in term " << mk_pp(t, m) << " is "
                                         << coeff << "\n";);
    if (coeff.is_pos())
        return 1;
    else if (coeff.is_neg())
        return -1;
    else {
        SASSERT(coeff.is_zero());
        return 0;
    }
}
// computes bounds u_v on each variable v in l
// bg ==> ( &u_v ==> l)
void under_approx::under_approx_lit(model_ref &model, expr *t, expr *c,
                                    expr_ref_vector &bg, expr_expr_map &lb,
                                    expr_expr_map &ub, expr_expr_map *sub) {
    expr_ref val(m);
    SASSERT(lb.size() == 0);
    SASSERT(ub.size() == 0);

    expr_ref_vector dims(m);
    get_uninterp_consts(t, dims);

    for (expr *d : dims) {
        // compute variation of l along dim d
        int change = under_approx_var(t, c, d);
        val = (*model)(sub ? (*sub)[d] : d);
        SASSERT(m_arith.is_numeral(val));

        // save reference since the map won't do it
        m_refs.push_back(val);

        if (change > 0) {
            ub.insert(d, val.get());
            TRACE("under_approximate_verb", tout << "upper bounds for "
                                                 << mk_pp(d, m) << " is "
                                                 << mk_pp(ub[d], m) << "\n";);
        } else if (change < 0) {
            lb.insert(d, val.get());
            TRACE("under_approximate_verb", tout << "lower bounds for "
                                                 << mk_pp(d, m) << " is "
                                                 << mk_pp(lb[d], m) << "\n";);
        }
    }
}

// computes bounds on each uninterp_const in e_and. If the uninterp_const is
// a an alias for a term, the bound on the uninterp_const is a bound on the
// term.
void under_approx::under_approx_cube(const expr_ref_vector &conj,
                                     model_ref &model, expr_expr_map &lb,
                                     expr_expr_map &ub, expr_expr_map *sub) {
    SASSERT(ub.size() == 0);
    SASSERT(lb.size() == 0);
    expr_ref t(m), c(m);
    for (expr *lit : conj) {
        if (is_le(lit, t, c)) {
            TRACE("under_approximate", tout << "literal is " << mk_pp(lit, m)
                                            << "normalized as: " << mk_pp(t, m)
                                            << " <= " << mk_pp(c, m) << "\n";);

            // conj of all other literals
            expr_ref_vector bg(m);
            for (expr *t : conj) {
                if (t != lit) bg.push_back(t);
            }
            if (bg.empty()) bg.push_back(m.mk_true());

            // under approximate the literal
            expr_expr_map t_lb, t_ub;
            under_approx_lit(model, t, c, bg, t_lb, t_ub, sub);

            // update global bounds
            rational n1, n2;
            for (auto &kv : t_lb) {
                auto &data = lb.insert_if_not_there(kv.m_key, kv.m_value);
                if (m_arith.is_numeral(kv.m_value, n1) &&
                    m_arith.is_numeral(data.m_value, n2) && n2 < n1)
                    lb[kv.m_key] = kv.m_value;
            }
            for (auto &kv : t_ub) {
                auto &data = ub.insert_if_not_there(kv.m_key, kv.m_value);
                if (m_arith.is_numeral(kv.m_value, n1) &&
                    m_arith.is_numeral(data.m_value, n2) && n1 < n2)
                    ub[kv.m_key] = kv.m_value;
            }
        }
    }
}

} // namespace spacer
