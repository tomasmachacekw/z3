pob *under_approx::under_approximate(pob &n, model_ref model) {
    expr *pob_exp = to_app(n.post());
    expr_ref_vector u_consts(m);
    get_uninterp_consts(pob_exp, u_consts);
    expr_ref_vector ua_pob(m);
    expr_ref_vector conj(m);

    SASSERT(is_app(pob_exp));
    flatten_and(pob_exp, conj);

    // if the literals are not in LA, return nullptr
    for (auto e : conj)
        if (!(is_app(e) && is_arith(to_app(e)))) return nullptr;

    // hack for testing groups.
    // if there is only one literal, split each product into term
    if (conj.size() == 1) {
        expr_ref_vector e_grp(m);
        for (expr *sub_term : *to_app(conj.get(0))) {
            if (!m_arith.is_numeral(sub_term))
                if (m_arith.is_add(sub_term))
                    for (expr *arg : *to_app(sub_term)) e_grp.push_back(arg);
        }
        group(conj, e_grp, model, ua_pob);
    }

    expr_expr_map lb, ub;

    // compute bounds
    ua_formula(conj, model, lb, ub);

    // create under approximation
    for (expr *u_const : u_consts) {
        if (lb.contains(u_const))
            ua_pob.push_back(m_arith.mk_ge(u_const, lb[u_const]));
        if (ub.contains(u_const))
            ua_pob.push_back(m_arith.mk_le(u_const, ub[u_const]));
    }

    TRACE("under_approximate", tout << "produced an arithmetic pob: "
                                    << mk_pp(mk_and(ua_pob), m) << "\n";);
    pob *new_pob = n.pt().mk_pob(&n, n.level(), n.depth(), mk_and(ua_pob),
                                 n.get_binding());
    m_refs.reset();
    return new_pob;
}
bool under_approx::is_disjoint(app *g1, app *g2) {
    expr_ref_vector v1(m), v2(m);
    get_uninterp_consts(g1, v1);
    get_uninterp_consts(g2, v2);
    for (expr *p : v1) {
        for (expr *q : v2) {
            if (p->get_id() == q->get_id()) return false;
        }
    }
    return true;
}
bool under_approx::is_disjoint(expr_ref_vector group) {
    for (unsigned i = 0; i < group.size(); i++) {
        for (unsigned j = i + 1; j < group.size(); j++) {
            SASSERT(is_app(group.get(i)));
            SASSERT(is_app(group.get(j)));
            if (!is_disjoint(to_app(group.get(i)), to_app(group.get(j))))
                return false;
        }
    }
    return true;
}

// takes as input a conjunction of literals expr, a satisfying assignment m
// and a set of disjoint groups
void under_approx::group(expr_ref_vector conj, expr_ref_vector groups,
                         model_ref model, expr_ref_vector &ua_conj) {
    TRACE("under_approx", tout << "grouping an arithmetic pob : ";
          for (auto &lit
               : conj) tout
          << mk_pp(lit, m) << " ";
          tout << "\n";);
    TRACE("under_approximate", tout << "groups are : "; for (expr *e
                                                             : groups) tout
                                                        << mk_pp(e, m) << " ";
          tout << "\n";);

    expr_ref conj_sub(m);
    SASSERT(is_sop(conj));
    SASSERT(is_disjoint(groups));
    SASSERT(can_group(conj, groups));
    // TODO ensure union of groups has all the variables
    expr_safe_replace s(m);
    expr_ref_vector variables(m);
    expr_expr_map sub;
    expr_ref_vector fresh_consts(m);
    for (expr *group : groups) {
        /* SASSERT(is_sub_expr(group,pob)); */
        expr_ref eval_ref = (*model)(&(*group));
        SASSERT(m_arith.is_numeral(eval_ref));
        fresh_consts.push_back(m.mk_fresh_const("sub_temp", m_arith.mk_int()));
        s.insert(group, fresh_consts.back());
        sub.insert(fresh_consts.back(), group);
    }
    s(mk_and(conj), conj_sub);
    TRACE("under_approximate",
          tout << "substituted pob : " << mk_pp(conj_sub, m) << "\n";);
    expr_expr_map lb, ub;
    expr_ref_vector conj_sub_vec(m), u_consts(m);
    flatten_and(conj_sub, conj_sub_vec);

    ua_formula(conj_sub_vec, model, lb, ub, &sub);

    get_uninterp_consts(conj_sub, u_consts);
    for (expr *u_const : u_consts) {
        if (lb.contains(u_const))
            ua_conj.push_back(m_arith.mk_ge(sub[u_const], lb[u_const]));
        if (ub.contains(u_const))
            ua_conj.push_back(m_arith.mk_le(sub[u_const], ub[u_const]));
    }
    fresh_consts.reset();
    TRACE("under_approximat",
          tout << "split pob : " << mk_pp(mk_and(ua_conj), m) << "\n";);
}

// get that subexpression containing only uinterpreted constants in g
/* expr* get_term(expr* e,expr_ref_vector g) */
/* { */
/*   SASSERT(is_sop(e)); */
/*   expr_ref sub_term(m); */
/*   app* lhs = to_app(getLHS(e)); */
/*   for(expr* child : *lhs) */
/*     { */
/*       if(m_arith.is_mul(child)) */
/*         { */
/*           expr* arg1 = to_app(child)->get_arg(0); */
/*           expr* arg2 = to_app(child)->get_arg(1); */
/*           if(contains(g,arg1) || contains(g,arg2)) */
/*             sub_term.push_back(child); */
/*         } */
/*       else if(is_uninterp_const(child) && contains(g,child)) */
/*         sub_term.push_back(child); */
/*     } */
/*   return m_arith.mk_add(sub_term.size(),*sub_term); */
/* } */
// checks whether arithmetic expression e is a Sum Of Products
// assumes that all the terms are on the lhs and the rhs is just a numeral
bool under_approx::is_sop(expr const *e) {
    // constants are special cases since they don't have children
    if (is_constant(e)) return true;
    if (!m_arith.is_arith_expr(e)) return false;
    expr *lhs = getLHS(e);
    // skipping the check for numeral RHS since it can be a product of
    // numerals.
    // TODO simplify RHS
    /* SASSERT(m_arith.is_numeral(getRHS(e))); */

    // cannot have a top level operand other than plus
    if (!m_arith.is_add(lhs) && !is_constant(lhs)) {
        if (!m_arith.is_mul(lhs)) return false;
        // all arguments for the product should be constants.
        for (expr *term_child : *to_app(lhs))
            if (!is_constant(term_child)) return false;
    }
    // all terms inside have to be either a constant or a product of
    // constants
    SASSERT(is_app(lhs));
    for (expr *term : *to_app(lhs)) {
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
