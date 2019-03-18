/*++
Copyright (c) 2006 Microsoft Corporation and Arie Gurfinkel

Module Name:

    sem_matcher.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-02.
    Arie Gurfinkel

Revision History:

--*/
#include "muz/spacer/spacer_sem_matcher.h"

namespace spacer {

sem_matcher::sem_matcher(ast_manager &man) : m(man), m_arith(m), m_pinned(m) {}

bool sem_matcher::match_var (var *v, expr *e) {
    expr_offset r;
    if (m_subst->find(v, 0, r)) {
        if (!m.are_equal(r.get_expr(), e)) {
            return false;
        }
    }
    else {
        m_subst->insert(v, 0, expr_offset(e, 1));
    }
    return true;
}
bool sem_matcher::operator()(expr * e1, expr * e2, substitution & s, bool &pos) {
    reset();
    m_subst = &s;
    m_todo.push_back(expr_pair(e1, e2));

    // true on the first run through the loop
    bool top = true;
    pos = true;
    while (!m_todo.empty()) {
        expr_pair const & p = m_todo.back();

        if (is_var(p.first)) {
            if (!match_var(to_var(p.first), p.second)) {
                return false;
            }
            m_todo.pop_back();
            top = false;
            continue;
        }


        if (is_var(p.second))
            return false;
        if (!is_app(p.first))
            return false;
        if (!is_app(p.second))
            return false;

        app * n1 = to_app(p.first);
        app * n2 = to_app(p.second);

        expr *t = nullptr;

        // strip negation
        if (top && n1->get_decl() != n2->get_decl()) {
            if (m.is_not(n1, t) && !m.is_not(n2) && is_app(t) &&
                to_app(t)->get_decl() == n2->get_decl()) {
                pos = false;
                n1 = to_app(e1);
            }
            else if (!m.is_not(n1) && m.is_not(n2, t) && is_app(t) &&
                     to_app(t)->get_decl() == n1->get_decl()) {
                pos = false;
                n2 = to_app(t);
            }
        }
        top = false;

        if (n1->get_decl() != n2->get_decl()) {
            expr *e1 = nullptr, *e2 = nullptr;
            rational val1, val2;

            // x<=y == !(x>y)
            if (m_arith.is_le(n1) && m.is_not(n2, t) && m_arith.is_gt(t)) {
                n2 = to_app(t);
            }
            else if (m_arith.is_le(n2) && m.is_not(n1, t) && m_arith.is_gt(t)) {
                n1 = to_app(t);
            }
            // x>=y == !(x<y)
            if (m_arith.is_ge(n1) && m.is_not(n2, t) && m_arith.is_lt(t)) {
                n2 = to_app(t);
            }
            else if (m_arith.is_ge(n2) && m.is_not(n1, t) && m_arith.is_lt(t)) {
                n1 = to_app(t);
            }
            // x+val1 matched to val2, where x is a variable, and
            // val1, val2 are numerals
            if (m_arith.is_numeral(n2, val2) && m_arith.is_add(n1, e1, e2) &&
                m_arith.is_numeral(e2, val1) && is_var(e1)) {
                val1 = val2 - val1;

                expr_ref num1(m);
                num1 = m_arith.mk_numeral (val1, val1.is_int());
                m_pinned.push_back(num1);
                if (!match_var (to_var(e1), num1)) {
                    return false;
                }

                m_todo.pop_back();
                continue;
            }
            else {
                return false;
            }
        }

        unsigned num_args1 = n1->get_num_args();
        if (num_args1 != n2->get_num_args())
            return false;

        m_todo.pop_back();

        if (num_args1 == 0)
            continue;

        unsigned j = num_args1;
        while (j > 0) {
            --j;
            m_todo.push_back(expr_pair(n1->get_arg(j), n2->get_arg(j)));
        }
    }
    return true;
}

// int sem_matcher:: distance(expr *e, substitution &s){
//     reset();
//     int dis = 0;
//     arith_util ari_u(m);
//     expr_ref applied(m);
//     s.apply(e, applied);
//     m_todo.push_back(expr_pair(e, applied));
//     TRACE("spacer_distance_a", tout << "applied: " << mk_pp(applied, m) <<"\n";);
//     TRACE("spacer_distance_a", tout << "e: " << mk_pp(e, m) << " isApp? " << is_app(e) <<"\n";);
//     // if e starts with var singleton nothing to look further
//     if(is_var(e)){
//         TRACE("spacer_distance_a", tout << "here " <<"\n";);
//         dis = -1;
//         return dis;
//     }

//     while(!m_todo.empty()){
//         expr_pair const &p = m_todo.back();
//         m_todo.pop_back();

//         if(is_var(p.first)){
//             if(!is_app(p.second)) { dis += 1000; }
//             else {
//                 if(to_app(p.second)->get_family_id() == null_family_id){
//                     dis += 1;
//                     TRACE("spacer_distance", tout << "uninter c: " << mk_pp(p.second, m) <<"\n";);
//                 } else if(to_app(p.second)->get_family_id() == 5){
//                     TRACE("spacer_distance_a", tout << "Got here with dis= " << dis <<"\n";);
//                     if(ari_u.is_int_expr(to_app(p.second)) && to_app(p.second)->get_depth() == 1){
//                         TRACE("spacer_distance_a", tout << "YAHOO!: " << mk_pp(to_app(p.second), m) <<"\n";);
//                         dis += 1;
//                     } else {
//                         dis += 3*(to_app(p.second)->get_depth());
//                     }
//                     TRACE("spacer_distance_a", tout << "Left here with dis= " << dis <<"\n";);
//                 }
//                 else {
//                     TRACE("spacer_distance_trace", tout << "second: " << mk_pp(p.second, m) <<"\n";);
//                     TRACE("spacer_distance_trace", tout << "family_id: " << to_app(p.second)->get_family_id() <<"\n";);
//                     dis += 10*(to_app(p.second)->get_depth());
//                     TRACE("spacer_distance", tout << "second: " << mk_pp(p.second, m) <<"\n";);
//                 }
//             }
//         } else if(is_app(p.first)){
//             TRACE("spacer_distance", tout << "Got here with dis= " << dis <<"\n";);
//             if(!is_app(p.second)) { dis += 1000; }
//             else {
//                 app *n1 = to_app(p.first);
//                 app *n2 = to_app(p.second);
//                 if(n1->get_decl() != n2->get_decl()){
//                     dis += 1;
//                     TRACE("spacer_distance", tout << "app 1st and 2nd mismatched \n";);
//                 }
//                 unsigned num_args1 = n1->get_num_args();
//                 if (num_args1 != n2->get_num_args()){
//                     TRACE("spacer_distance", tout << "This should never happen \n";);
//                 }
//                 unsigned j = num_args1;
//                 while (j > 0) {
//                     --j;
//                     m_todo.push_back(expr_pair(n1->get_arg(j), n2->get_arg(j)));
//                 }

//             }
//             TRACE("spacer_distance", tout << "Left here with dis= " << dis <<"\n";);
//         } else {
//             TRACE("spacer_distance", tout << "p.first is not app nor var!\n";);
//         }

//     }
//     return dis;
// }


void sem_matcher::reset() {
    m_todo.reset();
    m_pinned.reset();
}
}
