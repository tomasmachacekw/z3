/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_antiunify.h

Abstract:

  Antiunification utilities

Author:

    Bernhard Gleiss
    Arie Gurfinkel

Revision History:

--*/

#pragma once

#include "ast/ast.h"
#include "ast/substitution/substitution.h"
#include "util/obj_pair_hashtable.h"
namespace spacer {
/**
\brief Anti-unifier for ground expressions
*/
class anti_unifier
{
    typedef std::pair<expr *, expr *> expr_pair;
    typedef pair_hash<obj_ptr_hash<expr>, obj_ptr_hash<expr> > expr_pair_hash;
    typedef obj_pair_map<expr, expr, expr*> cache_ty;

    ast_manager &m;
    expr_ref_vector m_pinned;

    svector<expr_pair> m_todo;
    cache_ty m_cache;
    svector<expr_pair> m_subs;

public:
    anti_unifier(ast_manager& m);

    void reset();

    /**
       \brief Computes anti-unifier of two ground expressions. Returns
       the anti-unifier and the corresponding substitutions
     */
    void operator() (expr *e1, expr *e2, expr_ref &res,
                     substitution &s1, substitution &s2);
};

/// Abstracts numbers in the given ground expression by variables
/// Returns the created pattern and the corresponding substitution.
void mk_num_pat(expr *e, expr_ref &result, app_ref_vector &subs);
}
