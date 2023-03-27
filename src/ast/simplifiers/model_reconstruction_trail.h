/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    model_reconstruction_trail.h

Abstract:

   Model reconstruction trail
   A model reconstruction trail comprises of a sequence of assignments 
   together with assertions that were removed in favor of the assignments. 
   The assignments satisfy the removed assertions but are not (necessarily) 
   equivalent to the removed assertions. For the case where assignments 
   are equivalent to removed assertions, we squash the removed assertions 
   and don't track them.

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-3.
    
--*/

#pragma once

#include "util/scoped_ptr_vector.h"
#include "util/trail.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/simplifiers/dependent_expr.h"
#include "ast/converters/model_converter.h"
#include "ast/converters/generic_model_converter.h"

class dependent_expr_state;

class model_reconstruction_trail {

    struct entry {
        scoped_ptr<expr_substitution> m_subst;
        vector<dependent_expr>        m_removed;
        func_decl_ref                 m_decl;
        expr_ref                      m_def;
        expr_dependency_ref           m_dep;
        bool                          m_active = true;

        entry(ast_manager& m, expr_substitution* s, vector<dependent_expr> const& rem) :
            m_subst(s), m_removed(rem), m_decl(m), m_def(m), m_dep(m) {}

        entry(ast_manager& m, func_decl* h) : m_decl(h, m), m_def(m), m_dep(m) {}

        entry(ast_manager& m, func_decl* f, expr* def, expr_dependency* dep, vector<dependent_expr> const& rem) :
            m_removed(rem), m_decl(f, m), m_def(def, m), m_dep(dep, m) {}

        bool is_loose() const { return !m_removed.empty(); }

        bool intersects(ast_mark const& free_vars) const {
            if (is_hide())
                return false;
            if (is_def())
                return free_vars.is_marked(m_decl);
            for (auto const& [k, v] : m_subst->sub())
                if (free_vars.is_marked(k))
                    return true;
            return false;
        }

        bool is_hide() const { return m_decl && !m_def; }
        bool is_def() const { return m_decl && m_def; }
        bool is_subst() const { return !m_decl; }
    };

    ast_manager&             m;
    trail_stack&             m_trail_stack;
    scoped_ptr_vector<entry> m_trail;
    unsigned                 m_trail_index = 0;

    void add_vars(dependent_expr const& d, ast_mark& free_vars) {
        for (expr* t : subterms::all(expr_ref(d.fml(), d.get_manager())))
            free_vars.mark(t, true);
    }

    bool intersects(ast_mark const& free_vars, dependent_expr const& d) {
        expr_ref term(d.fml(), d.get_manager());
        auto iter = subterms::all(term);
        return any_of(iter, [&](expr* t) { return free_vars.is_marked(t); });
    }

    bool intersects(ast_mark const& free_vars, vector<dependent_expr> const& added) {
        return any_of(added, [&](dependent_expr const& d) { return intersects(free_vars, d); });
    }

    /**
    * Append new updates to model converter, update the current index into the trail in the process.
    */
    void append(generic_model_converter& mc, unsigned& index);
public:

    model_reconstruction_trail(ast_manager& m, trail_stack& tr): 
        m(m), m_trail_stack(tr) {}

    /**
    * add a new substitution to the trail
    */
    void push(expr_substitution* s, vector<dependent_expr> const& removed) {
        m_trail.push_back(alloc(entry, m, s, removed));
        m_trail_stack.push(push_back_vector(m_trail));       
    }

    /**
    * add declaration to hide
    */
    void hide(func_decl* f) {
        m_trail.push_back(alloc(entry, m, f));
        m_trail_stack.push(push_back_vector(m_trail));
    }

    /**
     * add definition
     */
    void push(func_decl* f, expr* def, expr_dependency* dep, vector<dependent_expr> const& removed) {
        m_trail.push_back(alloc(entry, m, f, def, dep, removed));
        m_trail_stack.push(push_back_vector(m_trail));
    }

    /**
    * register a new depedent expression, update the trail 
    * by removing substitutions that are not equivalence preserving.
    */
    void replay(unsigned qhead, dependent_expr_state& fmls);
    
    /**
    * retrieve the current model converter corresponding to chaining substitutions from the trail.
    */
    model_converter_ref get_model_converter();


    /**
    * Append new updates to model converter, update m_trail_index in the process.
    */
    void append(generic_model_converter& mc);

    std::ostream& display(std::ostream& out) const;
};

