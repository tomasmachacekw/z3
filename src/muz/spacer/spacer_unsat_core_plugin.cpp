#include "spacer_unsat_core_plugin.h"

#include "spacer_unsat_core_learner.h"

#include "smt_farkas_util.h"
#include "bool_rewriter.h"
#include "arith_decl_plugin.h"
#include <set>
#include "solver.h"

namespace spacer
{
    
#pragma mark - unsat_core_plugin_lemma

void unsat_core_plugin_lemma::compute_partial_core(proof* step)
{
    SASSERT(m_learner.is_a_marked(step));
    SASSERT(m_learner.is_b_marked(step));
    
    for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
    {
        SASSERT(m_learner.m.is_proof(step->get_arg(i)));
        proof* premise = to_app(step->get_arg(i));
        
        if (m_learner.is_b_marked(premise) && !m_learner.is_closed(premise))
        {
            SASSERT(!m_learner.is_a_marked(premise));
            add_lowest_split_to_core(premise);
        }
    }
    m_learner.set_closed(step, true);
}

void unsat_core_plugin_lemma::add_lowest_split_to_core(proof* step) const
{
    ptr_vector<proof> todo;
    todo.push_back(step);
    
    while (!todo.empty())
    {
        proof* current = todo.back();
        todo.pop_back();
        
        // if current step hasn't been processed,
        if (!m_learner.is_closed(current))
        {
            m_learner.set_closed(current, true);
            SASSERT(!m_learner.is_a_marked(current)); // by I.H. the step must be already visited
            
            // and the current step needs to be interpolated:
            if (m_learner.is_b_marked(current))
            {
                expr* fact = m_learner.m.get_fact(current);
                // if we trust the current step and we are able to use it
                if (m_learner.only_contains_symbols_b(fact) && !m_learner.is_h_marked(current))
                {
                    // just add it to the core
                    m_learner.add_lemma_to_core(expr_ref(fact, m_learner.m));
                }
                // otherwise recurse on premises
                else
                {
                    
                    for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
                    {
                        SASSERT(m_learner.m.is_proof(step->get_arg(i)));
                        proof* premise = to_app(step->get_arg(i));
                        todo.push_back(premise);
                    }
                }
            }
        }
    }
}


#pragma mark - unsat_core_plugin_farkas_lemma
void unsat_core_plugin_farkas_lemma::compute_partial_core(proof* step)
{
    SASSERT(m_learner.is_a_marked(step));
    SASSERT(m_learner.is_b_marked(step));
    
    func_decl* d = step->get_decl();
    symbol sym;
    if(!m_learner.is_closed(step) && // if step is not already interpolated
       step->get_decl_kind() == PR_TH_LEMMA && // and step is a Farkas lemma
       d->get_num_parameters() >= 2 && // the Farkas coefficients are saved in the parameters of step
       d->get_parameter(0).is_symbol(sym) && sym == "arith" && // the first two parameters are "arith", "farkas",
       d->get_parameter(1).is_symbol(sym) && sym == "farkas" &&
       d->get_num_parameters() >= m_learner.m.get_num_parents(step) + 2) // the following parameters are the Farkas coefficients
    {
        SASSERT(m_learner.m.has_fact(step));
        
        
        ptr_vector<app> literals;
        vector<rational> coefficients;
        
        /* The farkas lemma represents a subproof starting from premise(-set)s A, BNP and BP(ure) and
         * ending in a disjunction D. We need to compute the contribution of BP, i.e. a formula, which
         * is entailed by BP and together with A and BNP entails D.
         *
         * Let Fark(F) be the farkas coefficient for F. We can use the fact that
         * (A*Fark(A) + BNP*Fark(BNP) + BP*Fark(BP) + (neg D)*Fark(D)) => false. (E1)
         * We further have that A+B => C implies (A \land B) => C. (E2)
         *
         * Alternative 1:
         * From (E1) immediately get that BP*Fark(BP) is a solution.
         *
         * Alternative 2:
         * We can rewrite (E2) to rewrite (E1) to
         * (BP*Fark(BP)) => (neg(A*Fark(A) + BNP*Fark(BNP) + (neg D)*Fark(D))) (E3)
         * and since we can derive (A*Fark(A) + BNP*Fark(BNP) + (neg D)*Fark(D)) from
         * A, BNP and D, we also know that it is inconsisent. Therefore
         * neg(A*Fark(A) + BNP*Fark(BNP) + (neg D)*Fark(D)) is a solution.
         *
         * Finally we also need the following workaround:
         * 1) Although we know from theory, that the Farkas coefficients are always nonnegative,
         * the Farkas coefficients provided by arith_core are sometimes negative (must be a bug)
         * as workaround we take the absolute value of the provided coefficients.
         */
        parameter const* params = d->get_parameters() + 2; // point to the first Farkas coefficient
        
        IF_VERBOSE(3, verbose_stream() << "Farkas input: "<< "\n";);
        for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
        {
            SASSERT(m_learner.m.is_proof(step->get_arg(i)));
            proof *prem = to_app(step->get_arg(i));
            
            rational coef;
            VERIFY(params[i].is_rational(coef));
            bool b_pure = m_learner.only_contains_symbols_b(m_learner.m.get_fact(prem)) && !m_learner.is_h_marked(prem);
            IF_VERBOSE(3, verbose_stream() << (b_pure?"B":"A") << " " << coef << " " << mk_pp(m_learner.m.get_fact(prem), m_learner.m) << "\n";);
        }
        
        
        bool needsToBeClosed = true;
        
        for(unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
        {
            SASSERT(m_learner.m.is_proof(step->get_arg(i)));
            proof * premise = to_app(step->get_arg(i));
            
            if (m_learner.is_b_marked(premise) && !m_learner.is_closed(premise))
            {
                SASSERT(!m_learner.is_a_marked(premise));
                
                if (m_learner.only_contains_symbols_b(m_learner.m.get_fact(step)) && !m_learner.is_h_marked(step))
                {
                    m_learner.set_closed(premise, true);
                    
                    if (!m_use_constant_from_a)
                    {
                        rational coefficient;
                        VERIFY(params[i].is_rational(coefficient));
                        literals.push_back(to_app(m_learner.m.get_fact(premise)));
                        coefficients.push_back(abs(coefficient));
                    }
                }
                else
                {
                    needsToBeClosed = false;
                    
                    if (m_use_constant_from_a)
                    {
                        rational coefficient;
                        VERIFY(params[i].is_rational(coefficient));
                        literals.push_back(to_app(m_learner.m.get_fact(premise)));
                        coefficients.push_back(abs(coefficient));
                    }
                }
            }
            else
            {
                if (m_use_constant_from_a)
                {
                    rational coefficient;
                    VERIFY(params[i].is_rational(coefficient));
                    literals.push_back(to_app(m_learner.m.get_fact(premise)));
                    coefficients.push_back(abs(coefficient));
                }
            }
        }
        
        if (m_use_constant_from_a)
        {
            params += m_learner.m.get_num_parents(step); // point to the first Farkas coefficient, which corresponds to a formula in the conclusion
            
            // the conclusion can either be a single formula or a disjunction of several formulas, we have to deal with both situations
            if (m_learner.m.get_num_parents(step) + 2 < d->get_num_parameters())
            {
                unsigned num_args = 1;
                expr* conclusion = m_learner.m.get_fact(step);
                expr* const* args = &conclusion;
                if (m_learner.m.is_or(conclusion))
                {
                    app* _or = to_app(conclusion);
                    num_args = _or->get_num_args();
                    args = _or->get_args();
                }
                SASSERT(m_learner.m.get_num_parents(step) + 2 + num_args == d->get_num_parameters());
                
                bool_rewriter rewriter(m_learner.m);
                for (unsigned i = 0; i < num_args; ++i)
                {
                    expr* premise = args[i];
                    
                    expr_ref negatedPremise(m_learner.m);
                    rewriter.mk_not(premise, negatedPremise);
                    SASSERT(is_app(negatedPremise));
                    literals.push_back(to_app(negatedPremise));
                    
                    rational coefficient;
                    VERIFY(params[i].is_rational(coefficient));
                    coefficients.push_back(abs(coefficient));
                }
            }
        }
        
        // only close step if there are no non-pure steps
        if (needsToBeClosed)
        {
            m_learner.set_closed(step, true);
        }
        
        // now all B-pure literals and their coefficients are collected, so compute the linear combination
        expr_ref res(m_learner.m);
        compute_linear_combination(coefficients, literals, res);
        
        m_learner.add_lemma_to_core(res);
    }
}

void unsat_core_plugin_farkas_lemma::compute_linear_combination(const vector<rational>& coefficients, const ptr_vector<app>& literals, expr_ref& res)
{
    SASSERT(literals.size() == coefficients.size());
    
    ast_manager& m = res.get_manager();
    smt::farkas_util util(m);
    if (m_use_constant_from_a)
    {
        util.set_split_literals (m_split_literals); // small optimization: if flag m_split_literals is set, then preserve diff constraints
    }
    for(unsigned i = 0; i < literals.size(); ++i)
    {
        util.add(coefficients[i], literals[i]);
    }
    res = util.get();
}
    
#pragma mark - unsat_core_plugin_farkas_optimized
    void unsat_core_plugin_farkas_lemma_optimized::compute_partial_core(proof* step)
    {
        SASSERT(m_learner.is_a_marked(step));
        SASSERT(m_learner.is_b_marked(step));
        
        func_decl* d = step->get_decl();
        symbol sym;
        if(!m_learner.is_closed(step) && // if step is not already interpolated
           step->get_decl_kind() == PR_TH_LEMMA && // and step is a Farkas lemma
           d->get_num_parameters() >= 2 && // the Farkas coefficients are saved in the parameters of step
           d->get_parameter(0).is_symbol(sym) && sym == "arith" && // the first two parameters are "arith", "farkas",
           d->get_parameter(1).is_symbol(sym) && sym == "farkas" &&
           d->get_num_parameters() >= m_learner.m.get_num_parents(step) + 2) // the following parameters are the Farkas coefficients
        {
            SASSERT(m_learner.m.has_fact(step));
            
            vector<std::pair<app*,rational> > linear_combination; // collects all summands of the linear combination
            
            parameter const* params = d->get_parameters() + 2; // point to the first Farkas coefficient
            
            IF_VERBOSE(3, verbose_stream() << "Farkas input: "<< "\n";);
            for (unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
            {
                SASSERT(m_learner.m.is_proof(step->get_arg(i)));
                proof *prem = to_app(step->get_arg(i));
                
                rational coef;
                VERIFY(params[i].is_rational(coef));
                bool b_pure = m_learner.only_contains_symbols_b(m_learner.m.get_fact(prem)) && !m_learner.is_h_marked(prem);
                IF_VERBOSE(3, verbose_stream() << (b_pure?"B":"A") << " " << coef << " " << mk_pp(m_learner.m.get_fact(prem), m_learner.m) << "\n";);
            }
    
            bool needsToBeClosed = true;
            for(unsigned i = 0; i < m_learner.m.get_num_parents(step); ++i)
            {
                SASSERT(m_learner.m.is_proof(step->get_arg(i)));
                proof * premise = to_app(step->get_arg(i));
                
                if (m_learner.is_b_marked(premise) && !m_learner.is_closed(premise))
                {
                    SASSERT(!m_learner.is_a_marked(premise));
                    
                    if (m_learner.only_contains_symbols_b(m_learner.m.get_fact(step)) && !m_learner.is_h_marked(step))
                    {
                        m_learner.set_closed(premise, true);
                        rational coefficient;
                        VERIFY(params[i].is_rational(coefficient));
                        linear_combination.push_back(std::make_pair(to_app(m_learner.m.get_fact(premise)), abs(coefficient)));
                    }
                    else
                    {
                        needsToBeClosed = false;
                    }
                }
            }
            
            // only close step if there are no non-pure steps
            if (needsToBeClosed)
            {
                m_learner.set_closed(step, true);
            }
            
            // now all B-pure literals and their coefficients are collected
            // only process them when the whole proof is traversed
            if (!linear_combination.empty())
            {
                m_linear_combinations.push_back(linear_combination);
            }
        }
    }
    
    struct farkas_optimized_less_than_pairs
    {
        inline bool operator() (const std::pair<app*,rational>& pair1, const std::pair<app*,rational>& pair2) const
        {
            return (pair1.first->get_id() < pair2.first->get_id());
        }
    };
    
    void unsat_core_plugin_farkas_lemma_optimized::finalize()
    {
        if(m_linear_combinations.empty())
        {
            return;
        }
        for (auto& linear_combination : m_linear_combinations)
        {
            SASSERT(linear_combination.size() > 0);
        }
        
        // 1. sort each linear combination
        for (auto& linear_combination : m_linear_combinations)
        {
            std::sort(linear_combination.begin(), linear_combination.end(), farkas_optimized_less_than_pairs());
            for (unsigned i=0; i < linear_combination.size() - 1; ++i)
            {
                SASSERT(linear_combination[i].first->get_id() != linear_combination[i+1].first->get_id());
            }
        }
        
        // 2. build matrix: we use the standard idea how to construct union of two ordered vectors generalized to arbitrary number of vectors
        // init matrix
        ptr_vector<app> basis_elements;
        vector<vector<rational>> matrix;
        for (unsigned i=0; i < m_linear_combinations.size(); ++i)
        {
            matrix.push_back(vector<rational>());
        }
        
        // init priority queue: the minimum element always corresponds to the id of the next unhandled basis element
        std::set<unsigned> priority_queue;
        for (const auto& linear_combination : m_linear_combinations)
        {
            SASSERT(linear_combination.size() > 0);
            if (priority_queue.find(linear_combination[0].first->get_id()) == priority_queue.end())
            {
                priority_queue.insert(linear_combination[0].first->get_id());
            }
        }
        
        // init iterators
        ptr_vector<const std::pair<app*, rational>> iterators;
        for (const auto& linear_combination : m_linear_combinations)
        {
            iterators.push_back(linear_combination.begin());
        }
        
        // traverse vectors using priority queue and iterators
        while (!priority_queue.empty())
        {
            unsigned minimum_id = *priority_queue.begin(); // id of current basis element
            priority_queue.erase(priority_queue.begin());

            bool already_added_basis_element = false;
            for (unsigned i=0; i < iterators.size(); ++i)
            {
                auto& it = iterators[i];
                if (it != m_linear_combinations[i].end() && it->first->get_id() == minimum_id) // if current linear combination contains coefficient for current basis element
                {
                    // add coefficient to matrix
                    matrix[i].push_back(it->second);
                    
                    // if not already done, save the basis element
                    if(!already_added_basis_element)
                    {
                        basis_elements.push_back(it->first);
                        already_added_basis_element = true;
                    }
                    
                    // manage iterator invariants
                    it++;
                    if (it != m_linear_combinations[i].end() && priority_queue.find(it->first->get_id()) == priority_queue.end())
                    {
                        priority_queue.insert(it->first->get_id());
                    }
                }
                else // otherwise add 0 to matrix
                {
                    matrix[i].push_back(rational(0));
                }
            }
            SASSERT(already_added_basis_element);
        }
        
        // Debugging
        for (const auto& row : matrix)
        {
            SASSERT(row.size() == basis_elements.size());
        }
        if (get_verbosity_level() >= 3)
        {
            verbose_stream() << "\nBasis:\n";
            for (const auto& basis : basis_elements)
            {
                verbose_stream() << mk_pp(basis, m) << ", ";
            }
            verbose_stream() << "\n\n";
            verbose_stream() << "Matrix before transformation:\n";
            for (const auto& row : matrix)
            {
                for (const auto& element : row)
                {
                    verbose_stream() << element << ", ";
                }
                verbose_stream() << "\n";
            }
            verbose_stream() << "\n";
        }
        
        if (get_verbosity_level() >= 1)
        {
            SASSERT(matrix.size() > 0);
            verbose_stream() << "\nMatrix size: " << matrix.size() << ", " << matrix[0].size() << "\n";
        }
        // 3. perform gaussian elimination
        
        unsigned i=0;
        unsigned j=0;
        while(i < matrix.size() && j < matrix[0].size())
        {
            // find maximal element in column with row index bigger or equal i
            rational max = matrix[i][j];
            unsigned max_index = i;

            for (unsigned k=i+1; k < matrix.size(); ++k)
            {
                if (max < matrix[k][j])
                {
                    max = matrix[k][j];
                    max_index = k;
                }
            }
            
            if (max.is_zero()) // skip this column
            {
                ++j;
            }
            else
            {
                // reorder rows if necessary
                vector<rational> tmp = matrix[i];
                matrix[i] = matrix[max_index];
                matrix[max_index] = matrix[i];
                
                // normalize row
                rational pivot = matrix[i][j];
                if (!pivot.is_one())
                {
                    for (unsigned k=0; k < matrix[i].size(); ++k)
                    {
                        matrix[i][k] = matrix[i][k] / pivot;
                    }
                }
                
                // subtract row from all other rows
                for (unsigned k=1; k < matrix.size(); ++k)
                {
                    if (k != i)
                    {
                        rational factor = matrix[k][j];
                        for (unsigned l=0; l < matrix[k].size(); ++l)
                        {
                            matrix[k][l] = matrix[k][l] - (factor * matrix[i][l]);
                        }
                    }
                }
                
                ++i;
                ++j;
                
                if (get_verbosity_level() >= 3)
                {
                    verbose_stream() << "Matrix after a step:\n";
                    for (const auto& row : matrix)
                    {
                        for (const auto& element : row)
                        {
                            verbose_stream() << element << ", ";
                        }
                        verbose_stream() << "\n";
                    }
                    verbose_stream() << "\n";
                }
            }
        }
        
        if (get_verbosity_level() >= 1)
        {
            SASSERT(matrix.size() > 0);
            verbose_stream() << "Number of nonzero rows after transformation: " << i << "\n";
        }
        
        // 4. extract linear combinations from matrix and add result to core
        for (unsigned k=0; k < i; k++)// i points to the row after the last row which is non-zero
        {
            ptr_vector<app> literals;
            vector<rational> coefficients;
            for (unsigned l=0; l < matrix[k].size(); ++l)
            {
                if (!matrix[k][l].is_zero())
                {
                    literals.push_back(basis_elements[l]);
                    coefficients.push_back(matrix[k][l]);
                }
            }
            SASSERT(literals.size() > 0);
            expr_ref linear_combination(m);
            compute_linear_combination(coefficients, literals, linear_combination);
            
            m_learner.add_lemma_to_core(linear_combination);
        }
        
    }
    
    void unsat_core_plugin_farkas_lemma_optimized::compute_linear_combination(const vector<rational>& coefficients, const ptr_vector<app>& literals, expr_ref& res)
    {
        SASSERT(literals.size() == coefficients.size());
        
        ast_manager& m = res.get_manager();
        smt::farkas_util util(m);
        for(unsigned i = 0; i < literals.size(); ++i)
        {
            util.add(coefficients[i], literals[i]);
        }
        expr_ref negated_linear_combination = util.get();
        SASSERT(m.is_not(negated_linear_combination));
        res = mk_not(m, negated_linear_combination); //TODO: rewrite the get-method to return nonnegated stuff?
    }

}
