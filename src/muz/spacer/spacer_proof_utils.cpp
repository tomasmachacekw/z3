#include "spacer_proof_utils.h"

namespace spacer
{
    
    ProofIteratorPostOrder::ProofIteratorPostOrder(proof* root, ast_manager& manager) : m(manager)
    {m_todo.push_back(root);}
    
    bool ProofIteratorPostOrder::hasNext()
    {return !m_todo.empty();}
    
    /*
     * iterative post-order depth-first search (DFS) through the proof DAG
     */
    proof* ProofIteratorPostOrder::next() {
        while (!m_todo.empty()) {
            proof* currentNode = m_todo.back();
            
            // if we haven't already visited the current unit
            if (!m_visited.is_marked(currentNode)) {
                bool existsUnvisitedParent = false;
                
                // add unprocessed premises to stack for DFS. If there is at least one unprocessed premise, don't compute the result
                // for currentProof now, but wait until those unprocessed premises are processed.
                for (unsigned i = 0; i < m.get_num_parents(currentNode); ++i) {
                    SASSERT(m.is_proof(currentNode->get_arg(i)));
                    proof* premise = to_app(currentNode->get_arg(i));
                    
                    // if we haven't visited the current premise yet
                    if(!m_visited.is_marked(premise)) {
                        // add it to the stack
                        m_todo.push_back(premise);
                        existsUnvisitedParent = true;
                    }
                }
                
                // if we already visited all parent-inferences, we can visit the inference too
                if (!existsUnvisitedParent) {
                    m_visited.mark(currentNode, true);
                    m_todo.pop_back();
                    return currentNode;
                }
            }
            else {
                m_todo.pop_back();
            }
        } 
        // we have already iterated through all inferences
        return NULL;
    }
}

