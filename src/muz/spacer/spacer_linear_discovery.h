/*++
Copyright (c) 2019

Module Name:
  spacer_linear_discovery.cpp

Abstract:

  Linear relation discovery via matrix operation.
  Discovered LRs are used for dimension reduction.

Author:

  Yu-Ting Jeff Chen

Revision History:

--*/

#ifndef _SPACER_LINEAR_DISCOVERY_H_
#define _SPACER_LINEAR_DISCOVERY_H_

#include "util/vector.h"
#include "util/list.h"
#include "util/lp/dense_matrix.h"
#include "ast/substitution/substitution.h"

namespace sapcer{
  class spacer_linear_discovery {
  public:
    vector<int> m_base_vector;
    unsigned m_rows;     // number of rows; corresponds to number of substitutions
    unsigned m_columns;  // number of columns; corresponds to number of values per each substitution
    dense_matrix<int, int> lhs;
    dense_matrix<int, int> rhs;
    dense_matrix<int, int> result; // result of solve_right

    spacer_linear_discovery(list<substitution> subs);
    void reset();
    void operator()();
  };
}

#endif
