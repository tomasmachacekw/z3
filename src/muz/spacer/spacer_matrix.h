/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_matrix.h

Abstract:
    a matrix

Author:
    Bernhard Gleiss

Revision History:


--*/
#ifndef _SPACER_MATRIX_H_
#define _SPACER_MATRIX_H_

#include "util/rational.h"
#include "util/vector.h"

namespace spacer {

class spacer_matrix {
  public:
    spacer_matrix(unsigned m, unsigned n); // m rows, n columns

    unsigned num_rows() const;
    unsigned num_cols() const;

    const rational &get(unsigned i, unsigned j) const;
    void set(unsigned i, unsigned j, const rational &v);

    unsigned perform_gaussian_elimination();

    vector<rational> &get_row(unsigned i) {
        SASSERT(i < num_rows());
        return m_matrix.get(i);
    }

    const vector<rational> &get_row(unsigned i) const {
        SASSERT(i < m_num_rows);
        return m_matrix.get(i);
    }

    void add_row(vector<rational> &row);
    void reset(unsigned n_cols) {
        m_num_rows = 0;
        m_num_cols = n_cols;
        m_matrix.reset();
    }
    void print_matrix();
    void normalize();

  private:
    unsigned m_num_rows;
    unsigned m_num_cols;
    vector<vector<rational>> m_matrix;
};
} // namespace spacer
#endif
