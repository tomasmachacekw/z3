namespace spacer {
  template<typename T>
  class arith_kernel {
    //takes as input an m x n matrix and returns a k x n kernel matrix
    //where 0 <= k <= min(m, n)
    virtual void compute_arith_kernel(const T**& matrix, unsigned m, unsigned n, T**& kernel);
  };
}
