# Description of the test cases in each file


## Files with number 0X have special cases for formulas of a certain shape
`file_name` : description
- `psms_01.smt2`: A and B are cubes
- `psms_02.smt2`: A is a cube, B is not a cube
   These testcases should not trigger the lookahead mode
- `psms_03.smt2`: A is not a cube, B is a cube
   These testcases should not trigger the lookahead mode, A would propagate,
   and then "propagation" in B would create a full assignment to the variables in B.
- `psms_04.smt2`: A or B are horn clauses + literals


## Files with number 1X have arbitrary formulas
Each of them triggers different steps of the transition

- `psms_10.smt2`: A or B are arbitrary formulas
