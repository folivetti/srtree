# Changelog for srtree

## 2.0.0.0 

- Complete refactoring of the library
- Integration of other tools such as: srtree-opt, srtree-tools, srsimplify
- Implementation of Equality Saturation and support to e-graph 
- Using Massiv for performance 
- Using NLOpt as the optimization library 

## 1.1.0.0

- Reorganization of modules
- Renaming AD functions
- Inclusion of reverse mode that calculates the diagonal of and the full Hessian matrices

## 1.0.0.5

- Changed `base` and `mtl` versions

## 1.0.0.4

- Removed benchmarking code that demanded more dependencies

## 1.0.0.3

- Fixed issue with HUnit test

## 1.0.0.2

- Export `Fix` from `Data.SRTRee`
- `paramsToConst` function

## 1.0.0.1

- Fix `vector` version bounds
- Included benchmarking of `ad` package

## 1.0.0.0

- Complete refactoring of source
- We now work with the SRTree data type fixed point
- Symbolic derivative by Param or Var
- Forward mode autodiff
- Optimized gradient calculation of parameters if each parameter occurs only once in the expression

## 0.1.3.0

- `countParams` function

## 0.1.2.1

- Better bounds for base (compatible with stackage nightly)

## 0.1.2.0

- Implemented `deriveParamBy` to calculate the derivative by the parameters indexed by `ix`

## 0.1.1.0

- Fixed compilation bug

## 0.1.0.0

- Initial version
