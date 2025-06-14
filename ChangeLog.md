# Changelog for srtree

## 2.0.1.5

- Fix `refit` to only replace the fitness if it improves the fitness 
- Fix `paretoFront` 

## 2.0.1.4

- Added `loadTrainingOnly`, `splitData`, and `loadX` to `Data.SRTree.Datasets`
- Added `getFitness`, `getTheta`, `getSize`, `isSizeOf`, `getBestFitness` to `Algorithm.EqSat.Egraph`
- Added `parseNonTerms` to `Text.ParseSR` 
- Added module `Algorithm.EqSat.SearchSR` with support functions for SR algorithms with EqSat

## 2.0.1.3

- Fix compatibility with stackage nightly 

## 2.0.1.2

- Fix bug where the parameters were printed as `t[:,ix]` instead of `t[ix]` in `showPython`

## 2.0.1.1

- MSE loss is now the default
- Renamed `--distribution` argument to `--loss` in eggp and easter.
- Fixed bug with Gaussian distribution and fixed number of parameters.
- Fixed bug in which `--number-params 0` would create parameters.
- Fixed bug in `rEGGression` that pattern matched equivalent expressions.
- Support to `--numpy` flag that prints the output as a numpy expression (experimental, eggp only).
- Support to `--simplify` flag that simplifies the expressions before displaying (experimental, eggp only).

## 2.0.1.0

- Support to Multiview Symbolic Regression in eggp and symregg.
- Support to `--number-params` argument that limits the maximum number of parameters and allow repated parameters in an expression.

## 2.0.0.4

- Cleaned up test cases (they were deprecated), will include new ones later 

## 2.0.0.3

- Fixed compatibility with random-1.3.0 and GHC-9.12.1 
- Fixed bug in Bernoulli distribution 
- Removed `log(sqrt(x))` rule in parametric rules due to generating longer expressions 
- Fixed DL calculation without the correct number of parameters 
- Fixed memory issue when querying pattern distribution 

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
