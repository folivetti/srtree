# srtree: A supporting library for tree-based symbolic regression 

`srtree` is a Haskell library that implements a tree-based structure for expressions and supporting functions to be used in the context of **symbolic regression**.

The expression structure is defined as a fixed-point of a mix of unary and binary tree. This makes it easier to implement supporting functions that requires the traversal of the trees. Also, since it is a parameterized structure, we can creating partial trees to pattern math structures of interest.
This structure may contain four types of nodes:

- `Bin Op l r` that represents a binary operator `Op` with two children.
- `Uni Function t` that represents an unary function `Function` with a single child.
- `Var Int` representing the index of a variable (i.e., x0, x1, etc.).
- `Param Int` representing the index of a adjustable parameter (i.e., theta0, theta1, etc.).
- `Const Double`  representing a constant value.


The `SRTree` structure has instances for `Num, Fractional, Floating, IsString` which allows to create an expression as a valid Haskell expression such as (remember to turn on OverloadedStrings extension):

```haskell
expr = "x0" * 2 + sin("x1" * pi + "x0") :: Fix SRTree
```

This library comes with support to many quality of life functions to handle this data structure. Such as:

- getting the arity of a node
- getting the children of a node as a list
- count the number of nodes 
- number of nodes of a specific type
- counting unique tokens 
- number of variables and parameters 
- relabeling the parameters from 0 to p 
- converting floating point constants to parameters 

Additionally, the library provides supporting function to work with datasets, evaluating the expressions, 
calculating the derivatives, printing, generating random trees, simplifying the expression, calculating overall statistics,
optimizing parameters, and model selection metrics. 

Together with this library, we provide example applications (please refer to their corresponding README files):

- [srsimplify](apps/srsimplify/README.md): a parser and simplification tool supporting the output of many popular SR algorithms.
- [srtools](apps/srtools/README.md): a tool that can be used to evaluate symbolic regression expressions and create nice reports with confidence intervals. 
- [tinygp](apps/tinygp/README.md): a simple GP implementation based on tinyGP.

## Organization

The library is organized as `Data`, `Algorithm`, and `Text` modules where the `Data` modules implement functions directly tied to the data structure and the `Algorithm` modules implement algorithms related to symbolic regression, finally, the `Text` modules parse string expressions from different formats and apply simplification, when requested.

### `Data` modules

The `Data` modules is split into $5$ submodules:

- `Data.SRTree` contains the data strucuture and basic supporting functions.
- `Data.SRTree.Datasets` contains functions supporting loading datasets into Massiv.Arrays (aka numpy arrays).
- `Data.SRTree.Derivative` contains the symbolic derivatives of the functions and operators.
- `Data.SRTree.Eval` contains functions to evaluate the tree given a dataset and parameters.
- `Data.SRTree.Print` contains supporting functions for converting trees to different string representation.
- `Data.SRTree.Random`  contains functions to generate random trees.

#### `Data.SRTree`

The `SRTree val` data structure is a sum type structure that can be either a variable index, a parameter index, a constant value (of type `Double`), an univariate function or a binary operator. The data type is implemented as a fixed point so all the algorithms act on `Fix SRTree`:

```haskell 
t = "x0" + "t0" * sin("x1" + "t1"**2) :: Fix SRTree 
```

When creating the expression in a more natural notation, the variables and parameters are `String` composed of the first letter either `x`, for variables, or `t` for parameters (as in theta), and an integer corresponding to the index of the variable or parameter. The fixed point notation, allows us to implment recursive processing of a tree without many of the common boilerplate:

```haskell
countNodes = 
  \case 
    Var _     = 1
    Const _   = 1
    Param _   = 1
    Uni _ t   = 1 + t 
    Bin _ l r = 1 + l + r
```

The children are parameterized by the `val` type parameter. This allows us to create convenient partial structures, such as:

```haskell
-- + operator pointing to some structure
-- with index 1 and 2
Bin Add 1 2 

-- canonical representation of + operator 
Bin Add () ()
```

The main functions of this module are:

- `arity`: returns the arity of an operator.
- `getChildren`: returns the children of a `Fix SRTree` as a list 
- `countNodes`: returns the number of nodes 
- `countOccurrences`: counts the occurence of a given variable 
- `countVars`: returns the number of unique variables appearing the expression 
- `relabelParams`: relabels the parameters from the left leaves to the right 
- `constsToParams`: replace `Const` nodes with `Param` nodes.

#### `Data.SRTree.Datasets` module 

This module exports only the `loadDataset` function which takes a filename and 
returns the training and test sets together with the column labels.
The filename must follow the format:

`filename.ext:start_row:end_row:target:features`

where each ':' field is optional. The fields are:

- **start_row:end_row** is the range of the training rows (default 0:nrows-1).
   every other row not included in this range will be used as validation
- **target** is either the name of the PVector (if the datafile has headers) or the index
   of the target variable
- **features** is a comma separated list of SRMatrix names or indices to be used as
  input variables of the regression model.

Example of valid names: `dataset.csv`, `mydata.tsv`, `dataset.csv:20:100`, `dataset.tsv:20:100:price:m2,rooms,neighborhood`, `dataset.csv:::5:0,1,2`.

#### `Data.SRTree.Derivative` module 

Calculates symbolic derivatives of the expression w.r.t. the variables or the parameters.
The main functions of this module are:

- `deriveBy`: returns the symbolic derivative w.r.t. a certain variable or a certain parameter.
- `deriveByVar`: shortcut to `deriveBy` to derive by a variable.
- `deriveByParam`: shortcut to `deriveBy` to derive by a parameter.

#### `Data.SRTree.Eval` module 

Evaluates an expression given a dataset.
The main functions of this module are:

- `evalTree`: given a data matrix and a vector of parameters, evaluates the expression tree.
- `evalInverse`: evaluates the inverse of a function. 
- `invright`: evaluates the right inverse of an operator.
- `invleft`: evaluates the left inverse of an operator.

#### `Data.SRTree.Print` module 

Support functions to convert an expression tree into a `String`.
The main functions of this module are: 

- `showExpr` and `printExpr`: converts/print the expression into math notation .
- `showPython` and `printPython`: converts/print to a numpy notation.
- `showLatex` and `printLatex`: converts/print to a LaTeX notation.
- `showTikz` and `printTikz`: converts/print to a TikZ notation.

#### `Data.SRTree.Random` module 

Auxiliary functions to create random trees. 
The main functions of this module are:

- `randomTree`: creates a random tree with a certain number of nodes.
- `randomTreeBalanced`: creates a (almost) balanced random tree with a certain number of nodes.

### `Text` modules 

The `Text` module is split into $2$ modules:

- `Text.ParseSR`: contains the main parsers for different SR algorithms output.
- `Text.ParseSR.IO`: auxiliary functions to handle files containing many expressions.

#### `Text.ParseSR` module 

The only important function of this module is `parseSR` that  parses an string expression from a given algorithm to a certain output. It also converts variable names to x0, x1,...

#### `Text.ParseSR.IO` module 

The two main functions of this module are: 

- `withInput`: that reads the stdin or a text file and parse all expressions 
- `withOutput`: that writes the parsed expression into stdout or a file with one of the choices of output format. 

These functions handle any errors with an `Either` type and they can be safely pipelined together. Any invalid expression will be printed as "invalid expression <error message>".

### `Algorithm` modules 

The `Algorithm` modules are split into $5$ submodules:

- `Algorithm.SRTree.AD` contains automatic differentiation functions.
- `Algorithm.SRTree.ConfidenceIntervals` contains functions to calculate the confidence intervals of parameters and predictions of a symbolic expression using Laplace approximation or profile likelihood.
- `Algorithm.SRTree.Likelihood` contains functions support different likelihood functions and their derivatives (gradient and hessian).
- `Algorithm.SRTree.ModelSelection` implements different model selection criteria such as AIC, BIC, MDL.
- `Algorithm.SRTree.Opt` implements functions to optimize the parameters of an expression supporting different likelihood functions.

#### `Algorithm.SRTree.AD` module 

The main functions of this module are:

- `forwardMode`: returns the prediction errors vector multiplied by the Jacobian matrix using forward mode AD.
- `forwardModeUnique`: same as above, but assuming each parameter index appear only once in the tree. 
- `reverseModeUnique`: same as above, but using reverse mode 
- `forwardModeUniqueJac`: same as `forwardModeUnique` but returns the Jacobian (does not mutiply by the error).

#### `Algorithm.SRTree.Likelihood` module 

The main functions of this module are: 

- `sse, mse, rmse`: calculates the sum-of-square, mean squared, root of mean squared errors.
- `nll`: returns the negative log-likelihood given a distribution and the associated error (`Nothing` if unknown)
- `gradNLL`: returns the gradient of the negative log-likelihood. 
- `gradNLLNonUnique`: same as above but assumes non-unique parameters 
- `hessianNLL`: returns the hessian of the neg log-likelihood.

#### `Algorithm.SRTree.Opt` module 

The main functions of this module are:

- `minimizeNLL`: minimizes the negative log-likelihood of a distribution.
- `minimizeNLLNonUnique`: same as above but assumes repeated occurrences of parameters.
- `minimizeNLLWithFixedParam`: minimizes the neg log-likelihood but fixing the value of a single parameter.
- `minimizeGaussian`, `minimizePoisson`, `minimizeBinomial`: shortcut to minimize these three distributions.

#### `Algorithm.SRTree.ModelSelection` module 

The main functions of this module are:

- `bic`: Bayesian Information Criteria 
- `aic`: Akaike Information Criteria 
- `mdl`: Minimum Description Length as described in Bartlett, Deaglan J., Harry Desmond, and Pedro G. Ferreira. "Exhaustive symbolic regression." IEEE Transactions on Evolutionary Computation (2023)
- `mdlLattice`: as described in Bartlett, Deaglan, Harry Desmond, and Pedro Ferreira. "Priors for symbolic regression." Proceedings of the Companion Conference on Genetic and Evolutionary Computation. 2023.
- `mdlFreq` : MDL weighted by the frequency of occurrence of functions 

#### `Algorithm.SRTree.ConfidenceIntervals` module 

The main functions of this module are: 

- `paramCI`: calculates the parameters confidence intervals. 
- `predictionCI`: calculates the predictions confidence intervals 

### `EqSat` modules 

The `EqSat` modules are split into $4$ submodules:

- `Algorithm.EqSat.Simplify` contains function supporting algebraic simplification with equality saturation.
- `Algorithm.EqSat` contains the main equality saturation function.
- `Algorithm.EqSat.EGraph` contains the e-graph data structure and supporting functions.
- `Algorithm.EqSat.EqSatDB` contains supporting functions to pattern matching and insert equivalent expressions into an e-graph. 

#### `Algorithm.EqSat` module

The main functions of this module are: 

- `eqSat` : runs equality saturation over a single expression. 
- `getBest` : returns the best expression given the cost function used to generate the e-graph 
- `recalculateBest` : recalculates the cost of each e-class using a new cost function 
- `runEqSat` : runs equality saturation inside `EGraphST` monad. Use this if you want to return the e-graph. 

#### `Algorithm.EqSat.EGraph` module

The main functions of this module are: 

- `fromTree` : creates an e-graph from an expression tree.
- `fromTrees` : creates an e-graph from multiple expressions 
- `fromTreeWith` : inserts a new expression into the e-graph 
- `findRootClasses` : returns the roots of the e-graph, if any .
- `getExpressionFrom` : returns a single expression from a given e-class always picking the first e-node as the path 
- `getAllExpressionsFrom` : returns all expressions from the given e-class 
- `getRndExpressionFrom` : returns a random expression from this e-class 


#### `Algorithm.EqSat.EqSatDB` module

The main functions of this module are: 

- TODO: create auxiliary functions to apply substution rules inside an EGraphST monad . 

#### `Algorithm.EqSat.Simplify` module

The main functions of this module are: 

- `simplifyEqSatDefault` : simplifies an expression using the default parameters 
- `simplifyEqSat` : simplifies with custom parameters

## TODO:

- support more advanced functions
- support conditional branching (`IF-THEN-ELSE`)
- document egraph-search and ieeexplore
