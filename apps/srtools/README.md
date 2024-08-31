# srtools a swiss knife for symbolic regression models 

`srtools` offers a multitude of tools for parsing and processing symbolic models.
It offers two types of output: a **csv** file evaluating the model with different metrics,
and a **detailed report** showing the same information in a more readable style plus with 
the confidence intervals of the parameters and the 10 first predictions.

Besides that, it supports the reoptimization of the parameters of the model using L-BFGS method 
and the distribution of choice (Gaussian, Bernoulli, or Poisson).

The CSV file output will show the following fields: 

- `Index`: the index of the expression in the input file 
- `Filename`: filename storing the expressions 
- `Number_of_nodes`: number of nodes in the expression 
- `Number_of_parameters` : number of numerical parameters in the expression
- `Parameters` : values of the parameters separated by `;`
- `SSE_train_orig` : sum-of-square errors of the original expression in the training set 
- `SSE_val_orig` : sum-of-square errors of the original expression in the validation set 
- `SSE_test_orig` : sum-of-square errors of the original expression in the test set 
- `SSE_train_opt` : sum-of-square errors of the reoptimized expression in the training set 
- `SSE_val_opt` : sum-of-square errors of the reoptimized expression in the validation set 
- `SSE_test_opt` : sum-of-square errors of the reoptimized expression in the test set 
- `BIC, BIC_val` : Bayesian Information Criteria of the reoptimized expression on the training and validation set
- `Evidence, Evidence_val` : Evidence of the reoptimized expression on the training and validation set
- `MDL, MDL_Freq, MDL_Lattice, *_val` : Variations of Minimum Description Length of the reoptimized expression on the training and validation set
- `NegLogLikelihood_*` : negative log-likelihood of the chosen distribution for the training, validation, and test sets.
- `LogFunctional` : the log of the functional complexity as defined by MDL.
- `LogParameters` : log of the parameters complexity as defined by MDL. 
- `Fisher` : diagonal of the Fisher information matrix.

Example of detailed report:

```bash 
=================== EXPR 0 ==================
((212.6989526196226 * x0) / (6.413269696507164e-2 + x0))

---------General stats:---------

Number of nodes: 7
Number of params: 2
theta = [212.6989526196226,6.413269696507164e-2]

----------Performance:--------

SSE (train.): 1195.4494
SSE (val.): 0.0
SSE (test): 0.0
NegLogLiklihood (train.): 44.7294
NegLogLiklihood (val.): 0.0
NegLogLiklihood (test): 0.0

------Selection criteria:-----

BIC: 96.9136
AIC: 95.4588
MDL: 61.2252
MDL (freq.): 59.4291
Functional complexity: 11.2661
Parameter complexity: 5.2297

---------Uncertainties:----------

Correlation of parameters: 
Array D Seq (Sz (2 :. 2))
  [ [ 1.0, 0.78 ]
  , [ 0.78, 1.0 ]
  ]
Std. Err.: Array D Seq (Sz1 2)
  [ 7.1613, 8.7e-3 ]

Confidence intervals:

lower <= val <= upper
198.7435 <= 212.699 <= 227.6097
4.84e-2 <= 6.41e-2 <= 8.38e-2

Confidence intervals (predictions training):

lower <= val <= upper
43.0051 <= 50.5667 <= 59.3449
43.0051 <= 50.5667 <= 59.3449
92.819 <= 102.8107 <= 112.8937
92.819 <= 102.8107 <= 112.8937
125.5919 <= 134.3624 <= 142.7414
125.5919 <= 134.3624 <= 142.7414
157.5532 <= 164.6898 <= 171.7878
157.5532 <= 164.6898 <= 171.7878
181.4728 <= 190.834 <= 200.1936
181.4728 <= 190.834 <= 200.1936
=============================================================

```

## How to use 

```bash
srtools - a CLI tool to (re)optimize the numeric parameters of symbolic
regression expressions

Usage: srtools (-f|--from ['tir'|'hl'|'operon'|'bingo'|'gomea'|'pysr'|'sbp'|'eplex'])
               [-i|--input INPUT-FILE] [-o|--output OUTPUT-FILE]
               (-d|--dataset DATASET-FILENAME) [--test TEST] [--niter NITER] 
               [--hasheader] [--simplify] 
               [--distribution ['gaussian'|'bernoulli'|'poisson']] [--sErr Serr]
               [--restart] [--seed SEED] [--report] [--profile] [--alpha ALPHA] 
               [--ptype [Bates | ODE | Constrained]]

  Optimize the parameters of Symbolic Regression expressions.

Available options:
  -f,--from ['tir'|'hl'|'operon'|'bingo'|'gomea'|'pysr'|'sbp'|'eplex']
                           Input expression format
  -i,--input INPUT-FILE    Input file containing expressions. Empty string gets
                           expression from stdin. (default: "")
  -o,--output OUTPUT-FILE  Output file to store the stats in CSV format. Empty
                           string prints expressions to stdout. (default: "")
  -d,--dataset DATASET-FILENAME
                           Filename of the dataset used for optimizing the
                           parameters. Empty string omits stats that make use of
                           the training data. It will auto-detect and handle
                           gzipped file based on gz extension. It will also
                           auto-detect the delimiter. The filename can include
                           extra information: filename.csv:start:end:target:vars
                           where start and end corresponds to the range of rows
                           that should be used for fitting, target is the column
                           index (or name) of the target variable and cols is a
                           comma separated list of column indeces or names of
                           the variables in the same order as used by the
                           symbolic model.
  --test TEST              Filename of the test dataset. Empty string omits
                           stats that make use of the training data. It can have
                           additional information as in the training set, but
                           the validation range will be discarded. (default: "")
  --niter NITER            Number of iterations for the optimization algorithm.
                           (default: 10)
  --hasheader              Uses the first row of the csv file as header.
  --simplify               Apply basic simplification.
  --distribution ['gaussian'|'bernoulli'|'poisson']
                           Minimize negative log-likelihood following one of the
                           avaliable distributions. The default is Gaussian.
                           (default: Gaussian)
  --sErr Serr              Estimated standard error of the data. If not passed,
                           it uses the model MSE. (default: Nothing)
  --restart                If set, it samples the initial values of the
                           parameters using a Gaussian distribution N(0, 1),
                           otherwise it uses the original values of the
                           expression.
  --seed SEED              Random seed to initialize the parameters values. Used
                           only if restart is enabled. (default: -1)
  --report                 If set, reports the analysis in a user-friendly
                           format instead of csv. It will also include
                           confidence interval for the parameters and
                           predictions
  --profile                If set, it will use profile likelihood to calculate
                           the CIs.
  --alpha ALPHA            Significance level for confidence intervals.
                           (default: 5.0e-2)
  --ptype [Bates | ODE | Constrained]
                           Profile Likelihood method. Default: Constrained.
                           NOTE: Constrained method only calculates the
                           endpoint. (default: Constrained)
  -h,--help                Show this help text

```

## Instalation

To install this tool you'll need:

- `libz`
- `libnlopt`
- `libgmp`
- `ghc-9.6.6`
- `cabal` or `stack`

### Recommended step-by-step 

After installing the dependencies (e.g., `apt install libz libnlopt libgmp`), install [`ghcup`](https://www.haskell.org/ghcup/#)

For Linux, macOS, FreeBSD or WSL2:

```bash 
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

For Windows, run the following in a PowerShell:

```bash
Set-ExecutionPolicy Bypass -Scope Process -Force;[System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; try { & ([ScriptBlock]::Create((Invoke-WebRequest https://www.haskell.org/ghcup/sh/bootstrap-haskell.ps1 -UseBasicParsing))) -Interactive -DisableCurl } catch { Write-Error $_ }
```

After the installation, run `ghcup tui` and install the latest `stack` or `cabal` together with `ghc-9.6.6` (select the items and press `i`).
To install `srsimplify` simply run:

```bash 
cabal build exe:srtools
```

or 

```bash 
stack build :srtools
```
