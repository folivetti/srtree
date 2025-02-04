# eggp - E-graph GP

*eggp* (**e**-**g**raph **g**enetic **p**rogramming), follows the same structure as the traditional GP. The initial population is created using ramped half-and-half respecting a maximum size and maximum depth parameter and, for a number of generations, it will choose two parents using tournament selection, apply the subtree crossover with probability $pc$ followed by the subtree mutation with probability $pm$, when the offsprings replace the current population following a dominance criteria.

The key differences of *eggp* are:

    - new solutions are inserted into the e-graph followed by one step of equality saturation to find and store some of the  equivalent expressions of the new offspring.
    - the current population is replaced by the set of individuals formed by: the Pareto front, the next front after excluding the first Pareto-front, and a selection of the last offspring at random until it reaches the desired population size.
    - the subtree crossover and mutation are modified to try to generate an unvisited exp
    
## How to use 

```bash
eggp - E-graph Genetic Programming for Symbolic Regression.

Usage: eggp (-d|--dataset INPUT-FILE) [-t|--test ARG] [-g|--generations GENS]
            (-s|--maxSize ARG) [-k|--split ARG] [--print-pareto] [--trace] 
            [--loss ARG] [--opt-iter ARG] [--opt-retries ARG] 
            [--number-params ARG] [--nPop ARG] [--tournament-size ARG] 
            [--pc ARG] [--pm ARG] [--non-terminals ARG] [--dump-to ARG] 
            [--load-from ARG] [--moo]

  An implementation of GP with modified crossover and mutation operators
  designed to exploit equality saturation and e-graphs.
  https://arxiv.org/abs/2501.17848

Available options:
  -d,--dataset INPUT-FILE  CSV dataset.
  -t,--test ARG            test data (default: "")
  -g,--generations GENS    Number of generations. (default: 100)
  -s,--maxSize ARG         max-size.
  -k,--split ARG           k-split ratio training-validation (default: 1)
  --print-pareto           print Pareto front instead of best found expression
  --trace                  print all evaluated expressions.
  --loss ARG               loss function: MSE, Gaussian, Poisson, Bernoulli.
                           (default: MSE)
  --opt-iter ARG           number of iterations in parameter optimization.
                           (default: 30)
  --opt-retries ARG        number of retries of parameter fitting. (default: 1)
  --number-params ARG      maximum number of parameters in the model. If this
                           argument is absent, the number is bounded by the
                           maximum size of the expression and there will be no
                           repeated parameter. (default: -1)
  --nPop ARG               population size (Default: 100). (default: 100)
  --tournament-size ARG    tournament size. (default: 2)
  --pc ARG                 probability of crossover. (default: 1.0)
  --pm ARG                 probability of mutation. (default: 0.3)
  --non-terminals ARG      set of non-terminals to use in the search.
                           (default: "Add,Sub,Mul,Div,PowerAbs,Recip")
  --dump-to ARG            dump final e-graph to a file. (default: "")
  --load-from ARG          load initial e-graph from a file. (default: "")
  --moo                    replace the current population with the pareto front
                           instead of replacing it with the generated children.
  -h,--help                Show this help text
```

The dataset file must contain a header with each features name, and the `--dataset` and `--test` arguments can be accompanied by arguments separated by ':' following the format:

`filename.ext:start_row:end_row:target:features`

where each ':' field is optional. The fields are:

- **start_row:end_row** is the range of the training rows (default 0:nrows-1).
   every other row not included in this range will be used as validation
- **target** is either the name of the  (if the datafile has headers) or the index
   of the target variable
- **features** is a comma separated list of names or indices to be used as
  input variables of the regression model.

Example of valid names: `dataset.csv`, `mydata.tsv`, `dataset.csv:20:100`, `dataset.tsv:20:100:price:m2,rooms,neighborhood`, `dataset.csv:::5:0,1,2`.

The format of the file will be determined by the extension (e.g., csv, tsv,...). To use multi-view, simply pass multiple filenames in double-quotes:

```bash
eggp --dataset "dataset1.csv dataset2.csv dataset3.csv" ...
```

## Installation

To install eggp you'll need:

- `libz`
- `libnlopt`
- `libgmp`
- `ghc-9.6.6`
- `cabal` or `stack`

### Method 1: Pre-compile binaries

Go to the [releases](https://github.com/folivetti/srtree/tags) page, download the eggp binary corresponding to your OS and rename it to `eggp`.

Note: Windows and OSX releases are untested, for Windows Mingw with libnlopt are required.

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
cabal build srtree:eggp 
```

or 

```bash 
stack build srtree:eggp
```

## Citing this work

If you use eggp for your research, please cite:

```
@misc{defranca2025improvinggeneticprogrammingsymbolic,
      title={Improving Genetic Programming for Symbolic Regression with Equality Graphs}, 
      author={Fabricio Olivetti de Franca and Gabriel Kronberger},
      year={2025},
      eprint={2501.17848},
      archivePrefix={arXiv},
      primaryClass={cs.LG},
      url={https://arxiv.org/abs/2501.17848}, 
}
```
