# rEGGression (r🥚ression) - Nonlinear regression models exploration and query system with e-graphs (egg).

*r🥚ression* an interactive tool that can help SR users to explore alternative models generated from different sources. These sources can be: the final population of a single run, the Pareto front, the entire history of visited expressions during the search, or a combination of those sources from multiple runs of the same or different algorithms. This can provide a rich library of alternative expressions generated from different biases, induced by different hyper-parameters or algorithms, that can bring invaluable information about the data.
This tool supports simple queries such as querying for the top-N models filtered by size, complexity, and number of numerical parameters; insert and evaluate new expressions; list and evaluate sub-expressions of the already visited expressions, and also, more advanced queries such as calculate the frequency of common patterns (i.e., building blocks) observed in the set of models; and filter the expressions by patterns with a natural syntax.


## How to use 

```bash
r🥚ression - Nonlinear regression models exploration and query system with
e-graphs (egg).

Usage: reggression (-d|--dataset INPUT-FILE) [-t|--test ARG] 
                   [--distribution ARG] [--dump-to ARG] [--load-from ARG] 
                   [--parse-csv ARG] [--convert ARG] [--parse-parameters] 
                   [--to ARG] [--calculate-dl]

  Exploration and query system for a database of regression models using
  e-graphs.

Available options:
  -d,--dataset INPUT-FILE  CSV dataset.
  -t,--test ARG            test data (default: "")
  --distribution ARG       distribution of the data. (default: Gaussian)
  --dump-to ARG            dump final e-graph to a file. (default: "")
  --load-from ARG          load initial e-graph from a file. (default: "")
  --parse-csv ARG          parse-csv CSV file with the format
                           expression,parameters,fitness. The fitness value
                           should be maximization and the parameters a ;
                           separated list (there must be an additional parameter
                           for sigma in the Gaussian distribution). The format
                           of the equation is determined by the extension of the
                           file, supported extensions are operon, pysr, tir,
                           itea, hl (heuristiclab), gomea, feat, etc.
                           (default: "")
  --convert ARG            convert FROM TO, converts equation format from a
                           given format (see 'parse-csv') to either 'math' or
                           'numpy'. The 'math' format is compatible with the tir
                           format, so you can use this to standardize the
                           equations from multiple sources into a single file.
                           The output will be written to stdout. (default: "")
  --parse-parameters       Extract the numerical parameters from the expression.
                           In this case the csv file should be formatted as
                           "equation,error,fitness, where 'error' is the error
                           term used in Gaussia likelihood, it can be empty if
                           using other distributions."
  --to ARG                 Format to convert to. (default: MATH)
  --calculate-dl           (re)calculate DL.
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

The format of the file will be determined by the extension (e.g., csv, tsv,...). 

## Demo

[![asciicast](https://asciinema.org/a/713509.svg)](https://asciinema.org/a/713509)

## Installation

To install rEGGression you'll need:

- `libz`
- `libnlopt`
- `libgmp`
- `ghc-9.6.6`
- `cabal` or `stack`

### Method 1: Pre-compile binaries

Go to the [releases](https://github.com/folivetti/srtree/tags) page, download the eggp binary corresponding to your OS and rename it to `reggresion`.

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
cabal build srtree:reggression
```

or 

```bash 
stack build srtree:reggression
```

## Citing this work

If you use eggp for your research, please cite:

```
@inproceedings{rEGGression,
author = {de Franca, Fabricio Olivetti and Kronberger, Gabriel},
title = {rEGGression: an Interactive and Agnostic Tool for the Exploration of Symbolic Regression Models},
year = {2025},
isbn = {9798400714658},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
url = {https://doi.org/10.1145/3712256.3726385},
doi = {10.1145/3712256.3726385},
booktitle = {Proceedings of the Genetic and Evolutionary Computation Conference},
pages = {},
numpages = {9},
keywords = {Genetic programming, Symbolic regression, Equality saturation, e-graphs},
location = {Malaga, Spain},
series = {GECCO '25},
archivePrefix = {arXiv},
       eprint = {2501.17859},
 primaryClass = {cs.LG},
}
```
