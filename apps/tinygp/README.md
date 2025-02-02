# tinyGP - a simple example of tinyGP using SRTree

A very basic implementation of a simple GP using SRTree based on https://github.com/moshesipper/tiny_gp .

tinyGP is a minimalistic GP algorithm for symbolic regression implementing subtree crossover, subtree mutation,
and tournament selection.
This implementation supports parameter optimization, and multi-view symbolic regression (https://arxiv.org/abs/2402.04298).

## How to use 

```bash
tinyGP - a very simple example of GP using SRTRee.

Usage: tinygp (-d|--dataset INPUT-FILE) [--test INPUT-FILE] 
              [-p|--population POP-SIZE] [-g|--generations GENS] 
              [--max-size SIZE] [--probCx PC] [--probMut PM] 
              [--non-terminals ARG] [--tournament-size ARG] [--distribution ARG]

  Very simple example of GP using SRTree.

Available options:
  -d,--dataset INPUT-FILE  CSV dataset.
  --test INPUT-FILE        CSV dataset.
  -p,--population POP-SIZE Population size. (default: 100)
  -g,--generations GENS    Number of generations. (default: 100)
  --max-size SIZE          maximum expression size. (default: 20)
  --probCx PC              Crossover probability. (default: 0.9)
  --probMut PM             Mutation probability. (default: 0.3)
  --non-terminals ARG      set of non-terminals to use in the search.
                           (default: "Add,Sub,Mul,Div,PowerAbs,Recip")
  --tournament-size ARG    tournament size. (default: 2)
  --distribution ARG       distribution of the data. (default: MSE)
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
tinygp --dataset "dataset1.csv dataset2.csv dataset3.csv" ...
```

## Installation

To install tinyGP you'll need:

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
cabal build srtree:tinygp 
```

or 

```bash 
stack build srtree:tinygp 
```
