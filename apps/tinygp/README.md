# tinyGP - a simple example of tinyGP using SRTree [WORK IN PROGRESS]

A very basic implementation of a simple GP using SRTree. 
It will use the first columns as the input variables and the last column as the target. 
The operator set is fixed to the basic math operators, power, and inverse (1/x).
It generates random trees with a minimum and maximum depth of [2, 4] and maximum size of 20.
It selects parents using tournament selection with $2$ contenders.

The program will output the entire population of every generation.

## How to use 

```bash
tinyGP - a very simple example of GP using SRTRee.

Usage: tinygp (-d|--dataset INPUT-FILE) [-p|--population POP-SIZE] 
              [-g|--generations GENS] [--probCx PC] [--probMut PM]

  Very simple example of GP using SRTree.

Available options:
  -d,--dataset INPUT-FILE  CSV dataset.
  -p,--population POP-SIZE Population size. (default: 100)
  -g,--generations GENS    Number of generations. (default: 100)
  --probCx PC              Crossover probability. (default: 0.9)
  --probMut PM             Mutation probability. (default: 0.3)
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
cabal build exe:tinygp 
```

or 

```bash 
stack build :tinygp 
```
