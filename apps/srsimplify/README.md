# srsimplify - a CLI tool to simplify symbolic regression expressions with equality saturation.                                                           

## How to use 

```bash
Usage: srsimplify (-f|--from ['tir'|'hl'|'operon'|'bingo'|'gomea'|'pysr'|'sbp'|'eplex'])
                  (-t|--to ['python'|'math'|'tikz'|'latex']) 
                  [-i|--input INPUT-FILE] [-o|--output OUTPUT-FILE] 
                  [-v|--varnames VARNAMES]

  Simplify an expression using equality saturation.

Available options:
  -f,--from ['tir'|'hl'|'operon'|'bingo'|'gomea'|'pysr'|'sbp'|'eplex']
                           Input expression format
  -t,--to ['python'|'math'|'tikz'|'latex']
                           Output expression format
  -i,--input INPUT-FILE    Input file containing expressions. Empty string gets
                           expression from stdin. (default: "")
  -o,--output OUTPUT-FILE  Output file to store the stats in CSV format. Empty
                           string prints expressions to stdout. (default: "")
  -v,--varnames VARNAMES   Comma separated string of variable names. Empty
                           string defaults to the algorithm default (x0, x1,..).
                           (default: "")
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
cabal build exe:srsimplify 
```

or 

```bash 
stack build :srsimplify 
```
