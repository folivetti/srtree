#!/bin/zsh
stack run srtools -- -f tir -i examples/puro.expr  -d examples/puro.csv --hasheader  --alpha 0.01 --report --distribution Gaussian --niter 100 --profile --ptype $1
