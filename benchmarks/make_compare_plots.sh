#!/bin/bash

if [ -z "$1" ]; then
    basedir="data/latest"
else
    basedir="$1"
fi

timeout=120

tools="FOL (Z3 4.13.4),Tableau"
datasets=("nasa-boeing" "random" "random0")

set -x

for dataset in "${datasets[@]}"; do
    files="${basedir}/smt-quant_z3_${dataset}.csv,${basedir}/tableau_${dataset}.csv"
    python3 plot.py "${tools}" "${files}" ${timeout} --markers-survival --scatter -o "comp_${dataset}"
done
