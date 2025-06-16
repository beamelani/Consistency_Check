#!/bin/bash

if [ -z "$1" ]; then
    basedir="data/ablation/mltl/20250615"
else
    basedir="$1"
fi

datasets=("nasa-boeing" "random" "random0")
opts=("all" "no-jump" "no-g-f" "no-formula-optimizations" "no-early-local-consistency-check" "no-memoization" "no-simple-nodes")
opt_labels="All,No Jump,No GF,No Syntactic,No Early Check,No Memoization,No Easy Ops."

set -x

legendopt=
for dataset in "${datasets[@]}"; do
    csv_files=""
    for opt in "${opts[@]}"; do
        if [ -z "${csv_files}" ]; then
            csv_files="${basedir}/ablation_${opt}_${dataset}.csv"
        else
            csv_files="${csv_files},${basedir}/ablation_${opt}_${dataset}.csv"
        fi
    done

    python3 plot.py "${opt_labels}" "${csv_files}" 120 --log-survival -o "ablation_${dataset}" ${legendopt}
    if [ -z "${legendopt}" ]; then
        legendopt="--no-legend"
    fi
done
