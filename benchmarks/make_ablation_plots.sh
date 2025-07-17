#!/bin/bash

if [ -z "$1" ]; then
    basedir="data/ablation/mltl/20250615"
else
    basedir="$1"
    shift
fi

timeout=120
datasets=("nasa-boeing" "random" "random0")
opts=("all" "no-jump" "no-g-f" "no-formula-optimizations" "no-early-local-consistency-check" "no-memoization" "no-simple-nodes")
opt_labels="All,No Jump,No GF,No Syntactic,No Early Check,No Memoization,No Easy Ops."

while [[ $# -gt 0 ]]; do
    case "$1" in
        --timeout)
            timeout="$2"
            shift 2
            ;;
        --bench-sets)
            datasets=($2)
            shift 2
            ;;
        *)
            echo "Unknown argument: $1"
            exit 1
            ;;
    esac
done

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

    python3 plot.py "${opt_labels}" "${csv_files}" ${timeout} --log-survival -o "ablation_${dataset}" ${legendopt}
    if [ -z "${legendopt}" ]; then
        legendopt="--no-legend"
    fi
done
