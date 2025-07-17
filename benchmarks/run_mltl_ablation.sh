#!/bin/bash

opts=("no-jump" "no-g-f" "no-formula-optimizations" "no-early-local-consistency-check" "no-memoization" "no-simple-nodes")

if [ $# -lt 1 ]; then
    echo "Usage: $0 mltlsatdir [--timeout SECONDS] [--jobs N] [--max-mem MB] [--iters N]"
    exit 1
fi

mltlsatdir="$1"
shift

timeout=120
jobs=4
max_mem=30720
iters=5
bench_sets=("nasa-boeing" "random" "random0")
outdir=./output_ablation

while [[ $# -gt 0 ]]; do
    case "$1" in
        --timeout)
            timeout="$2"
            shift 2
            ;;
        --jobs)
            jobs="$2"
            shift 2
            ;;
        --max-mem)
            max_mem="$2"
            shift 2
            ;;
        --iters)
            iters="$2"
            shift 2
            ;;
        --bench-sets)
            bench_sets=($2)
            shift 2
            ;;
        *)
            echo "Unknown argument: $1"
            exit 1
            ;;
    esac
done

if [ ! -d "${outdir}" ]; then
    mkdir -p "${outdir}"
fi

set -x

for bset in "${bench_sets[@]}"; do
    ./run_bench.py --timeout ${timeout} --max-mem ${max_mem} --jobs ${jobs} --iters ${iters} -vv --csv "${outdir}/ablation_all_${bset}.csv" -b "${mltlsatdir}/" "${mltlsatdir}/benchmark_list/${bset}.list" tableau &> "${outdir}/ablation_all_${bset}.log"
done

for opt in "${opts[@]}"; do
    for bset in "${bench_sets[@]}"; do
        ./run_bench.py --timeout ${timeout} --max-mem ${max_mem} --jobs ${jobs} --iters ${iters} -vv --${opt} --csv "${outdir}/ablation_${opt}_${bset}.csv" -b "${mltlsatdir}/" "${mltlsatdir}/benchmark_list/${bset}.list" tableau &> "${outdir}/ablation_${opt}_${bset}.log"
    done
done
