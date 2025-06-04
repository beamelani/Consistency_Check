import sys
import os
sys.path.append(os.getcwd())

import time

from stl_consistency.parser import STLParser, normalize_bounds
from stl_consistency.node import Node
from stl_consistency.tableau import make_tableau, default_tableau_opts

from paper_benchmarks import datasets, make_and, run_with_timeout

import csv
from tabulate import tabulate

def check_dataset(dataset_name, dataset, max_depth, mode, max_quantum, timeout, iters, tableau_opts):
    # Formula
    formula = make_and(dataset)
    parser = STLParser()
    parsed_formula = parser.parse_relational_exprs(formula)
    normalized_formula = normalize_bounds(parsed_formula, max_quantum)

    start_t = time.perf_counter()
    for _ in range(iters):
        res_tableau = run_with_timeout(timeout, make_tableau, Node(*normalized_formula), max_depth, mode, False, False, False, False, False, tableau_opts)
        #res_tableau = make_tableau(Node(*normalized_formula), max_depth, mode, False, False, False, False)
        if res_tableau == 'timeout':
            elapsed_tableau = timeout
            break
    else:
        elapsed_tableau = (time.perf_counter() - start_t) / iters

    # Dizionario con i risultati
    return {
        'dataset': dataset_name,
        'time_tableau': elapsed_tableau,
        'result_tableau': res_tableau
    }

def pretty_print(datasets, results, csvfile):

    topts = list(results.keys())

    # Tabella
    results_matrix = [
        [dataset] + [r for topt in topts for r in [results[topt][dataset]['time_tableau'], results[topt][dataset]['result_tableau']]]
        for dataset in datasets
    ]

    # Intestazione della tabella
    header = ["Dataset"] + [h for topt in topts for h in [f"{topt} Time (s)", f"{topt} Result"]]

    print(tabulate(results_matrix, headers=header))

    if csvfile:
        for topt in topts:
            with open(csvfile + f'_{topt}.csv', 'w') as f:
                cw = csv.writer(f)
                cw.writerow(('dataset', 'time', 'result'))
                cw.writerows((results[topt][d]['dataset'], results[topt][d]['time_tableau'], results[topt][d]['result_tableau']) for d in datasets)

if __name__ == '__main__':
    sys.setrecursionlimit(1000000000)
    max_depth = 10000000
    mode = 'sat' # 'strong_sat'
    sampling_interval = 1 # Fraction(1,10)
    timeout = 120 # in seconds
    iterations = 1

    results = {'all': {name: check_dataset(name, data, max_depth, mode, sampling_interval, timeout, iterations, default_tableau_opts) for name, data in datasets.items()}}
    for topt in default_tableau_opts:
        results[topt] = {name: check_dataset(name, data, max_depth, mode, sampling_interval, timeout, iterations, default_tableau_opts | {topt: False}) for name, data in datasets.items()}

    pretty_print(datasets.keys(), results, 'ablation')
