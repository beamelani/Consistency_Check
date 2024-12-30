#!/usr/bin/env python3

import argparse
import platform
import os
import subprocess
import re
import statistics
import joblib
from tabulate import tabulate
import csv

time_pattern = re.compile(r"Total elapsed time \(s\): ([0-9]+\.[0-9]+)")
mem_pattern = re.compile(r"Max memory used \(KB\): ([0-9]+)")
result_pattern = re.compile(r"((sat)|(unsat)|(unknown)|(syntax error))")
pomc_pattern = re.compile(r".*\.pomc$")

if platform.system() == 'Darwin':
    time_bin = 'gtime'
else:
    time_bin = '/usr/bin/time'

def caps_command(timeout, max_mem):
    if timeout > 0 or max_mem > 0:
        return [
            'systemd-run',
            '--quiet',
            '--user',
            '--scope',
            '-p',
            'KillSignal=SIGKILL',
            '-p',
            'MemoryMax={:d}M'.format(max_mem) if max_mem > 0 else 'MemoryMax=infinity',
            '-p',
            'MemorySwapMax=0' if max_mem > 0 else 'MemorySwapMax=infinity',
            '-p',
            'RuntimeMaxSec={:d}'.format(timeout) if timeout > 0 else 'RuntimeMaxSec=infinity'
        ]
    else:
        return []

def bench_command(fname, args):
    match args.engine:
        case 'tableau':
            prog_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'stltree.py')
            return [prog_path, '--smtlib-result', fname]
        case 'smt-quant':
            return ['bash', '-c', "'", args.translator_path, '-smtlib', f'"$(cat {fname})"', '|', args.z3_path, '-in', "'"]
    assert False

def exec_bench(fname, args):
    print('Evaluating file', fname, '...')

    command = ' '.join(
        caps_command(args.timeout, args.max_mem)
        + [
            time_bin,
            '-f',
            '"Total elapsed time (s): %e\nMax memory used (KB): %M"'
        ]
        + bench_command(fname, args)
    )

    if args.verbose >= 1:
        print(command)

    raw_res = subprocess.run(
        command,
        capture_output=True,
        shell=True
    )
    raw_stdout = raw_res.stdout.decode('utf-8')
    raw_stderr = raw_res.stderr.decode('utf-8')
    if args.verbose >= 1:
        print(raw_stdout)
    if args.verbose >= 2:
        print(raw_stderr)

    if raw_res.returncode != 0:
        if raw_res.returncode == -9:
            return (-1, -1, -2**10, 'TO', -1)
        elif raw_res.returncode == 137:
            return (-1, -1, -2**10, 'OOM', -1)
        return (-1, -1, -2**10, 'Error {:d}'.format(raw_res.returncode), -1)

    time_match = time_pattern.search(raw_stderr)
    mem_match = mem_pattern.search(raw_stderr)
    result_match = result_pattern.search(raw_stdout)
    if not result_match:
        result_match = result_pattern.search(raw_stderr)
    result = result_match[0] if result_match else 'no result!'
    return (
        float(time_match.group(1)),
        int(mem_match.group(1)),
        result
    )

def iter_bench(fname, args):
    get_column = lambda rows, i: [r[i] for r in rows]
    results = [exec_bench(fname, args) for _ in range(0, args.iters)]
    times = get_column(results, 0)
    mems = get_column(results, 1)
    res = get_column(results, 2)
    return (
        fname,
        statistics.mean(times),
        statistics.mean(mems),
        res[0],
    )

def exec_all(fnames, args):
    if args.jobs <= 1:
        return [list(iter_bench(fname, args)) for fname in fnames]
    else:
        results = joblib.Parallel(n_jobs=args.jobs)(joblib.delayed(iter_bench)(fname, args)
                                                    for fname in fnames)
        return [list(res) for res in results]

def expand_files(benchfile, base_path):
    files = []
    with open(benchfile, 'rt') as benchlist:
        for path in benchlist:
            path = path.strip()
            if base_path:
                path = os.path.join(base_path, path)
            if os.path.isfile(path):
                files.append(path)
    return files

def pretty_print(results, csvfile):
    header = ["Name", "Time (s)", "Total memory (KiB)", "Result"]

    print(tabulate(results, headers=header))

    if csvfile:
        with open(csvfile, 'w', newline='') as f:
            cw = csv.writer(f)
            cw.writerow(header)
            cw.writerows(results)


if __name__ == '__main__':
    argp = argparse.ArgumentParser()
    argp.add_argument('-i', '--iters', type=int, default=1, help='Number of executions for each benchmark')
    argp.add_argument('-j', '--jobs', type=int, default=1, help='Maximum number of benchmarks to execute in parallel')
    argp.add_argument('-t', '--timeout', type=int, default=0, help='Timeout in seconds for each benchmark. 0 = no timeout (default)')
    argp.add_argument('-M', '--max-mem', type=int, default=0, help='Maximum memory to be allocated in MiBs. 0 = no limit (default)')
    argp.add_argument('-v', '--verbose', action='count', default=0, help='Show individual benchmark results')
    argp.add_argument('--csv', type=str, default='', help='Output result in CSV format in the specified file')
    argp.add_argument('-b', '--base-path', type=str, default=None, help='Base path for benchmark files')
    argp.add_argument('benchmarks', type=str, help='File containing a list of banchmark files, one per line')
    subparsers = argp.add_subparsers(required=True, dest='engine')

    tableau_p = subparsers.add_parser('tableau', help='Use the tree-shaped tableau')
    
    smt_quant_p = subparsers.add_parser('smt-quant', help='Use the SMT encoding with quantifiers and ILP')
    smt_quant_p.add_argument('translator_path', type=str)
    smt_quant_p.add_argument('z3_path', type=str, default='z3', nargs='?')

    args = argp.parse_args()

    print('Running benchmarks...')
    results = exec_all(expand_files(args.benchmarks, args.base_path), args)
    pretty_print(results, args.csv)
