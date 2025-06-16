# Benchmarks

## STL Benchmarks

STL benchmarks are located in `paper_benchmarks.py`.

To run them you'll need the following dependencies (skip this if you installed dependencies with `pdm install -d`):
```sh
pip install tabulate wrapt-timeout-decorator
```

To run STL benchmarks comparing the tree-shaped tableau with the SMT encoding, run:
```sh
cd .. # must be in the root of the repo
./paper_benchmarks.py
```

To run the ablation analysis of tableau optimizations, run:
```sh
./stl_ablation.py
```

## MLTL Benchmarks

### Requirements

Either run `pdm install -d` or
```sh
pip install joblib tabulate plotly pandas kaleido
```

The Z3 Theorem Prover is also needed.
Download the version you need from the [releases page](https://github.com/Z3Prover/z3/releases).

The MLTL benchmarks are located in [Jianwen Li's reposirtory](https://github.com/lijwen2748/mltlsat).
Clone it somewhere with
```sh
git clone https://github.com/lijwen2748/mltlsat.git
```

To compare STLTree with the First-Order Logic (FOL) encoding by Li et al., you first need to build their tool:
```sh
cd /path/to/mltlsat/translator/src
make run
```

### Running the Comparison with the FOL Encoding

Run the following script:
```sh
cd /path/to/stltree/benchmarks
./run_mltl_benchmarks.sh /path/to/mltlsat
```

The script supports the following command-line arguments:

| Argument         | Required | Value        | Default   | Description                                                                 |
|------------------|----------|--------------|-----------|-----------------------------------------------------------------------------|
| `mltlsatdir`     | Yes      | Directory    | —         | Path to the MLTL-SAT repository (first positional argument).                |
| `--timeout`      | No       | Seconds      | 120       | Timeout for each benchmark run (in seconds).                                |
| `--jobs`         | No       | Integer      | 4         | Number of parallel jobs to run.                                             |
| `--max-mem`      | No       | MB           | 30720     | Maximum memory allowed per process (in megabytes).                          |
| `--iters`        | No       | Integer      | 5         | Number of iterations to run each benchmark.                                 |
| `--z3bin`        | No       | Path         | z3        | Path to the Z3 binary to use for SMT-based benchmarks.                      |

For instance:
```sh
./run_mltl_benchmarks.sh /path/to/mltlsat --timeout 60 --jobs 4 --max-mem 4096 --iters 2 --z3bin /usr/bin/z3
```

### Running the Ablation Analysis

Run the following script:
```sh
cd /path/to/stltree/benchmarks
./run_mltl_ablation.sh /path/to/mltlsat
```

The script supports the following command-line arguments:

| Argument         | Required | Value        | Default   | Description                                                                 |
|------------------|----------|--------------|-----------|-----------------------------------------------------------------------------|
| `mltlsatdir`     | Yes      | Directory    | —         | Path to the MLTL-SAT repository (first positional argument).                |
| `--timeout`      | No       | Seconds      | 120       | Timeout for each benchmark run (in seconds).                                |
| `--jobs`         | No       | Integer      | 4         | Number of parallel jobs to run.                                             |
| `--max-mem`      | No       | MB           | 30720     | Maximum memory allowed per process (in megabytes).                          |
| `--iters`        | No       | Integer      | 5         | Number of iterations to run each benchmark.                                 |

For instance:
```sh
./run_mltl_ablation.sh /path/to/mltlsat --timeout 60 --jobs 4 --max-mem 4096 --iters 2
```

### Plot results

To plot results of the comparison with the FOL encoding, run
```sh
./make_compare_plots.sh
```

To plot the results of the ablation analysis of the tableau, run
```sh
./make_compare_plots.sh
```

By default, these script will use previous benchmarks data contained in the `data` directory.
To run them on new data, pass as a single command-line argument the directory containing the outputs of the respective benchmark script.
