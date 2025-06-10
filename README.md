# stl-consistency

This is a bounded satisfiability checker for temporal logic formulas (discrete-time STL), supporting both tableau-based and SMT-based solving.

## 📦 Features

- Parses temporal logic formulas from file
- Supports both **tableau-based** and **SMT-based** solving
- Optional trace output and `.dot` graph generation
- Flexible control over solver optimizations
- SMTLIB-compatible output option

## 🚀 How to Run

### ✅ Requirements and Dependencies to Install

- Python 3.11+

- matplotlib>=3.9.1

- networkx>=3.3

- pe>=0.5.0

- pydot>=3.0

- z3-solver>=4.13.0.0

- wrapt-timeout-decorator>=1.5.1

through: pip install -r requirements.txt

### Command line options:

| Option                              | Description                                                                                     |
|-------------------------------------|-------------------------------------------------------------------------------------------------|
| `-s`, `--smt`                       | Use SMT-based satisfiability checker instead of the tableau-based method.                      |
| `-d`, `--max-depth <int>`           | Maximum depth for tableau construction (ignored if `--smt` is used). Default: `10000000`.      |
| `-p`, `--plot <file>`               | Output tableau as a `.dot` file for visualization (ignored if `--smt` is used).                |
| `--print-trace`                     | Print an example trace that satisfies the formula.                                              |
| `-t`, `--strong-sat`                | Use strong satisfiability semantics (avoids vacuous truth).                                     |
| `--smtlib-result`                   | Output result in SMTLIB format: `sat`, `unsat`, or `unknown`.                                   |
| `--parallel`                        | Enable parallel tableau construction.                                                           |
| `--mltl`                            | Use MLTL semantics for `U` and `R` operators (not supported with SMT solver).                   |
| `--no-jump`                         | Disable the jump rule in the tableau.                                                           |
| `--no-formula-optimizations`        | Disable formula-level optimizations.                                                            |
| `--no-children-order-optimizations` | Disable child-node ordering optimizations.                                                      |
| `--no-early-local-consistency-check`| Only check local consistency for poised nodes.                                                  |
| `--no-memoization`                  | Disable memoization for tableau nodes.                                                          |
| `--no-simple-nodes`                 | Disable simple-node optimization.                                                               |
| `--no-g-f`                          | Disable special handling for `G` (Globally) and `F` (Eventually) operators.                     |
| `-v`, `--verbose`                   | Enable verbose output for debugging or analysis.                                                |
| `formula <file>`                    | Path to a file containing the temporal logic formula to be checked.                             |

Benchmarks from paper can be found in
benchmarks/paper_benchmarks.py

### 🏁 Running the Checker

python main.py [options] <formula-file>