#!/usr/bin/env python3

import argparse

from stl_consistency.parser import STLParser
from stl_consistency.smtchecker import smt_check_consistency

def read_formula(filename):
    with open(filename, 'rt') as f:
        return f.read()

def main():
    argp = argparse.ArgumentParser()
    argp.add_argument('-s', '--smt', action='store_true', help='Use SMT-based bounded satisfiability checker instead of tree-based tableau (default)')
    argp.add_argument('-v', '--verbose', action='store_true')
    argp.add_argument('formula', type=str, help='File containing formula to be checked.')
    args = argp.parse_args()

    formula = read_formula(args.formula)
    parser = STLParser()

    if args.smt:
        parsed_formula = parser.parse_formula_as_list(formula)
        smt_check_consistency(parsed_formula, args.verbose)
    else:
        pass

if __name__ == "__main__":
    main()
