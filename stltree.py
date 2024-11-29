#!/usr/bin/env python3

import argparse

from stl_consistency.parser import STLParser
from stl_consistency.smtchecker import smt_check_consistency
from stl_consistency.tableau import make_tableau, plot_tree

def read_formula(filename):
    with open(filename, 'rt') as f:
        return f.read()

def main():
    argp = argparse.ArgumentParser()
    argp.add_argument('-s', '--smt', action='store_true', help='Use SMT-based bounded satisfiability checker instead of tree-based tableau (default)')
    argp.add_argument('-p', '--plot', type=int, default=0, help='Plot the tree-shaped tableau up to the given depth.')
    argp.add_argument('-v', '--verbose', action='store_true')
    argp.add_argument('formula', type=str, help='File containing formula to be checked.')
    args = argp.parse_args()

    formula = read_formula(args.formula)
    parser = STLParser()

    if args.smt:
        parsed_formula = parser.parse_formula_as_list(formula)
        smt_check_consistency(parsed_formula, args.verbose)
    elif args.plot > 0:
        parsed_formula = parser.parse_formula_as_node(formula)
        tableau = make_tableau(parsed_formula, args.plot)
        plot_tree(tableau)
    else:
        print('Tableau SAT mode not implemented yet.')

if __name__ == "__main__":
    main()
