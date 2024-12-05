#!/usr/bin/env python3

# MIT License
#
# Copyright (c) 2024 Ezio Bartocci, Michele Chiari, Beatrice Melani
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import argparse

from stl_consistency.parser import STLParser
from stl_consistency.smtchecker import smt_check_consistency
from stl_consistency.tableau import make_tableau, plot_tree

def read_formula(filename):
    with open(filename, 'rt') as f:
        return f.read()

MAX_HORIZON = 255

def main():
    argp = argparse.ArgumentParser()
    argp.add_argument('-s', '--smt', action='store_true', help='Use SMT-based bounded satisfiability checker instead of tree-based tableau (default)')
    argp.add_argument('-p', '--plot', type=int, default=0, help='Plot the tree-shaped tableau up to the given depth.')
    argp.add_argument('-t', '--strong-sat', action='store_true', help='Use strong definition of satisfiability that avoids formulas being satisfied vacuously (default is normal satisfiability)')
    argp.add_argument('-v', '--verbose', action='store_true')
    argp.add_argument('formula', type=str, help='File containing formula to be checked.')
    args = argp.parse_args()

    formula = read_formula(args.formula)
    parser = STLParser()

    if args.smt:
        if args.strong_sat:
            print('Strong sat mode not implemented yet for SMT. Falling back to sat.')

        parsed_formula = parser.parse_formula_as_list(formula)
        smt_check_consistency(parsed_formula, args.verbose)
    elif args.plot > 0:
        parsed_formula = parser.parse_formula_as_node(formula)
        tableau, _ = make_tableau(parsed_formula, args.plot)
        plot_tree(tableau)
    else:
        parsed_formula = parser.parse_formula_as_node(formula)
        tableau, res = make_tableau(parsed_formula, MAX_HORIZON, mode=('strong_sat' if args.strong_sat else 'sat'))
        if res:
            print('The constraints are consistent.')
        else:
            print(f'The constraints are not consistent (for signals up to t = {MAX_HORIZON}).')

if __name__ == "__main__":
    main()
