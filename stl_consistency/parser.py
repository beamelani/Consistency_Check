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
 
from pyparsing import (
    Optional, Combine, Literal, Suppress, Word, alphas, nums, alphanums, Group,
    Forward, infix_notation, opAssoc, one_of
    )
from stl_consistency.node import Node

class STLParser:
    def __init__(self):
        # Basic elements
        identifier = Word(alphas, alphanums + "_")

        # Expression for integer
        non_zero_digit = "123456789"
        zero = "0"
        integer_number = Word(non_zero_digit, nums) | zero

        # Expression for real
        point = "."
        e = Word("eE", exact=1)
        plus_or_minus = Word("+-", exact=1)
        real_number = Combine(Optional(plus_or_minus) + Word(nums) + Optional(point + Optional(Word(nums))) + Optional(
            e + Optional(plus_or_minus) + Word(nums)))

        # Arithmetic expressions
        arith_expr = infix_notation(identifier | real_number,
            [
                (one_of('+ -'), 2, opAssoc.LEFT)
            ]
        )

        # Define relational operators
        relational_op = one_of("< <= > >= == !=")

        interval = Suppress('[') + integer_number + Suppress(',') + integer_number + Suppress(']')

        # Temporal operators
        unary_temporal_op = one_of("G F")
        unary_temporal_prefix = unary_temporal_op + interval

        binary_temporal_op = Literal('U')
        binary_temporal_prefix = binary_temporal_op + interval

        # Define expressions
        expr = Forward()

        # Building the expressions
        binary_relation = Group(arith_expr + relational_op + arith_expr)
        binary_variable = Group(identifier)

        # Expression with all options
        expr <<= infix_notation(binary_relation | binary_variable, [
            (unary_temporal_prefix, 1, opAssoc.RIGHT),
            ('!', 1, opAssoc.RIGHT),
            (binary_temporal_prefix, 2, opAssoc.LEFT),
            ('&&', 2, opAssoc.LEFT),
            ('||', 2, opAssoc.LEFT),
            (one_of('-> <->'), 2, opAssoc.RIGHT)
        ])
        self.parser = expr

    def parse_formula_as_list(self, formula):
        return self.parser.parse_string(formula, parse_all=True).as_list()

    def parse_formula_as_stl_list(self, formula):
        flist = self.parse_formula_as_list(formula)
        return STLParser.list_to_stl_list(flist[0])
    
    def parse_formula_as_node(self, formula):
        fslist = self.parse_formula_as_stl_list(formula)
        return Node(*fslist)

    def is_stl_operator(f):
        return any(map(lambda x: f == x, ['G', 'F', 'U', '!', '&&', '||', '->', '<->']))

    def arith_expr_prefix(expr):
        if isinstance(expr, list):
            if len(expr) == 1:
                return STLParser.arith_expr_prefix(expr[0])
            assert len(expr) >= 3 and isinstance(expr[-2], str) and expr[1] in {'+', '-'}
            return [expr[-2], STLParser.arith_expr_prefix(expr[0:-2]), STLParser.arith_expr_prefix(expr[-1])]
        assert isinstance(expr, str)
        return expr

    def list_to_stl_list(formula):
        if isinstance(formula, list):
            op = next(filter(STLParser.is_stl_operator, formula), None)
            if op is not None:
                # We assume all operators in a list are the same
                stl_list = [STLParser.list_to_stl_list(el) for el in formula if not STLParser.is_stl_operator(el)]
                if op == 'U': # We must bring forward intervals of infix operators
                    prefix = [op] + stl_list[1:3]
                    del stl_list[1:3]
                    return prefix + stl_list
                return [op] + stl_list
            elif len(formula) == 3 and isinstance(formula[1], str) and formula[1] in {'<', '<=', '>', '>=', '==', '!='}:
                return [formula[1], STLParser.arith_expr_prefix(formula[0]), STLParser.arith_expr_prefix(formula[2])]
            else:
                # Should be a proposition in this case
                assert len(formula) == 1
                return ['B_' + formula[0]]
        else:
            assert isinstance(formula, str) and formula.isdigit()
            return formula

    def is_float(string):
        first = string[0]
        return first.isdigit() or first in {'+', '-'}

    def parse_relational_exprs(self, formula):
        '''
        Complete parsing of partially-parsed formulas in which relational constraints are unparsed strings
        '''
        assert isinstance(formula, list)
        if len(formula) == 1 and formula[0][0:2] == 'R_':
            return self.parse_formula_as_stl_list(formula[0])
        return [
            self.parse_relational_exprs(el) if isinstance(el, list) else el
            for el in formula
        ] 
