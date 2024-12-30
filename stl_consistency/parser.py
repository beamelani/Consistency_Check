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
    pyparsing_common, Optional, Combine, Literal, Suppress, Word, alphas, nums, alphanums, Group,
    Forward, infix_notation, opAssoc, one_of, ParserElement
)
ParserElement.enablePackrat()

import pe
from pe.operators import Class, Star
from pe.actions import Capture, Constant, Pack

from stl_consistency.node import Node

class STLParser:
    def __init__(self):
        # Basic elements
        # identifier = pyparsing_common.identifier

        # # Expression for integer
        # non_zero_digit = "123456789"
        # zero = "0"
        # integer_number = Word(non_zero_digit, nums) | zero

        # # Expression for real
        # point = "."
        # e = Word("eE", exact=1)
        # plus_or_minus = Word("+-", exact=1)
        # real_number = Combine(Optional(plus_or_minus) + Word(nums) + Optional(point + Optional(Word(nums))) + Optional(
        #     e + Optional(plus_or_minus) + Word(nums)))

        # # Arithmetic expressions
        # arith_expr = infix_notation(identifier | real_number,
        #     [
        #         (one_of('+ -'), 2, opAssoc.LEFT)
        #     ]
        # )

        # # Define relational operators
        # relational_op = one_of("< <= > >= == !=")

        # interval = Suppress('[') + integer_number + Suppress(',') + integer_number + Suppress(']')

        # # Temporal operators
        # unary_temporal_op = one_of("G F")
        # unary_temporal_prefix = unary_temporal_op + interval

        # binary_temporal_op = one_of('U R')
        # binary_temporal_prefix = binary_temporal_op + interval

        # # Define expressions
        # # Boolean terms
        # binary_relation = Group(arith_expr + relational_op + arith_expr)
        # binary_variable = Group(identifier)

        # # Expressions with all operators
        # expr = infix_notation(binary_relation | binary_variable, [
        #     ('!' | unary_temporal_prefix, 1, opAssoc.RIGHT),
        #     (binary_temporal_prefix, 2, opAssoc.LEFT),
        #     (one_of('&& &'), 2, opAssoc.LEFT),
        #     (one_of('|| |'), 2, opAssoc.LEFT),
        #     (one_of('-> <->'), 2, opAssoc.RIGHT)
        # ])
        # self.parser = expr

        def identifier_action(name):
            name_lower = name.lower()
            if name_lower in {'true', 'false'}:
                return ['B_' + name_lower]
            return ['B_' + name]

        def bin_expr_action(*args):
            match len(args):
                case 3: # Lhs OP Rhs
                    return [args[1], args[0], args[2]]
                case 1: # pass lower level
                    return args[0]
            assert False

        def un_expr_action(*args):
            match len(args):
                case 2: # NOT Term
                    return list(args)
                case 3: # UN_TEMP_OP Interval Term
                    ret = [args[0]]
                    ret.extend(args[1])
                    ret.append(args[2])
                    return ret
                case 1: # Term
                    return args[0]
            assert False

        self.parser = pe.compile(
            r'''
            # Hierarchical syntax
            Formula     <  ImplExpr EOF
            ImplExpr    <  OrExpr IMPLIFF ImplExpr
                         / OrExpr
            OrExpr      <  AndExpr OR OrExpr
                         / AndExpr
            AndExpr     <  BinTempExpr AND AndExpr
                         / BinTempExpr
                         / UnExpr AND AndExpr
                         / UnExpr
            BinTempExpr <  UnExpr BIN_TEMP_OP Interval UnExpr
            UnExpr      <  NOT Term
                         / UN_TEMP_OP Interval UnExpr
                         / Term
            Term        <  Identifier
                         / LPAR ImplExpr RPAR
            Interval    <  '[' TBound ',' TBound ']'


            # Lexical syntax
            Identifier <- IdentStart IdentCont*
            IdentStart <- [a-zA-Z_]
            IdentCont  <- IdentStart / [0-9]

            TBound     <- ~( [0-9]* )

            IMPLIFF    <- ~( '->' ) / ~( '<->' )
            AND        <- '&&' / '&'
            OR         <- '||' / '|'
            NOT        <- '!' / '~'
            BIN_TEMP_OP <- ~( 'U' ) / ~( 'R' )
            UN_TEMP_OP <- ~( 'G' ) / ~( 'F' )
            PLUS       <- '+'
            LPAR       <- '('
            RPAR       <- ')'
            EOF        <- !.
            ''',
            ignore=Star(Class("\t\n\f\r ")),
            actions={
                'Identifier': Capture(identifier_action),
                'AND': Constant('&&'),
                'OR': Constant('||'),
                'NOT': Constant('!'),
                'Interval': Pack(list),
                'UnExpr': un_expr_action,
                'BinTempExpr': lambda lhs, op, bounds, rhs: [op, bounds[0], bounds[1], lhs, rhs],
                'OrExpr': bin_expr_action,
                'AndExpr': bin_expr_action,
                'ImplExpr': bin_expr_action,
            },
            flags=pe.OPTIMIZE
        )

    def parse_formula_as_list(self, formula):
        return self.parser.parse_string(formula, parse_all=True).as_list()

    def parse_formula_as_stl_list(self, formula):
        #flist = self.parse_formula_as_list(formula)
        #return STLParser.list_to_stl_list(flist[0])
        return self.parser.match(formula, flags=pe.STRICT|pe.MEMOIZE).value()
    
    def parse_formula_as_node(self, formula):
        fslist = self.parse_formula_as_stl_list(formula)
        #print(fslist)
        return Node(*fslist)

    def is_stl_operator(f):
        return any(map(lambda x: f == x, ['G', 'F', 'U', 'R', '!', '&&', '&', '||', '|', '->', '<->']))

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
                if op in {'U', 'R'}: # We must bring forward intervals of infix operators
                    prefix = [op] + stl_list[1:3]
                    del stl_list[1:3]
                    return prefix + stl_list
                elif op in {'&', '|'}:
                    op *= 2

                return [op] + stl_list
            elif len(formula) == 3 and isinstance(formula[1], str) and formula[1] in {'<', '<=', '>', '>=', '==', '!='}:
                return [formula[1], STLParser.arith_expr_prefix(formula[0]), STLParser.arith_expr_prefix(formula[2])]
            else:
                # Should be a proposition in this case
                assert len(formula) == 1
                prop_lower = formula[0].lower()
                if prop_lower in {'true', 'false'}:
                    return ['B_' + prop_lower]
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
