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
 
import pe
from pe.operators import Class, Star
from pe.actions import Capture, Constant, Pack

from stl_consistency.node import Node

class STLParser:
    def __init__(self):
        def impl_expr_action(*args):
            match len(args):
                case 3: # Lhs OP Rhs
                    if args[1] == '<->':
                        return ['||', ['&&', args[0], args[2]], ['&&', ['!', args[0]], ['!', args[2]]]]
                    assert args[1] == '->'
                    return [args[1], args[0], args[2]]
                case 1: # pass lower level
                    return args[0]
            assert False

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

        def term_action(*args):
            match len(args):
                case 3: # RExpr REL RExpr
                    return [args[1], args[0], args[2]]
                case 1: # pass lower level
                    if isinstance(args[0], str): # Identifier
                        name = args[0]
                        name_lower = name.lower()
                        if name_lower in {'true', 'false'}:
                            return ['B_' + name_lower]
                        return ['B_' + name]
                    assert isinstance(args[0], list) # LPAR ImplExpr RPAR
                    return args[0]
            assert False

        def rexpr_action(*expr):
            if len(expr) == 1:
                return expr[0]
            assert len(expr) >= 3 and isinstance(expr[-2], str) and expr[1] in {'+', '-'}
            return [expr[-2], rexpr_action(*expr[0:-2]), expr[-1]]

        def rterm_action(*rterm):
            if len(rterm) == 1:
                return rterm[0]
            assert len(rterm) == 3 and rterm[0] == rterm[2] == '|'
            return ['abs', rterm[1]]


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
            Term        <  RExpr REL RExpr
                         / Identifier
                         / LPAR ImplExpr RPAR
            RExpr       <  RTerm (PM RTerm)*
            RTerm       <  Identifier
                         / REAL
                         / LPAR RExpr RPAR
                         / ABSPAR RExpr ABSPAR
            Interval    <  '[' TBound ',' TBound ']'

            # Lexical syntax
            Identifier <- ~( IdentStart IdentCont* )
            IdentStart <- [a-zA-Z_]
            IdentCont  <- IdentStart / [0-9]

            TBound     <- ~( DIGITS )

            DIGITS      <- [0-9]+
            INTEGER     <- "-"? DIGITS
            REAL        <- ~( INTEGER FRACTION? EXPONENT? )
            FRACTION    <- "." DIGITS
            EXPONENT    <- [Ee] [-+]? DIGITS

            IMPLIFF    <- ~( '->' ) / ~( '<->' )
            AND        <- '&&' / '&'
            OR         <- '||' / '|'
            NOT        <- '!' / '~'
            BIN_TEMP_OP <- ~( 'U' ) / ~( 'R' )
            UN_TEMP_OP <- ~( 'G' ) / ~( 'F' )
            PM         <- ~( '+' ) / ~( '-' )
            REL        <- ~('<=') / ~('<') / ~('>=') / ~('>') / ~('==') / ~('!=')
            LPAR       <- '('
            RPAR       <- ')'
            ABSPAR     <- ~( '|' )
            EOF        <- !.
            ''',
            ignore=Star(Class("\t\n\f\r ")),
            actions={
                'ImplExpr': impl_expr_action,
                'AndExpr': bin_expr_action,
                'OrExpr': bin_expr_action,
                'BinTempExpr': lambda lhs, op, bounds, rhs: [op, bounds[0], bounds[1], lhs, rhs],
                'UnExpr': un_expr_action,
                'Term': term_action,
                'RExpr': rexpr_action,
                'RTerm': rterm_action,
                'Interval': Pack(list),
                'NOT': Constant('!'),
                'OR': Constant('||'),
                'AND': Constant('&&'),
            },
            flags=pe.OPTIMIZE
        )

    def parse_formula_as_stl_list(self, formula):
        return self.parser.match(formula, flags=pe.STRICT|pe.MEMOIZE).value()
    
    def parse_formula_as_node(self, formula):
        fslist = self.parse_formula_as_stl_list(formula)
        node = Node(*fslist)
        node.flatten()
        return node

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
