from pyparsing import (
    Optional, Combine, Literal, Word, alphas, nums, alphanums, Group, Forward, infixNotation,
    opAssoc, oneOf
    )
from node import Node

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

        # Define relational operators
        relational_op = oneOf("< <= > >= == !=")

        # Logical operators
        unary_logical_op = Literal('!')
        binary_logical_op = oneOf("&& || -> <->")

        interval = Literal('[') + integer_number + Literal(',') + integer_number + Literal(']')

        # Temporal operators
        unary_temporal_op = oneOf("G F")
        unary_temporal_prefix = unary_temporal_op + interval

        binary_temporal_op = Literal('U')
        binary_temporal_prefix = binary_temporal_op + interval

        # Define expressions
        expr = Forward()

        # Parentheses for grouping
        parens = Group(Literal("(") + expr + Literal(")"))

        # Building the expressions
        binary_relation = Group(identifier + relational_op + real_number) | Group(
            identifier + relational_op + identifier)
        binary_variable = Group(identifier)
        unary_relation = Group(Optional(binary_temporal_prefix) + unary_logical_op + expr)

        # Expression with all options
        expr <<= infixNotation(binary_relation | unary_relation | binary_variable | parens,
                               [(unary_temporal_prefix, 1, opAssoc.RIGHT),
                                (unary_logical_op, 1, opAssoc.RIGHT),
                                (binary_temporal_prefix, 2, opAssoc.LEFT),
                                (binary_logical_op, 2, opAssoc.LEFT)
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

    def is_comp_operator(o):
        return any(map(lambda x: o == x, ['<', '<=', '>', '>=', '==', '!=']))

    def list_to_stl_list(formula):
        if isinstance(formula, list):
            if len(formula) == 3 and formula[0] == '(' and formula[2] == ')':
                return STLParser.list_to_stl_list(formula[1])

            op = next(filter(STLParser.is_stl_operator, formula), None)
            if op is not None:
                stl_list = [STLParser.list_to_stl_list(el) for el in formula if not STLParser.is_stl_operator(el) and all(map(lambda x: el != x, ['[', ']', ',']))]
                if op == 'U': # We must bring forward intervals of infix operators
                    prefix = [op] + stl_list[1:3]
                    del stl_list[1:3]
                    return prefix + stl_list
                return [op] + stl_list
            else:
                op = next(filter(STLParser.is_comp_operator, formula), None)
                if op is not None:
                    return ['R_' + ' '.join(formula)]

                # Should be a proposition in this case
                assert len(formula) == 1
                return ['B_' + formula[0]]
        else:
            assert isinstance(formula, str) and formula.isdigit()
            return formula

formula = "(y>6) U[3,7] (y < 3)"
parser = STLParser()
print(parser.parse_formula_as_stl_list(formula))
parser.parse_formula_as_node(formula)
