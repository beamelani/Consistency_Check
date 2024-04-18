#Authors: Ezio Bartocci, Beatrice Melani
# STL Consistency Checking (ver 0.1)
# Date: 17-04-2024
#
# Parser for Signal Temporal Logic (STL) formulas (discrete semantics)


from pyparsing import (Optional, Combine, Literal, Word, alphas, nums, alphanums, Group, Forward, infixNotation, opAssoc, oneOf)

class SyntaxError(Exception):
    """Base class for other exceptions"""
    pass


class STLVisitor:
    def visit(self, node):
        # Determine the type of the node and call the appropriate visit method
        if isinstance(node, list):
            if len(node) == 1:
                # Single element (either a terminal or a unary expression)
                return self.visit(node[0])
            elif not isinstance(node[0], list):
                if node[0] in {'!'}:
                    return self.visit_unary_logical(node[0], node[1])
                elif node[0] in {'G', 'F'}:  # Temporal operators with a single argument
                    if (int(node[2]) > int(node[4])):
                        raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                    return self.visit_unary_temporal_operator(node[0], node[2], node[4], node[6])
            elif not isinstance(node[1], list):
                if node[1] in {'U'}:  # Temporal operators with two arguments
                    print(node[0])
                    print(node[7])
                    return self.visit_binary_temporal_operator(node[1], node[3], node[5], node[0], node[7])
                elif node[1] in {'&&', '||', '->', '<->'}:  # Binary logical operators
                    return self.visit_binary_logical(node[1], node[0], node[2])
                elif node[1] in {'<', '<=', '>', '>=', '==', '!='}:  # Binary relational operators
                    return self.visit_binary_relational(node[1], node[0], node[2])
        elif isinstance(node, str):
            return self.visit_identifier(node)

    def visit_unary_temporal_operator(self, operator, time_interval_low, time_interval_high, expr):
        # Visit the expression within the temporal operator
        print(f"Visiting Unary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        return operator, self.visit(expr)

    def visit_binary_temporal_operator(self, operator, time_interval_low, time_interval_high, left, right):
        # Visit the expression within the temporal operator
        print(f"Visiting Binary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        print(left)
        print(right)
        return operator, self.visit(left), self.visit(right)

    def visit_unary_logical(self, operator, expr):
        # Visit both sides of the logical expression
        print(f"Visiting Unary Logical Operator: {operator}")
        return operator, self.visit(expr)

    def visit_binary_logical(self, operator, left, right):
        # Visit both sides of the logical expression
        print(f"Visiting Logical Operator: {operator}")
        return operator, self.visit(left), self.visit(right)

    def visit_binary_relational(self, operator, left, right):
        # Visit both sides of the relational expression
        print(f"Visiting Relational Operator: {operator}")
        return operator, self.visit(left), self.visit(right)

    def visit_identifier(self, identifier):
        # Simply return the identifier, in more complex cases you might want to look up values
        print(f"Visiting Identifier: {identifier}")
        return identifier


def create_stl_parser():
    # Basic elements
    identifier = Word(alphas, alphanums + "_")

    non_zero_digit = "123456789"
    zero = "0"
    integer_number = Word(non_zero_digit, nums) | zero

    point = "."
    e = Word("eE", exact=1)
    plus_or_minus = Word("+-", exact=1)
    real_number = Combine(Optional(plus_or_minus) + Word(nums) + Optional(point + Optional(Word(nums))) + Optional(e + Optional(plus_or_minus) + Word(nums)))


    # Define relational operators
    relational_op = oneOf("< <= > >= == !=")

    # Logical operators
    unary_logical_op = Literal('!')
    binary_logical_op = oneOf("&& || -> <->")

    # Temporal operators
    unary_temporal_op = oneOf("G F")
    unary_temporal_prefix = unary_temporal_op + Literal('[') + integer_number + Literal(',') + integer_number + Literal(']')

    binary_temporal_op = Literal('U')
    binary_temporal_prefix = binary_temporal_op + Literal('[') + integer_number + Literal(',') + integer_number + Literal(']')

    # Define expressions
    expr = Forward()

    # Parentheses for grouping
    parens = Group(Literal("(") + expr + Literal(")"))

    # Building the expressions
    binary_relation = Group(identifier + relational_op + real_number)

    # Expression with all options
    expr <<= infixNotation(binary_relation | parens,
                           [ (unary_temporal_prefix, 1, opAssoc.RIGHT),
                             (unary_logical_op, 1, opAssoc.RIGHT),
                             (binary_temporal_prefix, 2, opAssoc.LEFT),
                             (binary_logical_op, 2, opAssoc.LEFT)
                           ])

    return expr

# Example parser usage
def parse_stl_expression(expression):
    stl_parser = create_stl_parser()
    parsed_expression = stl_parser.parseString(expression, parseAll=True)
    return parsed_expression.asList()

# Example STL expression
stl_expression = "(! x<0 && y>0) U[1,5] ( y > 6.07)"
parsed_expr = parse_stl_expression(stl_expression)
print("Parsed STL Expression:", parsed_expr)

# Create a visitor and visit the parsed expression
visitor = STLVisitor()
result = visitor.visit(parsed_expr)
print("Result of visiting:", result)
