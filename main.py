# Authors: Ezio Bartocci, Beatrice Melani
# STL Consistency Checking (ver 0.2)
# Date: 22-04-2024
#
# Parser for Signal Temporal Logic (STL) formulas (discrete semantics)


from pyparsing import (Optional, Combine, Literal, Word, alphas, nums, alphanums, Group, Forward, infixNotation, opAssoc, oneOf)

class SyntaxError(Exception):
    """Base class for other exceptions"""
    pass


class STLVisitor:

    def __init__(self):
        self._variables          = {}  # Protected variable
        self._real_constraints   = {}  # Protected variable
        self._binary_constraints = {}  # Protected variable
        self._basic_propositions = {}  # Protected variable
        self._prop_count         = 0   # Protected variable


    def print_vars(self):
        print(self._variables)
        print(self._real_constraints)
        print(self._binary_constraints)
        print(self._basic_propositions)

    def visit(self, node):
        # Determine the type of the node and call the appropriate visit method
        if isinstance(node, list):
            if len(node) == 1:
                # Single element (either a terminal or a unary expression)
                if isinstance(node[0], str) and len(node[0]) == 1:
                    return self.visit_binary_variable(node[0])
                return self.visit(node[0])
            elif len(node) == 3 and isinstance(node[0], str) and isinstance(node[1], str) and isinstance(node[2], str):
                if node[1] in {'<', '<=', '>', '>=', '==', '!='}:
                    return self.visit_binary_relational(node[1], node[0], node[2])
            elif not isinstance(node[0], list):
                if node[0] in {'!'}:
                    return self.visit_unary_logical(node[0], node[1])
                elif node[0] in {'('} and node[len(node)-1] in {')'}:
                    return self.visit_parenthesis(node[0], node[len(node)-1], node[1])
                elif node[0] in {'G', 'F'}:  # Temporal operators with a single argument
                    if (int(node[2]) > int(node[4])):
                        raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                    return self.visit_unary_temporal_operator(node[0], node[2], node[4], node[6])
            elif isinstance(node[1], str):
                print(node[0])
                if node[1] in {'U'}:  # Temporal operators with two arguments
                    if (int(node[3]) > int(node[5])):
                        raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                    return self.visit_binary_temporal_operator(node[1], node[3], node[5], node[0], node[7])
                elif node[1] in {'&&', '||', '->', '<->'}:  # Binary logical operators
                    return self.visit_binary_logical(node[1], node[0], node[2:])
        elif isinstance(node, str):
            return self.visit_identifier(node)


    def visit_parenthesis(self, openPar, closePar, expr):
        # Visit the expression within the temporal operator
        print(f"Visiting parenthesis: {openPar}{closePar}")
        prop0 = [self.visit(expr)]
        prop = f"_phi{self._prop_count}"
        self._basic_propositions[prop] = prop0
        self._prop_count = self._prop_count + 1
        return prop

    def visit_unary_temporal_operator(self, operator, time_interval_low, time_interval_high, expr):
        # Visit the expression within the temporal operator
        print(f"Visiting Unary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        prop0 = [operator, time_interval_low, time_interval_high, self.visit(expr)]
        prop = f"_phi{self._prop_count}"
        self._basic_propositions[prop] = prop0
        self._prop_count = self._prop_count + 1

        return prop

    def visit_binary_temporal_operator(self, operator, time_interval_low, time_interval_high, left, right):
        # Visit the expression within the temporal operator
        print(f"Visiting Binary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        return operator, self.visit(left), self.visit(right)

    def visit_unary_logical(self, operator, expr):
        # Visit both sides of the logical expression
        print(f"Visiting Unary Logical Operator: {operator}")

        prop0 = [operator, self.visit(expr)]
        prop = f"_phi{self._prop_count}"
        self._basic_propositions[prop] = prop0
        self._prop_count = self._prop_count + 1
        return prop

    def visit_binary_logical(self, operator, left, right):
        # Visit both sides of the logical expression
        print(f"Visiting Logical Operator: {operator}")
        if operator in {'&&', '||'}:
            prop0 = [operator, self.visit(left), self.visit(right)]
            prop = f"_phi{self._prop_count}"
            self._basic_propositions[prop] = prop0
            self._prop_count = self._prop_count + 1
        elif operator in {'->'}:
            prop0 = ['!', self.visit(left)]
            prop = f"_phi{self._prop_count}"
            self._basic_propositions[prop] = prop0
            self._prop_count = self._prop_count + 1
            prop1 = ['||', prop, self.visit(right)]
            prop = f"_phi{self._prop_count}"
            self._basic_propositions[prop] = prop1
            self._prop_count = self._prop_count + 1
        elif operator in {'<->'}:
            p = self.visit(left)
            q = self.visit(right)
            p_and_q = self.visit_binary_logical('&&', p, q)
            np_and_nq = self.visit_binary_logical('&&', self.visit_unary_logical('!', p), self.visit_unary_logical('!', q))
            prop = self.visit_binary_logical('||', p_and_q, np_and_nq)
        return prop

    def visit_binary_relational(self, operator, left, right):
        # Visit both sides of the relational expression
        print(f"Visiting Relational Operator: {operator}")
        prop = ""

        if left in self._variables:
            print(f"Key '{left}' is in the dictionary.")

            if (self._variables[left] == 'binary'):
                raise SyntaxError(f"Variable '{left}' cannot be real and binary")

            print(self._real_constraints[left].keys())
            if operator in self._real_constraints[left].keys():
                print(f"'{operator}' is in {self._real_constraints[left].keys()}")
                if right in self._real_constraints[left][operator].keys():
                     prop = self._real_constraints[left][operator][right]
                     print(prop)
                else:
                     prop = f"_phi{self._prop_count}"
                     self._real_constraints[left][operator] = {right: prop}
                     self._basic_propositions[prop] = [left, operator, right]
                     self._prop_count = self._prop_count + 1
            else:
                print(f"'{operator}' is not in {self._real_constraints[left].keys()}")
                prop = f"_phi{self._prop_count}"
                self._real_constraints[left][operator]={right:prop}
                self._basic_propositions[prop] = [left, operator, right]
                self._prop_count = self._prop_count + 1

        else:
            print(f"Key '{left}' is not in the dictionary.")
            self._variables[left] = 'real'
            print(f"Key '{left}' added in the dictionary.")
            prop = f"_phi{self._prop_count}"
            self._real_constraints[left] = {operator:{right:prop}}
            self._basic_propositions[prop] = [left, operator, right]
            self._prop_count = self._prop_count + 1

        return prop


    def visit_binary_variable(self, binary_var):
        # Simply return the identifier, in more complex cases you might want to look up values
        print(f"Visiting Binary Variable: {binary_var}")
        prop = ""
        if binary_var in self._variables:
            print(f"Key '{binary_var}' is in the dictionary.")
            if (self._variables[binary_var] == 'real'):
                raise SyntaxError(f"Variable '{binary_var}' cannot be real and binary")
            prop = self._binary_constraints[binary_var]
        else:
            print(f"Key '{binary_var}' is not in the dictionary.")
            self._variables[binary_var] = 'binary'
            print(f"Key '{binary_var}' added in the dictionary.")
            prop = f"_phi{self._prop_count}"
            self._binary_constraints[binary_var] = prop
            self._basic_propositions[prop] = [binary_var]
            self._prop_count = self._prop_count + 1

        return prop

    def visit_identifier(self, identifier):
        # Simply return the identifier, in more complex cases you might want to look up values
        # print(f"Visiting Identifier: {identifier}")
        return identifier







def create_stl_parser():
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
    real_number = Combine(Optional(plus_or_minus) + Word(nums) + Optional(point + Optional(Word(nums))) + Optional(e + Optional(plus_or_minus) + Word(nums)))


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
    binary_relation = Group(identifier + relational_op + real_number)
    binary_variable = Group(identifier)

    # Expression with all options
    expr <<= infixNotation(binary_relation | binary_variable | parens,
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
stl_expression = " F [0,5] a > 0 && ! b > 0"
parsed_expr = parse_stl_expression(stl_expression)
print("Parsed STL Expression:", parsed_expr)

# Create a visitor and visit the parsed expression
visitor = STLVisitor()
result = visitor.visit(parsed_expr)
print("Result of visiting:", result)

visitor.print_vars()


