from pyparsing import *
# NB: quando scrivi la formula STL
#     1) G,F,U devono essere sempre seguiti dal bound temporale e poi da una parentesi tonda
#     2) gli operatori logici devono essere preceduti e seguiti da cose tra parentesi tonde (a meno che non si tratti di un numero o singola variabile
def create_stl_parser():
    # Basic elements
    identifier = Word(alphas, alphanums + "_")
    number = Word(nums + ".")  # Allow floating point numbers

    # Parentheses and commas
    lpar = Literal("(").suppress()
    rpar = Literal(")").suppress()
    lbrack = Literal("[").suppress()
    rbrack = Literal("]").suppress()
    comma = Literal(",").suppress()

    # Define relational operators
    relational_op = oneOf("< <= > >= == !=")

    # Logical operators
    logical_op = oneOf("&& || ! =>")

    # Temporal operators
    temporal_op = oneOf("G F")
    until = ("U")
    temporal_prefix = temporal_op + lbrack + number + comma + number + rbrack
    temporal_prefix_until = until+ lbrack + number + comma + number + rbrack


    # Define expressions
    expr = Forward()

    # Parentheses for grouping
    parens = lpar + expr + rpar

    # Building the expressions
    binary_relation = Group(identifier + relational_op + identifier | identifier + relational_op + number)
    logical_expr = Group(expr + logical_op + expr)
    temporal_expr = Group(temporal_prefix + expr)
    temporal_expr_until = Group(expr + temporal_prefix_until + expr)

    # Expression with all options
    expr <<= infixNotation(binary_relation | identifier | number | parens,
                           [
                               (temporal_prefix, 1, opAssoc.RIGHT),
                               (temporal_prefix_until, 2, opAssoc.LEFT),
                               ("!", 1, opAssoc.RIGHT),
                               ("&&", 2, opAssoc.LEFT),
                               ("||", 2, opAssoc.LEFT),
                               ("=>", 2, opAssoc.LEFT)
                           ])

    return expr

def parse_stl_expression(expression):
    stl_parser = create_stl_parser()
    parsed_expression = stl_parser.parseString(expression, parseAll=True)
    return parsed_expression.asList()

class STLVisitor:
    def visit(self, node):
        # Determine the type of the node and call the appropriate visit method
        if isinstance(node, list):
            if len(node) == 1:
                # Single element (either a terminal or a unary expression)
                return self.visit(node[0])
            elif isinstance(node[0], str) and node[0] in {'G', 'F'}:  # Temporal operators with a single argument
                return self.visit_temporal_operator(node[0], node [1:3], node[3:])
            elif node[1] in {'&&', '||', '=>'}:  # Binary logical operators
                return self.visit_binary_logical(node[1], node[0], node[2])
            elif node[1] in {'<', '<=', '>', '>=', '==', '!='}:  # Binary relational operators
                return self.visit_binary_relational(node[1], node[0], node[2])
            #elif node[1] in {'U'}: #temporal operator with two arguments
                #return self.visit_until(node[1], node[0], node[2:4], node[4:])
        elif isinstance(node, str):
            return self.visit_identifier(node)

    def visit_temporal_operator(self, operator, time_interval, expr):
        # Visit the expression within the temporal operator
        print(f"Visiting Temporal Operator: {operator}")
        print(f"Visiting Time Interval: [{time_interval[0]}, {time_interval[1]}]") #aggiunto io
        return operator, time_interval, [self.visit(e) for e in expr]

    def visit_binary_logical(self, operator, left, right):
        # Visit both sides of the logical expression
        print(f"Visiting Logical Operator: {operator}")
        return operator, self.visit(left), self.visit(right)

    def visit_binary_relational(self, operator, left, right):
        # Visit both sides of the relational expression
        print(f"Visiting Relational Operator: {operator}")
        return operator, self.visit(left), self.visit(right)
    #def visit_until(self, argument, node[2:4], node[4:])
    def visit_identifier(self, identifier):
        # Simply return the identifier, in more complex cases you might want to look up values
        print(f"Visiting Identifier: {identifier}")
        return identifier


# Example STL expression
#stl_expression = "G[0,5] ((x > 3) && (F[2,7] (y < 2)))"
stl_expression = "G[0,5] ((x > 3) && (y < 2))"
#stl_expression = "G[0,5] ((F[2,7] (y < 2)))"
#stl_expression = "G[0,5] (z == 2)"
#stl_expression = "G[0,5] (F[7,9] (x > 3))"
#stl_expression = "G[0,10](x U[2,5] y)" #Until è sistemato
# stl_expression = "G[0,5] (!(x && y == 5))"
# stl_expression = "G[0,10] ((x > 0) => (F[0,5] (y > 0)))" #aggiunto simbolo =>
# stl_expression = "G[0,5] (x && y)"


parsed_expr = parse_stl_expression(stl_expression)
print("Parsed STL Expression:", parsed_expr)


# Create a visitor and visit the parsed expression
visitor = STLVisitor()
result = visitor.visit(parsed_expr)
print("Result of visiting:", result)

#Dopo aver fatto il visiting dell'espressione, devi scrivere una funzione
#che prende l'until (se c'è) e lo riscrive in questo modo:

#x U[a,b] y = G[0,a] (x) && F[a,b] (y) && F[a,a](x U y)
