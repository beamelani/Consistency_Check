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

## TODO: adapt for class representation
def formula_to_string(formula):
    """
    :param formula:
    :return: trasforma la lista in una stringa per utilizzarla nell'etichetta del nodo del grafo e stamparla
    """
    if isinstance(formula, list) and len(formula) == 1 and isinstance(formula[0], list): # se ho [[formula]]
        formula = formula[0]

    if isinstance(formula, list) and len(formula) == 1 and isinstance(formula[0], str): #serve per formule del tipo ['p']
        return formula[0][2:]

    if isinstance(formula, str): #probabilemente non serve
        return formula

    operator = formula[0]

    if operator == 'G':
        _, lowerb, upperb, arg = formula
        return f"G[{lowerb}, {upperb}] ({formula_to_string(arg)})"

    elif operator == 'F':
        _, lowerb, upperb, arg = formula
        return f"F[{lowerb}, {upperb}] ({formula_to_string(arg)})"

    elif operator == 'O':
        _, arg = formula
        return f"O ({formula_to_string(arg)})"

    elif operator == '!':
        _, arg = formula
        return f"!({formula_to_string(arg)})"

    elif operator == 'U':
        _, lowerb, upperb, arg1, arg2 = formula
        return f"({formula_to_string(arg1)}) U[{lowerb}, {upperb}] ({formula_to_string(arg2)})"

    elif operator == 'R':
        _, lowerb, upperb, arg1, arg2 = formula
        return f"({formula_to_string(arg1)}) R[{lowerb}, {upperb}] ({formula_to_string(arg2)})"

    elif operator == '&&':
        subformulas = [f"({formula_to_string(subformula)})" for subformula in formula[1:]]
        return " && ".join(subformulas)

    elif operator == ',':
        subformulas = [f"({formula_to_string(subformula)})" for subformula in formula[1:]]
        return " , ".join(subformulas)

    elif operator == '||':
        subformulas = [f"({formula_to_string(subformula)})" for subformula in formula[1:]]
        return " || ".join(subformulas)

    elif operator == '->':  # Implication
        _,  arg1, arg2 = formula
        return f"({formula_to_string(arg1)}) -> ({formula_to_string(arg2)})"


def arith_expr_to_string(expr):
    if isinstance(expr, list):
        if len(expr) == 3 and expr[0] in {'<', '<=', '>', '>=', '==', '!=', '+', '-'}:
            return ' '.join([arith_expr_to_string(expr[1]), expr[0], arith_expr_to_string(expr[2])])
        elif len(expr) == 1 and isinstance(expr[0], str):
            return expr[0]
    elif isinstance(expr, str):
        return expr
    else:
        raise ValueError('Bad operator')


class Node:
    def __init__(self, operator, *args):
        self.current_time = None
        self.initial_time = '-1'
        self.is_derived = False
        self.identifier = None
        self.implications = None
        self.operator = operator
        if operator in {'&&', '||', ',', '!', 'O', '->', '<->'}:
            self.lower = self.upper = -1
            self.operands = list(args)
            if operator in {'&&', ','}:
                self.satisfied_implications = []
        elif operator in {'G', 'F', 'U', 'R'}:
            self.lower = args[0]
            self.upper = args[1]
            self.operands = list(args[2:])
        elif operator in {'<', '<=', '>', '>=', '==', '!='}:
            # The comparison is flattened into a str in this case
            # TODO: fix smt_check in tableau to accept list representation
            self.lower = self.upper = -1
            self.operator = 'P'
            self.operands = [arith_expr_to_string([operator] + list(args))]
        elif isinstance(operator, str) and len(args) == 0:
            self.lower = self.upper = -1
            self.operator = 'P'
            self.operands = [operator]
        else:
            print(operator, args)
            raise ValueError('Bad formula' + operator + str(args))

        # Convert operands to Nodes, if any
        if self.operator != 'P' and len(self.operands) > 0 and not isinstance(self.operands[0], Node):
            self.operands = [Node(*op) for op in self.operands]

    def set_current_time(self, time):
        self.current_time = time
    
    def get_current_time(self):
        return self.current_time

    def lower_bound(self):
        return self.lower

    def upper_bound(self):
        return self.upper

    def to_list(self):
        '''
        Convert node to list representation
        '''
        if self.operator in {'&&', '||', ',', '!', 'O', '->', '<->'}:
            return [self.operator] + [op.to_list() for op in self.operands]
        elif self.operator in {'G', 'F', 'U', 'R'}:
            return [self.operator, self.lower, self.upper] + [op.to_list() for op in self.operands]
        elif self.operator == 'P':
            return self.operands
        else:
            raise ValueError('Unknown operator')

    def to_label(self, counter):
        '''
        Use node.to_label(counter) to create a label for a graph node.
        The current time must be set before using this method with node.set_current_time()
        '''
        return " ".join([formula_to_string(self.to_list()), str(self.current_time), str(counter)])

    def __getitem__(self, i):
        '''
        Can be used to write e.g. node[0] to get the first operand
        '''
        return self.operands[i]

    def flatten(self, now_operands):
        if self.operator in {'&&', '||', ','}:
            for i in range(len(self.operands)):
                if self.operands[i].operator == self.operator:
                    self.operands[i:i+1] = self.operands[i].operands
