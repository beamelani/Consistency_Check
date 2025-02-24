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
        self.initial_time = '-1' # the initial time of the outer operator of a nested operator
        self.is_derived = False  # tells if a temporal operand is derived from the decomposition of a nested temporal operand
        self.identifier = None   # a number that uniquely identifies (some) operands
        self.implications = None # counts how many implications need to be satisfied at a given time instant
        self.operator = operator
        self.id_implication = -1 # serve per identificare da quale el. dell'implicazione proviene un termine quando è stato estratto (mi serve se l'impl è annidata e ha elementi con G e devo quindi sapere quale el incrementare invece di estrarre)
        self.and_element = -1 # identifica univoc gli operandi di un && dentro a un G
        self.or_element = -1 # identifica univoc gli operandi di un || dentro a un G
        self.execution_time = -1 # serve in nodi con operator = 'P'
        if operator in {'&&', '||', ',', '!', 'O', '->', '<->'}:
            self.lower = self.upper = -1
            self.operands = list(args)
            if operator in {'&&', ','}:
                self.satisfied_implications = []
        elif operator in {'G', 'F', 'U', 'R'}:
            self.lower = int(args[0])
            self.upper = int(args[1])
            self.operands = list(args[2:])
            if operator == 'G':
                self.counter_F = 0 #needed in case you have GF and need to keep track of when F is satisfied
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

    def to_label(self):
        '''
        Use node.to_label(counter) to create a label for a graph node.
        The current time must be set before using this method with node.set_current_time()
        '''
        return " ".join([formula_to_string(self.to_list()), str(self.current_time), str(self.counter)])

    def __getitem__(self, i):
        '''
        Can be used to write e.g. node[0] to get the first operand
        '''
        return self.operands[i]

    def flatten(self):
        if self.operator in {'&&', '||', ','}:
            for i in range(len(self.operands)):
                self.operands[i].flatten()
                if self.operands[i].operator == self.operator:
                    self.operands[i:i+1] = self.operands[i].operands
        if self.operator != 'P':
            for op in self.operands:
                op.flatten()

    def __lt__(self, other):
        return (self.operator, self.lower, self.upper, self.operands) < (other.operator, other.lower, other.upper, other.operands)
    
    def __le__(self, other):
        return (self.operator, self.lower, self.upper, self.operands) <= (other.operator, other.lower, other.upper, other.operands)

    def __gt__(self, other):
        return (self.operator, self.lower, self.upper, self.operands) > (other.operator, other.lower, other.upper, other.operands)
    
    def __ge__(self, other):
        return (self.operator, self.lower, self.upper, self.operands) >= (other.operator, other.lower, other.upper, other.operands)

    def get_imply_sort_key(self):
        return (
            # We put ops that generate just one child first so they are decomposed first
            'A' + self.operator if self.operator in {'&&', ',', 'G'} else self.operator,
            self.operands,
            self.lower - (self.current_time if self.current_time else 0),
            self.upper - (self.current_time if self.current_time else 0)
        )

    def get_imply_search_key(self):
        return (
            'A' + self.operator if self.operator in {'&&', ',', 'G'} else self.operator,
            self.operands
        )

    def sort_operands(self):
        self.operands.sort(key=Node.get_imply_sort_key)
    
    def implies_quick(self, other):
        '''
        :return: True if we can quickly determine that self implies other, False otherwise
        Assumes both nodes' operands have been sorted with sort_operands
        '''
        if self.operator != other.operator:
            return False
        match self.operator:
            case ',':
                j = 0
                for i in range(len(other.operands)):
                    not_implies = order = True
                    while j < len(self.operands) and not_implies and order:
                        if self.operands[j].implies_quick(other.operands[i]):
                            not_implies = False
                            break
                        if other.operands[i].get_imply_search_key() < self.operands[j].get_imply_search_key():
                            order = False
                            break
                        j += 1
                    if not_implies: # j >= len(self.operands) or not order:
                        # we break the loop because no operand in self implies other.operands[i]
                        return False
                return True
            case 'F': # TODO normalize times
                # TODO implement __eq__ to avoid to_list
                return self.operands[0].to_list() == other.operands[0].to_list() and other.lower - other.current_time <= self.lower - self.current_time and other.upper - other.current_time >= self.upper - self.current_time
            case 'G':
                return self.operands[0].to_list() == other.operands[0].to_list() and self.lower - self.current_time <= other.lower - other.current_time and self.upper - self.current_time >= other.upper - other.current_time
            case '!':
                return self.operands[0].implies_quick(other.operands[0])
            case 'P':
                return self.operands[0] == other.operands[0]
            # TODO: U, R, etc
        return False
