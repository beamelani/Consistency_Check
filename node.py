
## TODO: adapt for class representation
def formula_to_string(formula):
    """
    :param formula:
    :return: trasforma la lista in una stringa per utilizzarla nell'etichetta del nodo del grafo e stamparla
    """
    if isinstance(formula, list) and len(formula) == 1 and isinstance(formula[0], list): # se ho [[formula]]
        formula = formula[0]

    if isinstance(formula, list) and len(formula) == 1 and isinstance(formula[0], str): #serve per formule del tipo ['p']
        return formula[0]

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



class Node:
    def __init__(self, operator, *args):
        self.current_time = None
        self.initial_time = None
        self.is_derived = False
        self.operator = operator
        if operator in {'&&', '||', ',', '!', 'O'}:
            self.lower = self.upper = -1
            self.operands = args
        elif operator in {'G', 'F', 'U', 'R'}:
            self.lower = args[0]
            self.upper = args[1]
            self.operands = args[2:]
        elif isinstance(operator, str) and len(args) == 0:
            self.lower = self.upper = -1
            self.operator = 'P'
            self.operands = [operator]
        else:
            raise ValueError('Bad formula')

        # Convert operands to Nodes, if any
        if self.operator != 'P':
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
        if self.operator in {'&&', '||', ',', '!', 'O'}:
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
