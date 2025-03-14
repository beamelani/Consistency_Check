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

class Node:
    def __init__(self, *args):
        if len(args) == 0:
            return # We create an empty object to be filled later
        operator = args[0]
        args = args[1:]

        # If you add more fields, remember to update shallow_copy
        self.current_time = None
        self.initial_time = '-1' # the initial time of the outer operator of a nested operator
        self.is_derived = False  # tells if a temporal operand is derived from the decomposition of a nested temporal operand
        self.identifier = None   # a number that uniquely identifies (some) operands
        self.implications = None # counts how many implications need to be satisfied at a given time instant
        self.operator = operator
        self.id_implication = -1 # serve per identificare da quale el. dell'implicazione proviene un termine quando è stato estratto (mi serve se l'impl è annidata e ha elementi con G e devo quindi sapere quale el incrementare invece di estrarre)
        self.and_element = -1 # identifica univoc gli operandi di un && dentro a un G
        self.or_element = -1 # identifica univoc gli operandi di un || dentro a un G
        self.jump1 = False # needed because in some instances you can only jump 1 step to make sure you do not miss anything important
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
            self.real_expr_id = None
            self.lower = self.upper = -1
            self.operator = 'P'
            self.operands = [operator] + list(args)
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

    def replace_operand(self, index, new_operand, *more_new_operands):
        '''
        Replaces the operand at the given index with the new operand(s),
        appending operands other than the first to the end.
        '''
        self.operands[index] = new_operand
        self.operands.extend(more_new_operands)

    def shallow_copy(self):
        new = Node()
        new.current_time = self.current_time
        new.initial_time = self.initial_time
        new.is_derived = self.is_derived
        new.identifier = self.identifier
        new.implications = self.implications
        new.operator = self.operator
        new.id_implication = self.id_implication
        new.and_element = self.and_element
        new.or_element = self.or_element
        new.jump1 = self.jump1
        new.lower = self.lower
        new.upper = self.upper
        new.operands = self.operands.copy()
        if hasattr(self, 'satisfied_implications'):
            new.satisfied_implications = self.satisfied_implications.copy()
        if hasattr(self, 'counter_F'):
            new.counter_F = self.counter_F
        if hasattr(self, 'real_expr_id'):
            new.real_expr_id = self.real_expr_id
        return new

    def __list__(self):
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
        return " ".join([str(self), str(self.current_time), str(self.counter)])

    def set_min_time(self):
        '''
        :param formula:
        :return: estrae il min lower bound della formula e setta il current_time
        '''
        match self.operator:
            case 'P' | '!':
                min_time = None
            case 'G' | 'F' | 'U' | 'R':
                min_time = self.lower
            case 'O':
                min_time = self.operands[0].lower
            case '&&' | '||' | ',' | '->':
                min_time = None
                for op in self.operands:
                    op_time = op.set_min_time()
                    if op_time is not None and (min_time is None or op_time < min_time):
                        min_time = op_time
            case _:
                raise ValueError(f'Operator {self.operator} not handled')
        self.current_time = min_time
        return min_time

    def get_max_upper(self):
        '''
        :return: the maximum upper bound from temporal operators in the first-level
                 boolean closure of self, and -1 if self is purely propositional
        '''
        match self.operator:
            case '&&' | '||' | ',' | '->' | '!':
                return max(op.get_max_upper() for op in self.operands)
            case _:
                # Works because in all non-temporal operators self.upper == -1
                return self.upper

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

    def __str__(self):
        match self.operator:
            case 'G' | 'F':
                return f"{self.operator}[{self.lower},{self.upper}] {self.operands[0]}"
            case 'O' | '!':
                return f"{self.operator} {self.operands[0]}"
            case 'U' | 'R':
                return f"({self.operands[0]}) {self.operator}[{self.lower},{self.upper}] ({self.operands[1]})"
            case '&&' | '||' | '->':
                return f"({f' {self.operator} '.join(str(op) for op in self.operands)})"
            case ',':
                return f"({', '.join(str(op) for op in self.operands)})"
            case 'P':
                if len(self.operands) == 1:
                    return self.operands[0]
                else:
                    return Node.arith_expr_to_string(self.operands)
            case _:
                raise ValueError(f'Operator {self.operator} not handled.')

    def arith_expr_to_string(expr):
        if isinstance(expr, list):
            if len(expr) == 3 and expr[0] in {'<', '<=', '>', '>=', '==', '!=', '+', '-'}:
                return ' '.join([Node.arith_expr_to_string(expr[1]), expr[0], Node.arith_expr_to_string(expr[2])])
            elif len(expr) == 2 and expr[0] == 'abs':
                return f'|{Node.arith_expr_to_string(expr[1])}|'
            elif len(expr) == 1 and isinstance(expr[0], str):
                return expr[0]
        elif isinstance(expr, str):
            return expr
        else:
            raise ValueError('Bad operator')

    def __hash__(self):
        '''
        Node: only hashes formula content!
        '''
        return hash((
            self.operator, self.lower, self.upper,
            Node.lists_to_tuples(self.operands) if self.operator == 'P' else tuple(self.operands)
        ))

    def __eq__(self, other):
        '''
        Note: only checks formula equality!
        '''
        return isinstance(other, Node) and (self.operator, self.lower, self.upper, self.operands) == (other.operator, other.lower, other.upper, other.operands)

    def __lt__(self, other):
        return (self.operator, self.lower, self.upper, self.operands) < (other.operator, other.lower, other.upper, other.operands)
    
    def __le__(self, other):
        return (self.operator, self.lower, self.upper, self.operands) <= (other.operator, other.lower, other.upper, other.operands)

    def __gt__(self, other):
        return (self.operator, self.lower, self.upper, self.operands) > (other.operator, other.lower, other.upper, other.operands)
    
    def __ge__(self, other):
        return (self.operator, self.lower, self.upper, self.operands) >= (other.operator, other.lower, other.upper, other.operands)

    def get_imply_sort_key(self, time=None):
        if time is None:
            time = self.current_time
        return (
            self.operator,
            self.operands,
            self.lower - time,
            self.upper - time
        )

    def get_imply_search_key(self):
        return (
            self.operator,
            self.operands
        )

    def sort_operands(self):
        self.operands.sort(key=lambda op: op.get_imply_sort_key(self.current_time))

    def implies_quick_inner(self, other, time_self, time_other):
        if self.operator != other.operator:
            return False
        match self.operator:
            case 'F':
                return self.operands[0] == other.operands[0] and other.lower - time_other <= self.lower - time_self and other.upper - time_other >= self.upper - time_self
            case 'G':
                return self.operands[0] == other.operands[0] and self.lower - time_self <= other.lower - time_other and self.upper - time_self >= other.upper - time_other
            case 'P':
                return self.operands[0] == other.operands[0]
            case '!':
                return self.operands[0].implies_quick_inner(other.operands[0])
            # TODO: U, R, etc
        return False

    def implies_quick(self, other):
        '''
        :return: True if we can quickly determine that self implies other, False otherwise
        Assumes both nodes' operands have been sorted with sort_operands
        '''
        assert self.operator == other.operator == ','
        j = 0
        len_operands = len(self.operands)
        for i in range(len(other.operands)):
            not_implies = order = True
            while j < len_operands and not_implies and order:
                if self.operands[j].implies_quick_inner(other.operands[i], self.current_time, other.current_time):
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

    def lists_to_tuples(l):
        if isinstance(l, list) or isinstance(l, tuple):
            return tuple(Node.lists_to_tuples(el) for el in l)
        return l

    def check_boolean_closure(self, pred):
        match self.operator:
            case '!' | '&&' | '||' | ',' | '->':
                return any(op.check_boolean_closure(pred) for op in self.operands)
            case _:
                return pred(self)
