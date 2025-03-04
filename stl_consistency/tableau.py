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

# Nuova versione del codice Tableau test che prende come input una lista del tipo:

"""
[['&&', 'sottof1', 'sottof2',...]]
|| come sopra
! come sopra
[['G', 'lowerb', 'upperb', 'arg']]
F come sopra
[['O', 'arg']]
[['U', 'lowerb', 'upperb', 'arg1', 'arg2']]
[['R', 'lowerb', 'upperb', 'arg1', 'arg2']]
[['->', 'lowerb', 'upperb', 'arg1', 'arg2']]

Sintassi Z3
Definire variabili:
x = Real('x')
p = Bool('p')
z = Int('z')

Scrivere i vincoli:

Bool constraints:
Not(p)
Implies(p,q)
Or(p,q)
And(p,q)
r == q (bi-implication)

Real Constraints, puoi scrivere con i seguenti operatori <, <=, >, >=, == , !=  espressioni del tipo:
x>5
x+y == 7
2*x+y == 1

Creare il problema con tutti i vincoli
solve(constraint1, constraint2,...)  #li considera in and
"""

'''
COSE DA FARE:
1) DONE verifica come sistemare decompose_imply nel caso in cui tu abbia una formula del tipo G(->, G..., XXX) o G(->, XXX, G...).
Quando decomponi -> estrai gli operatori interni e anche lì in alcuni casi puoi accorpare i G/F
2) verifica cosa fare nel caso in cui tu abbia G(||, G, XXX)
3) sistema il caso con G(F...) [DONE] e versioni + complesse (G(&&, F.., XXX)) 

'''


import re
import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import graphviz_layout
import random
import copy
import z3
from fractions import Fraction
from math import gcd, lcm
import bisect
import concurrent.futures as fs
from stl_consistency.node import Node
from stl_consistency.parser import STLParser

def push_negation(node):
    if node.operator == '!':
        operand = node[0]
        new_node = operand.shallow_copy()
        if operand.operator == 'P':
            return node
        elif operand.operator == ',' or operand.operator == '&&':
            new_node.operator = '||'
            new_node.operands = [push_negation(Node('!', op)) for op in operand]
        elif operand.operator == '||':
            new_node.operator = ','
            new_node.operands = [push_negation(Node('!', op)) for op in operand]
        elif operand.operator == '->':
            new_node.operator = ','
            new_node.operands = [operand[0], push_negation(Node('!', operand[1]))]
        elif operand.operator == '!':
            pass
        elif operand.operator == 'O':
            new_node.operator = operand.operator
            new_node.operands = [push_negation(Node('!', operand[0]))]
        elif operand.operator == 'G':
            new_node.operator = 'F'
            new_node.lower, new_node.upper = operand.lower, operand.upper
            new_node.operands = [push_negation(Node('!', operand[0]))]
        elif operand.operator == 'F':
            new_node.operator = 'G'
            new_node.lower, new_node.upper = operand.lower, operand.upper
            new_node.operands = [push_negation(Node('!', operand[0]))]
        elif operand.operator == 'U':
            new_node.operator = 'R'
            new_node.lower, new_node.upper = operand.lower, operand.upper
            new_node.operands = [push_negation(Node('!', operand[0])), push_negation(Node('!', operand[1]))]
        elif operand.operator == 'R':
            new_node.operator = 'U'
            new_node.lower, new_node.upper = operand.lower, operand.upper
            new_node.operands = [push_negation(Node('!', operand[0])), push_negation(Node('!', operand[1]))]
        else:
            raise ValueError('Bad formula')

        return new_node
    elif node.operator == 'P':
        return node
    else:  # Any non-negated operator
        new_node = node.shallow_copy()
        new_node.operands = [push_negation(op) for op in node.operands]
        return new_node


def set_min_time(formula):
    '''
    :param formula:
    :return: estrae il min lower bound della formula e setta il current_time
    '''
    if formula.operator in {'P'}:
        if not formula.execution_time == -1:
            min_time = formula.execution_time
        else:
            min_time = None
    elif formula.operator in {'!'}:
        if formula.operands[0].operator == 'P' and not formula.operands[0].execution_time == -1:
            min_time = formula.operands[0].execution_time
        else:
            min_time = None
    elif formula.operator in {'G', 'F', 'U', 'R'}:
        min_time = formula.lower
    elif formula.operator in {'O'}:
        min_time = formula.operands[0].lower
    elif formula.operator in {'&&', '||', ',', '->'}:
        times = []
        for op in formula.operands:
            op_time = set_min_time(op)
            if op_time is not None:
                times.append(op_time)
        min_time = min(times, default=None)
    formula.current_time = min_time
    return min_time



def calculate_time_quantum(formula):
    """
    Compute the maximum time length `quantum` such that all interval bounds are integer multiples of `quantum`.
    """
    def extract_bounds(formula):
        bounds = []
        if isinstance(formula, list):
            for elem in formula:
                if isinstance(elem, list):
                    if elem[0] in ['G', 'F', 'U', 'R']:  # Controlla operatori temporali
                        bounds.extend(elem[1:3])
                    bounds.extend(extract_bounds(elem))  # Ricorsione per esplorare strutture annidate
        return bounds

    # Extract all bounds
    bounds = extract_bounds(formula)
    denominators = {Fraction(b).denominator for b in bounds}
    return Fraction(1, lcm(*denominators))


def normalize_bounds(formula):
    quantum = calculate_time_quantum(formula)
    if quantum == 1:
        return formula

    def norm_bound(bound):
        return str(int(Fraction(bound) / quantum))

    def recompute_bounds(formula):
        if isinstance(formula, list) and formula[0]:
            if isinstance(formula[0], list):
                return list(map(recompute_bounds, formula))
            elif formula[0] in {'&&', '||', ',', '->'}:
                return [formula[0]] + list(map(recompute_bounds, formula[1:]))
            elif formula[0] in {'G', 'F'}:
                return [formula[0], norm_bound(formula[1]), norm_bound(formula[2]), recompute_bounds(formula[3])]
            elif formula[0] in {'U', 'R'}:
                return [formula[0], norm_bound(formula[1]), norm_bound(formula[2]), recompute_bounds(formula[3]),
                        recompute_bounds(formula[4])]
            elif len(formula) == 1 and isinstance(formula[0], str):
                return formula
            else:
                raise ValueError('Malformed formula ' + str(formula))
        return formula

    return recompute_bounds(formula)


def extract_time_instants(formula, flag):
    """
    :return: funzione che restituisce gli estremi di tutti gli intervalli della formula in un vettore ordinato
    (non quelli degli op derivati, eccezione se op is_derived è estratto da -> o ||)
    """
    if flag:
        time_instants = []
        if formula.operator not in {'P'}:
            for elem in formula:
                if elem.operator not in {'P'}:
                    if elem.operator in ['G', 'F', 'U', 'R'] and not elem.is_derived:
                        # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                        time_instants.append(elem.lower)
                        time_instants.append(elem.upper)
                    #caso in cui op is_derived è estratto da un -> che era dentro a un G o U o R (flag == True)
                    elif elem.operator in ['G', 'F', 'U', 'R'] and elem.is_derived and (not elem.id_implication == -1 or not elem.or_element == -1):
                        time_instants.append(elem.lower)
                        time_instants.append(elem.upper) #va fatto anche nel caso 'O' ??
                    elif elem.operator in ['O'] and not elem.operands[0].is_derived:
                        time_instants.append(elem.operands[0].lower)
                        time_instants.append(elem.operands[0].upper)
    else:
        time_instants = []
        if formula.operator not in {'P'}:
            for elem in formula:
                if elem.operator not in {'P'}:
                    if elem.operator in ['G', 'F', 'U', 'R']:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                        time_instants.append(elem.lower)
                        time_instants.append(elem.upper)
                    elif elem.operator in ['O']:
                        time_instants.append(elem.operands[0].lower)
                        time_instants.append(elem.operands[0].upper)
    assert all(isinstance(t, int) for t in time_instants)
    time_instants = sorted(time_instants)
    return time_instants


def assign_identifier(formula):
    '''
    :param formula:
    :return: la formula assegna un identificatore agli operatori nested, in modo che nella decomposizione gli operatori
    derivati dalla decomposizione di un nested siano riconducibili all'operatore originario
    '''
    counter = 0
    if formula.operator in {'&&', '||', ',', '->'}:
        for operand in formula.operands:
            if operand.operator in {'G', 'F'} and operand.operands[0].operator not in {'P', '!'}:
                operand.identifier = counter
                counter += 1
            elif operand.operator in {'U', 'R'} and (
                    operand.operands[0].operator not in {'P', '!'} or operand.operands[1].operator not in {'P', '!'}):
                operand.identifier = counter
                counter += 1
    elif formula.operator in {'G', 'F', 'U', 'R'}:
        if formula.operator in {'G', 'F'} and formula.operands[0].operator not in {'P', '!'}:
            formula.identifier = counter
            counter += 1
        elif formula.operator in {'U', 'R'} and (
                formula.operands[0].operator not in {'P', '!'} or formula.operands[1].operator not in {'P', '!'}):
            formula.identifier = counter
            counter += 1
    return formula

# TODO Can we merge this with assign_identifier?
def assign_real_expr_id(node):
    id_counter = 0

    def do_assign(node):
        nonlocal id_counter
        if node.operator == 'P' and len(node.operands) > 1:
            node.real_expr_id = id_counter
            id_counter += 1
        elif node.operator != 'P':
            for operand in node.operands:
                do_assign(operand)

    do_assign(node)


def has_temporal_operator(node):
    '''
    :param node: Node containing a formula
    :return: True if the formula contains any temporal operator
    '''
    match node.operator:
        case 'G' | 'F' | 'U' | 'R':
            return True
        case '&&' | '||' | ',' | '!' | '->':
            return any(has_temporal_operator(operand) for operand in node)
    return False

def flagging(node):
    '''
    :param node:
    :return: True if the node contains any `problematic` operators
    '''
    match node.operator:
        case ',' | '&&' | '||' | '!' | '->':
            return any(flagging(operand) for operand in node)
        case 'O':
            match node[0].operator:
                case 'G' | 'U':
                    return has_temporal_operator(node[0][0])
                case 'R':
                    return has_temporal_operator(node[0][1])
            return False
    return False

def formula_to_string(formula):
    """
    :param formula:
    :return: trasforma la lista in una stringa per utilizzarla nell'etichetta del nodo del grafo e stamparla
    """
    if isinstance(formula, list) and len(formula) == 1 and isinstance(formula[0], list):  # se ho [[formula]]
        formula = formula[0]

    if isinstance(formula, list) and len(formula) == 1 and isinstance(formula[0],
                                                                      str):  # serve per formule del tipo ['p']
        return formula[0]

    if isinstance(formula, str):  # probabilemente non serve
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

    elif operator == '->':
        _, arg1, arg2 = formula
        return f"({formula_to_string(arg1)}) -> ({formula_to_string(arg2)})"



def decompose(tableau_data, node, current_time):
    """
    :param node: nodo da decomporre che ha operatore ','
    :param current_time: istante di tempo attuale, per capire quali operatori sono attivi e quali no
    :return: ritorna la lista decomposta (i.e. il successivo nodo del tree)
    """
    assert node.operator == ','
    counter = 0
    for j in range(len(node.operands)):
        if node.operands[j].operator in {'&&', ','}:
            return decompose_and(node)
        elif node.operands[j].operator == '||':
            return decompose_or(node, j)
        elif node.operands[j].operator == 'G' and node.operands[j].lower == current_time:
            return decompose_all_G_nodes(node, current_time)
        elif node.operands[j].operator == 'F' and node.operands[j].lower == current_time:
            return decompose_F(node, j)
        elif node.operands[j].operator == 'U' and node.operands[j].lower == current_time:
            node = copy.deepcopy(node)
            return decompose_U(node.operands[j].to_list(), node, j)
        elif node.operands[j].operator == 'R' and node.operands[j].lower == current_time:
            node = copy.deepcopy(node)
            return decompose_R(node.operands[j].to_list(), node, j)
        elif node.operands[j].operator == '->':
            if tableau_data.mode == 'complete' or tableau_data.mode == 'sat':
                return decompose_imply_classic(node, j)
            else:
                node = copy.deepcopy(node)
                return decompose_imply_new(node, j)
        else:  # se arrivo qui vuol dire che non sono entrata in nessun return e quindi non c'era nulla da decomporre
            # perché l'elemento era già decomposto o non ancora attivo
            counter += 1

    if counter == len(node.operands):
        # fai qui il check accept/reject, se rigetti non serve nemmeno fare il jump
        if local_consistency_check(tableau_data, node):
            res = decompose_jump(node)
            if res:
                res[0].current_time = node.current_time
            return res
        else:
            return ['Rejected']

    return None


def decompose_all_G_nodes(outer_node, current_time):
    """
    Decompone tutti i nodi G nella formula con lower bound uguale a current_time.
    """
    assert outer_node.operator == ','
    # Funzione interna ricorsiva per modificare l'argomento
    def modify_argument(arg, G_node, identifier, short):
        if arg.operator == 'P':
            ret = arg.shallow_copy()
            ret.execution_time = current_time #in realtà nel G non serve perché rimane il OG, però potrebbe forse servire quando OG si cancella perche lb=ub
            return ret
        elif arg.operator == '!':
            if arg.operands[0].operator == 'P':
                ret = arg.shallow_copy()
                ret.operands[0] = arg.operands[0].shallow_copy()
                ret.operands[0].execution_time = current_time
                return ret
            return arg
        elif arg.operator in {'U', 'R', 'F'} or (arg.operator in {'G', 'F'} and G_node.lower == G_node.initial_time) or (arg.operator in {'G', 'F'} and not short):
            # Modifica bounds sommando quelli del nodo G
            extract = copy.deepcopy(arg) # TODO modify add_G_for_U so that we don't need a deep copy
            extract.lower = arg.lower + lower_bound
            extract.upper = arg.upper + lower_bound
            extract.is_derived = True
            extract.identifier = identifier
            if arg.operator in {'U', 'R'}:
                extract = add_G_for_U(extract, extract.operator, True)
            return extract
        elif short and arg.operator == 'G' and G_node.lower > G_node.initial_time: #non aggiungo un altro G, ma allungo intervallo di quello già esistente
            G_counter = 0
            for i, operand in enumerate(outer_node.operands):
                if operand.operator == 'G' and operand.is_derived and operand.identifier == G_node.identifier and operand.and_element == arg.and_element:
                    outer_node.operands[i] = operand.shallow_copy()
                    outer_node.operands[i].upper += 1
                    G_counter += 1
                    if G_node.lower == G_node.upper:
                        outer_node.operands[i].is_derived = False
                elif operand.operator == 'O' and operand.operands[0].operator == 'G' and operand.operands[0].is_derived and operand.operands[0].identifier == G_node.identifier and operand.operands[0].and_element == arg.and_element:
                    operand.operands[0] = operand.operands[0].shallow_copy()
                    operand.operands[0].upper += 1
                    G_counter += 1
                    if G_node.lower == G_node.upper:
                        operand.operands[0].is_derived = False
            if G_counter == 0:
                extract = arg.shallow_copy()
                extract.lower = arg.lower + lower_bound
                extract.upper = arg.upper + lower_bound
                extract.is_derived = True
                extract.identifier = identifier
                return extract
            else:
                return None # non ritorno niente perché è bastato modificare il nodo esistente
        elif arg.operator in {'&&', ','}:
            # Applica la modifica ricorsivamente agli operandi
            arg = arg.shallow_copy()
            new_operands = (modify_argument(op, G_node, identifier, True) for op in arg.operands)
            arg.operands = [x for x in new_operands if x is not None]
            if arg.operands:
                return arg
            else:
                return None
        elif arg.operator in {'||', '->'}:
            arg = arg.shallow_copy()
            new_operands = (modify_argument(op, G_node, identifier, False) for op in arg.operands)
            arg.operands = [x for x in new_operands if x is not None]
            return arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

    outer_node = outer_node.shallow_copy()
    G_nodes = []
    for i, operand in enumerate(outer_node.operands):
        if operand.operator == 'G' and operand.lower == current_time:
            G_nodes.append(operand)
            if operand.lower < operand.upper:
                # Sostituisco con ['O', ['G', 'a', 'b', ['p']]]
                outer_node.operands[i] = Node('O', operand)
            else:
                # Elimino l'elemento se a == b
                outer_node.operands[i] = None
    outer_node.operands = [x for x in outer_node.operands if x is not None]

    for G_node in G_nodes:
        lower_bound = G_node.lower
        identifier = G_node.identifier
        #initial_time = node.initial_time
        # a volte se il G annidato viene dalla dec di un altro op annidato diverso da G (tipo F), non ha l'initial time settato
        if G_node.operator == 'G' and G_node.operands[0].operator not in {'P', '!'} and G_node.initial_time == '-1':
            set_initial_time(G_node)
        # Decomponi il nodo originale
        new_operands = modify_argument(G_node.operands[0], G_node, identifier, True)
        if new_operands:
            outer_node.operands.append(new_operands)
    return [outer_node]


def decompose_F(node, index):
    assert index >= 0 and node is not None

    F_formula = node[index]
    lower_bound = F_formula.lower
    current_time = F_formula.current_time

    # Funzione interna ricorsiva per modificare l'argomento
    def modify_argument(arg):
        if arg.operator == 'P':
            ret = arg.shallow_copy()
            ret.execution_time = current_time
            return ret
        elif arg.operator in {'!'}:
            if arg.operands[0].operator in {'P'}:
                ret = arg.shallow_copy()
                ret.operands[0] = arg.operands[0].shallow_copy()
                ret.operands[0].execution_time = current_time
                return ret
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modifica bounds sommando quelli del nodo G
            extract = copy.deepcopy(arg) # TODO modify add_G_for_U so that we don't need a deep copy
            extract.lower = arg.lower + lower_bound
            extract.upper = arg.upper + lower_bound
            extract.current_time = current_time
            if arg.operator in {'U', 'R'}:
                extract = add_G_for_U(extract, extract.operator, True)
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Applica la modifica ricorsivamente agli operandi
            new_arg = arg.shallow_copy()
            new_arg.operands = [modify_argument(op) for op in arg.operands]
            return new_arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

    # Node where we postpone satisfaction of F
    new_node1 = node.shallow_copy()
    new_node1.replace_operand(index, Node('O', F_formula))

    # Node where the operand holds
    new_node2 = node.shallow_copy()
    new_node2.replace_operand(index, modify_argument(F_formula.operands[0]))

    return new_node2, new_node1 #conviene fare prima return del node_2



def decompose_U(node, formula, index):
    '''
    Potrei decomporlo dicende che all'istante 2 può succedere p o q, se succede q il req è già soddisfatto e non mi interessa
    più cosa succede dopo (posso eliminare U da quel ramo. Mentre se succede p dovrò riportare che voglio avere pU[3,5]q all'ora all'istante successivo può succedere di nuovo p,
    oppure può succedere q e così via fino a 5, se a 5 è sempre successo p e mai q elimino il ramo perché U non è soddisfatto
    :return:
    NB: nel ramo dove faccio q se P ha operator = 'P' devo aggiungere execution_time
    '''
    assert index >= 0 and formula is not None

    if node[3][0] in {'G', 'F', 'U', 'R'}:  # caso nested
        new_node = copy.deepcopy(node[3])
        new_node[1] = new_node[1] + node[1]
        new_node[2] = new_node[2] + node[1]
        node_1 = Node(*[',', ['O', node], new_node])
        node_1.operands[1].is_derived = True
        if node[3][0] in {'U', 'R'}:
            node_1 = add_G_for_U(node_1, ',', True)
        if index < 0:
            node_1.operands[0].operands[0].initial_time = formula.initial_time
            node_1.operands[0].operands[0].identifier = formula.identifier
            node_1.operands[1].identifier = formula.identifier
        else:
            node_1.operands[0].operands[0].initial_time = formula.operands[index].initial_time
            node_1.operands[0].operands[0].identifier = formula.operands[index].identifier
            node_1.operands[1].identifier = formula.operands[index].identifier
    else:
        node_1 = Node(*[',', ['O', node], node[3]])
    if node[4][0] in {'G', 'F', 'U',
                      'R'}:  # caso nested, in questo caso il salto non crea problemi, non mi serve initial time
        new_node2 = copy.deepcopy(node[4])
        new_node2[1] = new_node2[1] + node[1]
        new_node2[2] = new_node2[2] + node[1]
        node_2 = Node(*new_node2)
        node_2_2 = Node(*[',', new_node2])
        if node[4][0] in {'U', 'R'}:
            node_2 = add_G_for_U(node_2, node[4][0], False)
            node_2_2 = add_G_for_U(node_2_2, ',', False)
    else:
        node_2 = Node(*node[4])
        node_2_2 = Node(*[',', node[4]])  # perché poi quando faccio extend lo faccio con gli operands e tolgo ','

    formula_1 = copy.deepcopy(formula)
    formula_2 = copy.deepcopy(formula)
    del formula_1.operands[index]  # tolgo U dalla formula di partenza
    del formula_2.operands[index]
    formula_1.operands.extend(
        node_1.operands)  # sdoppio la formula di partenza (senza U) e aggiungo a una un pezzo e all'altra l'altro
    for operand in formula_2.operands:
        if operand.identifier == formula.operands[index].identifier:
            operand.is_derived = False  # nel ramo in or non non voglio che siano su is_derived, perché poi crea problemi nell'estrarre i bound
    formula_2.operands.extend(node_2_2.operands)
    return [formula_2, formula_1]


def decompose_R(node, formula, index):
    '''
    NB: questo fa SOLO da a in poi, per la parte prima di a aggiungo un G nel pre-processing
    p R[a,b] q
    q always holds in [a, b], but if p holds in a position t'' before b, then q holds from a to t''
    Quindi se p succede prima di a, allora q non è mai vero: quindi tra 0 e a ho che se succede p, allora non avrò mai q
    quindi se succede p, puoi cancellare il R dalla formula: quindi tra 0 a a ho p OR (pR[a,b]q)
    tra a e b ho q and O(pRq) OR p
NB: nel ramo dove faccio p se P ha operator = 'P' devo aggiungere execution_time
    :param formula:
    :param index:
    :return:
    '''
    assert index >= 0 and formula is not None
    # p R[a,b] q diventa:
    # (q and O(pRq)) OR p
    formula_1 = copy.deepcopy(formula)
    formula_2 = copy.deepcopy(formula)
    del formula_1.operands[index]  # tolgo U dalla formula di partenza
    del formula_2.operands[index]
    if node[3][0] not in {'G', 'F', 'U', 'R'}:
        node_1 = Node(*[',', node[3]])
    else:
        node_1 = copy.deepcopy(node[3])
        node_1[1] = node_1[1] + node[1]
        node_1[2] = node_1[2] + node[1]
        node_1 = Node(*node[1])
        if node[3][0] in {'U', 'R'}:
            node_1 = add_G_for_U(node_1, node[3][0], False)
    if node[1] == node[2]:  # se sono all'ultimo istante non ho O
        if node[4][0] not in {'G', 'F', 'U', 'R'}:
            node_2 = Node(*[',', node[4]])
        else:
            new_node = copy.deepcopy(node[4])
            new_node[1] = new_node[1] + node[1]
            new_node[2] = new_node[2] + node[1]
            node_2 = Node(*[',', new_node])
            if node[4][0] in {'U', 'R'}:
                node_2 = add_G_for_U(node_2, ',', False)
    else:
        if node[4][0] not in {'G', 'F', 'U', 'R'}:
            node_2 = Node(*[',', ['O', node], node[4]])
        else:
            new_node = copy.deepcopy(node[4])
            new_node[1] = new_node[1] + node[1]
            new_node[2] = new_node[2] + node[1]
            node_2 = Node(*[',', ['O', node], new_node])
            if node[4][0] in {'U', 'R'}:
                node_2 = add_G_for_U(node_2, ',', True)
    if len(node_2.operands) >= 2:  # se ho O(R...)
        node_2.operands[1].is_derived = True
        node_2.operands[1].identifier = formula.operands[index].identifier
        node_2.operands[0].operands[0].initial_time = formula.operands[index].initial_time
        node_2.operands[0].operands[0].identifier = formula.operands[index].identifier
    else:  # caso in cui sono a R[b,b], togli is_derived dagli operatori derivati da R
        for operand in formula_2.operands:  # tolgo solo da qui perché formula_1 non ha is_derived essendo in OR con R
            if operand.identifier == formula.operands[index].identifier:
                operand.is_derived = False
    formula_1.operands.extend(node_1.operands)
    formula_2.operands.extend(node_2.operands)
    return formula_1, formula_2


def decompose_and(node):
    assert node.operator == ','
    new_node = node.shallow_copy()
    # We decomose all AND operators, but only at the first level
    for i, operand in enumerate(node.operands):
        if operand.operator in {'&&', ','}:
            new_node.replace_operand(i, *operand.operands)

    return [new_node]


def decompose_or(node, index):
    assert index >= 0 and node is not None
    # Funzione di ordinamento basata sulla complessità
    def complexity_score(node):
        """Calcola un punteggio di complessità per ordinare i nodi, penalizzando gli annidamenti temporali."""
        # 1. Operatori con solo 'P' → Migliori
        if node.operator in {'P', '!'}:
            return 0
        if node.operator in {'&&', ','} and all(op.operator == 'P' for op in node.operands):
            return 1
        if node.operator == '->' and all(op.operator == 'P' for op in node.operands):
            return 2
        if node.operator == '||' and all(op.operator == 'P' for op in node.operands):
            return 3

        # 2. Operatori temporali senza annidamenti complessi
        if node.operator in {'G', 'F', 'U', 'R'}:
            # Penalizzo in base all'orizzonte temporale
            score = 10 + (node.upper - node.lower)

            # Penalizzazione extra se l'operando è un altro temporale
            if node.operator == 'G' and node.operands[0].operator in {'G', 'F', 'U', 'R'}:
                score += 20  # G annidato → peggior caso
            elif node.operator == 'U' and node.operands[0].operator in {'G', 'F', 'U', 'R'}:
                score += 15  # U con temporale nel primo operand → peggio
            elif node.operator == 'R' and node.operands[1].operator in {'G', 'F', 'U', 'R'}:
                score += 15  # R con temporale nel secondo operand → peggio

            return score

        # 3. Operatori logici misti (nessun solo P)
        if node.operator == '->':
            return 30 + len(node.operands)
        elif node.operator == '&&':
            return 40 + len(node.operands)
        elif node.operator == '||':
            return 50 + len(node.operands)
        elif node.operator == ',':
            return 60 + len(node.operands)
        
        raise ValueError(f"Operatore non gestito: {node.operator}")

    # voglio creare un nodo figlio per ogni operand dell'OR, nodo che contiene l'operand dell'or + il resto del nodo padre (tolto l'or)
    res = []
    # Ordino i nodi secondo l’euristica
    for or_operand in sorted(node[index].operands, key=complexity_score):
        new_node = node.shallow_copy()
        if or_operand.is_derived and or_operand.or_element > -1:
            z = 0
            for element in new_node.operands:
                if element.operator == 'G' and element.identifier == or_operand.identifier and element.or_element == or_operand.or_element:
                    z += 1
                    element.upper = or_operand.upper
                elif element.operator == 'O' and element.operands[0].operator == 'G' and element.operands[0].is_derived and element.operands[0].identifier == or_operand.identifier and element.operands[0].or_element == or_operand.or_element:
                    z += 1
                    element.operands[0].upper = or_operand.upper
            if z == 0: #se il G non era ancora mai stato estratto
                new_node.replace_operand(index, or_operand)
            else:
                # We modified some exisiting G, so we don't need to add more formulas
                del new_node.operands[index]
        else:
            new_node.replace_operand(index, or_operand)
        res.append(new_node)
    return res


def decompose_imply_classic(node, index):
    '''
    :return: decompone p->q come not(p) OR (p and q), senza evitare il caso vacuously true
    '''
    assert index >= 0 and node is not None

    imply_formula = node[index]
    lhs = imply_formula.operands[0]
    rhs = imply_formula.operands[1]
    
    if lhs.id_implication == -1:
        lhs = lhs.shallow_copy() # Can we avoid these shallow copies?
        lhs.id_implication = 0
    if rhs.id_implication == -1:
        rhs = rhs.shallow_copy()
        rhs.id_implication = 1

    def merge_derived_g_nodes(imply_op, new_node):
        # Cerca nodi 'G' derivati nel nuovo nodo
        for i, operand in enumerate(new_node.operands):
            if operand.operator == 'G' and operand.identifier == imply_op.identifier and operand.is_derived and operand.id_implication == imply_op.id_implication:
                # We are modifying the existing G node, so we need to make a copy
                new_node.operands[i] = operand.shallow_copy()
                # TODO Investigate if this is correct
                new_node.operands[i].upper = operand.upper+1
                return None
        return imply_op

    # lhs of the implication
    new_node1 = node.shallow_copy()
    new_node1.replace_operand(index, push_negation(Node('!', lhs)))

    # rhs of the implication
    new_node2 = node.shallow_copy()
    new_lhs, new_rhs = lhs, rhs
    if lhs.operator == 'G' and lhs.is_derived:
        new_lhs = merge_derived_g_nodes(lhs, new_node2)
    if rhs.operator == 'G' and rhs.is_derived:
        new_rhs = merge_derived_g_nodes(rhs, new_node2)
    new_node2.replace_operand(index, *(x for x in [new_lhs, new_rhs] if x is not None))

    # euristica per ottimizzare, se nella formula ho già antecedente che deve essere vero
    # resituisco prima nodo in cui antecedente è vero, altrimenti il contrario
    if lhs.operator == 'P':
        for operand in node.operands:
            if lhs[0] == operand[0]:
                return new_node2, new_node1
    elif lhs.operator in {'&&', ',', '||'}:
        for operand in node.operands:
            for element in lhs.operands:
                if element[0] == operand[0]:
                    return new_node2, new_node1
    return new_node1, new_node2



def decompose_imply_new(node, index):
    '''
    :return: decompone p->q come not(p) OR (p and q). Se ci sono più -> in and, viene rigettato il nodo in cui tutti
    gli antecedenti sono negati. Se c'è un solo -> viene rigettato il nodo con antecedente negato
    NB: non so se qui si può introdurre la semplificazione per creare meno elementi (verifica che satisfied implications venga comnque correttamente aggiornato)
    '''

    imply_formula = node[index]
    lhs = imply_formula.operands[0]  # antecedente
    rhs = imply_formula.operands[1]  # conseguente

    assert index >= 0 and node is not None
    if len(node.operands) > 1:
        if node.implications is None:  # non so perché a volte sia None, in attesa di trovare il problema uso questa soluzione
            node = count_implications(node)
        new_node2 = node.shallow_copy()
        new_node2.replace_operand(index, lhs, rhs)
        new_node2.satisfied_implications.append(node.operands[index].identifier)
        new_node1 = node.shallow_copy()
        if node.implications > 1:  # quando sono a 1 significa che quello che sto negando ora è l'ultimo e quindi li ho negati tutti
            new_node1.replace_operand(index, push_negation(Node('!', lhs)))
            new_node1.implications -= 1  # decremento di 1 ogni volta che passo dal ramo che nega l'antecedente per poter sapere quando li ho negati tutti
            new_node1 = push_negation(new_node1)
        else:
            new_node1 = 'Rejected'
    else:  # se l'imply non è in and con nulla posso direttamente rigettare il ramo negato
        new_node1 = 'Rejected'
        new_node2 = Node(',')
        new_node2.operands = imply_formula.operands
    # qui conviene restituire prima il ramo in cui antecedente è vero, perché tanto finché non sono tutti veri almeno
    #una volta non posso interrompere l'esplorazione
    return new_node2, new_node1


def simplify_F(node):
    '''
    Simplify formula according to the rule
    F[a,b] p && F[c,d] p <-> F[c,d] p whenever c >= a && d <= b
    '''
    assert node.operator == ','
    remove_indices = []
    F_formulas = {}
    for i, formula in enumerate(node.operands):
        if formula.operator == 'F':
            operand = formula[0]
            if operand in F_formulas:
                for j, F_formula in F_formulas[operand]:
                    if F_formula.lower >= formula.lower and F_formula.upper <= formula.upper:
                        remove_indices.append(i)
                    elif formula.lower >= F_formula.lower and formula.upper <= F_formula.upper:
                        remove_indices.append(j)
                        # We could also remove (j, F_formula) from the set, but we would have to do it out of the loop
            else:
                F_formulas[operand] = {(i, formula)}
    for i in sorted(remove_indices, reverse=True):
        del node.operands[i]
    return node

def decompose_jump(node):
    '''
    Distingue casi problematici da non problematici

    NB nei casi PROBLEMATICI (flag = True) posso saltare a partire dal minimo tra range dell'operatore esterno
    e a+d (G[a,b]F[c,d]...) e salto fino al minimo successivo della formula completa (senza contare i bound degli op derivati dalla decomposizione dei nested).
    Se il minimo tra i 2 è l'op esterno in realta non devo fare nulla perché avanzo di 1 in 1 finche non sparisce il nesting, a quel punto la
    flag diventa False ed entro nell'altro caso.

    NB: NON CONTARE I BOUND DEGLI OPERATORI DERIVED DAI NESTED
    '''
    assert node.operator == ','
    flag = flagging(node)
    time_instants = extract_time_instants(node, flag)
    if not flag:  # non ci sono operatori probelmatici attivi
        '''
        new_node = Node(',')
        new_node.satisfied_implications = node.satisfied_implications #altrimenti perdi info
        for operand in node.operands:
            if operand.operator not in {'P', '!', 'O'}:
                new_node.operands.append(operand)
            elif operand.operator == 'O' and operand.operands[0].lower < operand.operands[0].upper:
                sub_formula = operand.operands[0].shallow_copy()
                # trovo il primo numero maggiore dell'istante corrente di tempo
                indice = bisect.bisect_right(time_instants, sub_formula.lower)
                sub_formula.lower = time_instants[indice]
                new_node.operands.append(sub_formula)
        if new_node.operands:
            if len(new_node.operands) > 1:
                simplify_F(new_node)
            return [new_node]
        else:
            return None
        '''
        #provo a fare togliendo dal nodo originale, invece di crearne uno nuovo
        new_operands = []
        for operand in node.operands:
            if operand.operator not in {'P', '!', 'O'}:
                new_operands.append(operand)
            elif operand.operator == 'O' and operand.operands[0].lower < operand.operands[0].upper:
                sub_formula = operand.operands[0].shallow_copy()
                # trovo il primo numero maggiore dell'istante corrente di tempo
                indice = bisect.bisect_right(time_instants, sub_formula.lower)
                sub_formula.lower = time_instants[indice]
                new_operands.append(sub_formula)
        node.operands = new_operands
        if node.operands:
            if len(node.operands) > 1:
                simplify_F(node)
            return [node]
        else:
            return None
    else:  # caso con operatori problematici, uso direttamente i nodi per non perdere info su is_derived e initial_time
        # We first compute the time jump
        jump = []
        for operand in node.operands:
            # Controllo prima gli operatori nested problematici perché il salto dipende da loro:
            # verifico se ho raggiunto la threshold per cui posso saltare, se l'ho raggiunta cacolo il salto,
            # se non l'ho raggiunta il salto è 1
            # una volta calcolato il salto per ogni operatore problematico, faccio il minimo
            # una volta stabilito il salto da effettuare faccio un altro ciclo negli operands e applico il salto ad ognuno
            # controllando se ogni operatore è derivato da un nested o no (perché saltano in modo diverso)
            if operand.operator == 'O' and operand.operands[0].lower <= operand.operands[0].upper and not operand.operands[0].is_derived:
                if operand.operands[0].operator in {'G', 'U'} and operand.operands[0].operands[0].operator in {'G', 'F', 'U', 'R'}:
                    # se operatore interno è esaurito
                    if operand.operands[0].lower >= operand.operands[0].initial_time + operand.operands[0].operands[0].upper:
                        indice = bisect.bisect_right(time_instants, operand.operands[0].lower)  # trovo il primo numero maggiore dell'istante corrente di tempo
                        jump.append(time_instants[indice] - operand.operands[0].lower)  # il jump che devo fare è l'istante in cui devo arrivare - quello corrente
                    else:  # se sono qui non posso saltare, devo andare avanti di 1 in 1
                        jump.append(1)
                elif operand.operands[0].operator in {'G', 'U'} and operand.operands[0].operands[0].operator in {'&&', '||', ',', '->'}:
                    max_upper = 0
                    # trovo il max tra gli upper bound degli op interni
                    nested = 0
                    for arg in operand.operands[0].operands[0].operands:
                        if arg.operator in {'G', 'F', 'U', 'R'}:
                            nested += 1
                        if arg.upper > max_upper:
                            max_upper = arg.upper
                    if nested > 0 and operand.operands[0].lower >= operand.operands[0].initial_time + max_upper:
                        indice = bisect.bisect_right(time_instants, operand.operands[0].lower)
                        jump.append(time_instants[indice] - operand.operands[0].lower)
                    else:
                        jump.append(1)
                elif operand.operands[0].operator == 'R' and operand.operands[0].operands[1].operator in {'G', 'F', 'U', 'R'}:
                    if operand.operands[0].lower >= operand.operands[0].initial_time + operand.operands[0].operands[1].upper:
                        indice = bisect.bisect_right(time_instants, operand.operands[0].lower)
                        jump.append(time_instants[indice] - operand.operands[0].lower)
                    else:
                        jump.append(1)
                elif operand.operands[0].operator == 'R' and operand.operands[0].operands[1].operator in {'&&', '||', ',', '->'}:
                    max_upper = 0
                    # trovo il max tra gli upper bound degli op interni
                    for arg in operand.operands[0].operands[1].operands:
                        if arg.upper > max_upper:
                            max_upper = arg.upper
                    if operand.operands[0].lower >= operand.operands[0].initial_time + max_upper:
                        indice = bisect.bisect_right(time_instants, operand.operands[0].lower)
                        jump.append(time_instants[indice] - operand.operands[0].lower)
                    else:
                        jump.append(1)
        jump = min(jump)
        # Now we build the new node after the jump
        new_node_operands = []
        for operand in node.operands:
            if operand.operator in {'F', 'G', 'U', 'R'} and (jump == 1 or not operand.is_derived):
                new_node_operands.append(operand)
            elif operand.operator == 'O' and operand.operands[0].lower < operand.operands[0].upper:
                if jump == 1:
                    sub_formula = operand.operands[0].shallow_copy() # argomento di 'O'
                    sub_formula.lower = sub_formula.lower + jump
                    new_node_operands.append(sub_formula)
                else:
                    if operand.operands[0].is_derived:  # per questi devo aggiungere jump ad entrambi gli estremi dell'intervallo
                        sub_formula = operand.operands[0].shallow_copy()
                        sub_formula.lower = sub_formula.lower + jump
                        sub_formula.upper = sub_formula.upper + jump
                        new_node_operands.append(sub_formula)
                    else:
                        sub_formula = operand.operands[0].shallow_copy()
                        sub_formula.lower = sub_formula.lower + jump
                        new_node_operands.append(sub_formula)

        new_node = node.shallow_copy()
        new_node.operands = new_node_operands
        if len(new_node.operands) > 1:
            simplify_F(new_node)
        return [new_node]

def real_expr_to_z3(z3_variables, expr):
    if isinstance(expr, str):
        if STLParser.is_float(expr):
            return float(expr)
        if expr not in z3_variables:
            z3_variables[expr] = z3.Real(expr)
        return z3_variables[expr]

    assert isinstance(expr, list) and len(expr) == 3
    lhs = real_expr_to_z3(z3_variables, expr[1])
    rhs = real_expr_to_z3(z3_variables, expr[2])
    match expr[0]:
        case '+':
            return lhs + rhs
        case '-':
            return lhs - rhs
    raise ValueError(f"Operatore non gestito: {expr[0]}")

def real_term_to_z3(z3_variables, node):
    if node.real_expr_id in z3_variables:
        return z3_variables[node.real_expr_id]

    comp, lhs, rhs = node.operands
    lhs = real_expr_to_z3(z3_variables, lhs)
    rhs = real_expr_to_z3(z3_variables, rhs)
    match comp:
        case '<':
            res = lhs < rhs
        case '<=':
            res = lhs <= rhs
        case '>':
            res = lhs > rhs
        case '>=':
            res = lhs >= rhs
        case '==':
            res = lhs == rhs
        case '!=':
            res = lhs != rhs
        case _:
            raise ValueError(f"Unknown operator: {comp}")
    
    if node.real_expr_id is not None:
        z3_variables[node.real_expr_id] = res
    return res

def local_consistency_check(tableau_data, node):
    '''
    :return: True if node is consistent, False otherwise
    '''
    constraints = []
    for operand in node.operands:
        if operand.operator == 'O' and operand[0].operator in {'F', 'U'} and operand[0].lower == operand[0].upper:
            return False
        if operand.operator == 'P':
            if operand[0] in {'<', '<=', '>', '>=', '==', '!='}:
                constraints.append(real_term_to_z3(tableau_data.z3_variables, operand))
                #solver.add(real_term_to_z3(tableau_data.z3_variables, operand))
            else: # Boolean variable
                prop = operand[0]
                if prop == 'B_false':
                    return False # we have false in the upper level of a node
                elif prop == 'B_true':
                    continue # if we have true in the upper level of a node we can just ignore it
                
                if prop not in tableau_data.z3_variables:
                    tableau_data.z3_variables[prop] = z3.Bool(prop)

                constraints.append(tableau_data.z3_variables[prop])
                #solver.add(tableau_data.z3_variables[prop])
        elif operand.operator == '!':
            if operand[0][0] in {'<', '<=', '>', '>=', '==', '!='}:
                #solver.add(z3.Not(real_term_to_z3(tableau_data.z3_variables, operand[0])))
                constraints.append(z3.Not(real_term_to_z3(tableau_data.z3_variables, operand[0])))
            else: # Boolean variable
                prop = operand[0][0]
                if prop == 'B_true':
                    return False # we have !true in the upper level of a node
                elif prop == 'B_false':
                    continue # if we have !false in the upper level of a node we can just ignore it
                
                if prop not in tableau_data.z3_variables:
                    tableau_data.z3_variables[prop] = z3.Bool(prop)

                #solver.add(z3.Not(tableau_data.z3_variables[prop]))
                constraints.append(z3.Not(tableau_data.z3_variables[prop]))

    solver = z3.Solver()
    solver.add(constraints)
    # Verifica se vincoli sono sat
    return solver.check() == z3.sat


def set_initial_time(formula):
    '''
    :return: Serve per il jump nei casi nested problematici (devo sapere qual era il lower bound iniziale
    del nested + esterno per sapere se posso saltare)
    '''
    if formula.operator in {'&&', '||', ',', '->'}:
        for operand in formula.operands:
            if operand.operator in {'G', 'U'} and operand.operands[0].operator not in {'P', '!'}:
                operand.initial_time = operand.lower
            elif operand.operator in {'R'} and operand.operands[1].operator not in {'P', '!'}:
                operand.initial_time = operand.lower
            elif operand.operator in {'&&', '||', ',', '->', '<->'}:
                return set_initial_time(operand)
    elif formula.operator in {'G', 'U'} and formula.operands[0].operator not in {'P', '!'}:
        formula.initial_time = formula.lower
    elif formula.operator in {'R'} and formula.operands[1].operator not in {'P', '!'}:
        formula.initial_time = formula.lower
    return formula


def add_G_for_U(node, single, derived):
    """
    NB: devo applicarlo non solo all'inizio, ma anche dopo (es se ho GU o FU o GR...)
    Cerca un operatore 'U' in un nodo e, se presente, aggiunge un nodo 'G' con scope [0, lower]
    avente come operando il primo argomento dell'operatore 'U' a pari livello.

    Invece per R sostituisce R con F[0,a] p OR (p R[a,b] q)

    :param node: Oggetto di tipo Node su cui effettuare la modifica.
    :return: Il nodo modificato

    NB: da sistemare!!! se U è interno ad un nested non bisogna aggiungere!!!
    """
    if single in {',', '&&', '||', '->'}:
        new_operands = []
        for operand in node.operands:
            if isinstance(operand, Node):
                # Se troviamo un nodo con operatore 'U', creiamo il nuovo nodo 'G'
                if operand.operator == 'U' and operand.lower != '0':
                    # Creiamo il nodo G con bounds [0, operand.lower] e primo operando di 'U'
                    new_G_node = Node('G', '0', operand.lower, operand.operands[0])
                    if derived:
                        new_G_node.is_derived = True
                    # Aggiungiamo sia l'operatore 'U' corrente sia il nuovo 'G' come figli del nodo
                    new_operands.append(operand)
                    new_operands.append(new_G_node)
                elif operand.operator == 'R' and operand.lower != '0':  # qui non serve is_derived perché F è in OR
                    new_G_node = Node(
                        *['||', ['F', '0', operand.lower, operand.operands[0].to_list()], operand.to_list()])
                    new_operands.append(new_G_node)
                elif operand.operator not in {'G', 'F', 'O'}:
                    # Se non è un nodo 'U', richiamiamo ricorsivamente la funzione
                    add_G_for_U(operand, ',', False)
                    new_operands.append(operand)
                else:
                    new_operands.append(operand)
            else:
                new_operands.append(operand)

        # Aggiorna gli operandi del nodo corrente con quelli modificati
        node.operands = new_operands
        return node
    elif single in {'U', 'R'}:  # nel caso in cui U e R escano dalla decomp di nested non sono mai qui
        if single == 'U' and node.lower != '0':
            new_G_node = Node(*['G', '0', node.lower, node.operands[0].to_list()])
            # Ritorna un nodo con ',' come operatore che include sia 'U' sia 'G'
            return Node(*[',', node.to_list(), new_G_node.to_list()])
        elif single == 'R' and node.lower != '0':
            new_G_node = Node(*['||', ['F', '0', node.lower, node.operands[0].to_list()], node.to_list()])
            return new_G_node
        else:
            return node
    else:
        return node


def count_implications(formula):
    counter = 1
    if formula.operator in {'&&', ','}:
        # Conta quante implicazioni ('->') ci sono tra gli operandi
        implication_count = sum(1 for operand in formula.operands if operand.operator == '->')
        # Aggiungi l'attributo 'implications' al nodo e assegna il conteggio
        formula.implications = implication_count
        for operand in formula.operands:
            if operand.operator == '->':
                operand.identifier = counter
                counter += 1
    else:
        # Se il nodo non è un '&&', esplora ricorsivamente i suoi operandi
        for operand in formula.operands:
            if isinstance(operand, Node):
                count_implications(operand)
    return formula


def assign_and_or_element(node):
    """
    Assegna l'attributo and_element numerato a ogni operando di un nodo G con operando &&
    """
    if not node.operands:
        return

    if node.operator == 'G' and node.operands[0].operator in {'&&'}:
        # Scorre i figli e assegna and_element
        for index, operand in enumerate(node.operands[0].operands):
            operand.and_element = index
    elif node.operator == 'G' and node.operands[0].operator in {'||'}:
        # Scorre i figli e assegna and_element
        for index, operand in enumerate(node.operands[0].operands):
            operand.or_element = index

    # Ricorsione su tutti gli operandi
    for operand in node.operands:
        if isinstance(operand, Node):
            assign_and_or_element(operand)


def add_tree_child(tableau_data, G, parent_label, child):
    tableau_data.counter += 1
    if isinstance(child, str):
        child_label = child + ' ' + str(tableau_data.counter)
    else:
        child.counter = tableau_data.counter
        child_label = child.to_label()
    G.add_node(child_label)
    G.add_edge(parent_label, child_label)

def add_rejected(tableau_data, node):
    # Note: checking if some other node implies this one seems not to be useful
    node.sort_operands()
    tableau_data.rejected_store.append(node)
    # We should use bisect.insort_left to keep the list sorted, but it seems to be slower for some benchmarks
    # bisect.insort_left(rejected_store, node, key=Node.get_imply_sort_key)

def check_rejected(tableau_data, node):
    node.sort_operands()
    i = bisect.bisect_left(tableau_data.rejected_store, node.get_imply_search_key(), key=Node.get_imply_search_key)
    for rejected in tableau_data.rejected_store[i:]:
        if node.implies_quick(rejected):
            if tableau_data.verbose:
                print('Rejecting', node.to_list(), ' because it implies rejected node ', rejected.to_list())
            return True
        if rejected.operator == node.operator == ',' and node.operands[-1].get_imply_search_key() < rejected.operands[0].get_imply_search_key():
            return False
    return False

def add_children(tableau_data, node, depth, last_spawned, max_depth, current_time):
    mode = tableau_data.mode

    if depth >= max_depth:
        return None

    if tableau_data.tree:
        node_label = node.to_label()

    current_time = node.current_time # extract_min_time(node_copy) should have been called by the parent
    assert current_time is None or isinstance(current_time, int)
    children = decompose(tableau_data, node, current_time)
    if children is None:
        if tableau_data.verbose:
            print('No more children in this branch')
        if mode in {'sat', 'complete'}:
            return True
        else: # mode == 'strong_sat':
            tableau_data.true_implications.update(node.satisfied_implications)
            if len(tableau_data.true_implications) == tableau_data.number_of_implications:
                return True
            else:
                return False
    if tableau_data.verbose:
        for child in children:
            if not isinstance(child, str):
                print(child.to_list())
            else:
                print(child)
    child_queue = []
    for child in children:
        if child != 'Rejected':
            set_min_time(child) # updates the node's current_time, called here once and for all
            if mode != 'sat' or child.current_time == current_time or not check_rejected(tableau_data, child):
                child_queue.append(child)
            elif tableau_data.tree and mode == 'sat':
                add_tree_child(tableau_data, tableau_data.tree, node_label, child)
                node_label = child.to_label()
                child = 'Rejected (memo)'
        if tableau_data.tree:
            add_tree_child(tableau_data, tableau_data.tree, node_label, child)
    
    if mode == 'complete':
        complete_result = False
    if tableau_data.parallel and mode == 'sat' and depth - last_spawned > 30 and len(child_queue) > 1: # add 'strong_sat'
        # print("spawning", node.to_list())
        # print("children: ", str([child.to_list() for child in child_queue]))

        pool = fs.ProcessPoolExecutor(max_workers=2)
        try:
            futures = [pool.submit(add_children, tableau_data, child, depth + 1, depth, max_depth, current_time) for child in child_queue]
            for fut in fs.as_completed(futures):
                if fut.result():
                    return True
        finally:
            # We wait for running subtask to finish, otherwise they remain hanging.
            # TODO maybe use Event to stop them asap
            pool.shutdown(wait=True, cancel_futures=True)
    else:
        for child in child_queue:
            if add_children(tableau_data, child, depth + 1, last_spawned, max_depth, current_time):
                if mode == 'complete':
                    complete_result = True
                else: # mode in {'sat', 'strong_sat'}
                    return True
            elif mode == 'sat' and child.current_time is not None and child.current_time > current_time:
                add_rejected(tableau_data, child)

    if mode in {'sat', 'strong_sat'}:
        return False
    else: # mode == 'complete'
        return complete_result

def build_decomposition_tree(tableau_data, root, max_depth):
    """
    : return:
        if mode in {'sat', 'complete'}:
            True if the tableau has an accepting branch rooted at node,
            False if the tableau has only rejected branches rooted at node,
            None if we reached max_dept without finding an accepting branch
        if mode == 'strong_sat':
            True if the tableau has an accepting branch rooted at node and all implications are satisfied,
            False if the tableau has only rejected branches rooted at node,
            None if we reached max_dept without finding an accepting branch
    """
    time = set_min_time(root)
    if tableau_data.build_tree:
        root.counter = tableau_data.counter
        tableau_data.tree.add_node(root.to_label())

    if tableau_data.verbose:
        print(root.to_list())

    res = add_children(tableau_data, root, 0, 0, max_depth, time)

    if res and tableau_data.mode in {'sat', 'strong_sat'} and tableau_data.verbose:
        print("The requirement set is consistent")
    elif not res and tableau_data.mode in {'sat', 'strong_sat'}:
        print("The requirement set is not consistent")
    if tableau_data.build_tree:
        return tableau_data.tree, res
    else:
        return res

class TableauData:

    def __init__(self, formula, mode, build_tree, parallel, verbose):
        self.true_implications = set()
        self.number_of_implications = formula.implications
        self.build_tree = build_tree
        self.mode = mode
        self.parallel = parallel
        self.verbose = verbose
        if build_tree:
            self.counter = 0
            self.tree = nx.DiGraph()
        else:
            self.tree = None
        if mode == 'sat':
            self.rejected_store = []
        self.z3_variables = {}


def plot_tree(G):
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=8, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()


def make_tableau(formula, max_depth, mode, build_tree, parallel, verbose):
    if formula.operator != ',':
        formula = Node(',', formula)

    formula = add_G_for_U(formula, formula.operator, False)
    assign_and_or_element(formula)
    formula = assign_identifier(formula)
    assign_real_expr_id(formula)
    formula = count_implications(formula)
    set_initial_time(formula)
    formula = push_negation(formula)
    # formula = normalize_bounds(formula)

    tableau_data = TableauData(formula, mode, build_tree, parallel, verbose)
    return build_decomposition_tree(tableau_data, formula, max_depth)


'''
CASI NON PROBLEMATICI:
FG
FF
FU (non problematico, ma ogni volta che estrai U dovresti aggiungere il G)
U con nesting nel secondo argument
R con nesting nel primo argument

CASI PROBLEMATICI:
GF
GG
GU
GR
U con nesting nel primo argument (F,G)
R con nesting nel secondo argument (F,G)


'''
