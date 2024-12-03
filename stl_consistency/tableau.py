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

# utente deve solo inserire in input la max_depth dell'albero

import re
import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import graphviz_layout
import copy
from z3 import *
from fractions import Fraction
from math import gcd, lcm
from functools import reduce
import bisect
from stl_consistency.node import Node


def push_negation(node):
    if node.operator == '!':
        operand = node[0]
        new_node = copy.copy(node)
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
            new_node.operator = operand[0].operator
            new_node.operands = operand[0].operands
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
        new_node = copy.copy(node)
        new_node.operands = [push_negation(op) for op in node.operands]
        return new_node


def extract_min_time(formula):
    '''

    :param formula:
    :return: estrae il min lower bound della formula per settare il current_time
    '''
    if formula.operator in {'P', '!'}:
        min_time = None
    elif formula.operator in {'G', 'F', 'U', 'R'}:
        min_time = Fraction(formula.lower)
    elif formula.operator in {'O'}:
        min_time = Fraction(formula.operands[0].lower)
    elif formula.operator in {'&&', '||', ',', '->'}:
        times = []
        for op in formula.operands:
            op_time = extract_min_time(op)
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
    Come fare per operatori annidati? Forse la funzione andrebbe richiamata ogni volta e non solo una, perché
    si generano nuovi elementi
    """
    if flag:
        time_instants = []
        if formula.operator not in {'P'}:
            for elem in formula:
                if elem.operator not in {'P'}:
                    if elem.operator in ['G', 'F', 'U',
                                         'R'] and not elem.is_derived:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                        time_instants.append(elem.lower)
                        time_instants.append(elem.upper)
                    elif elem.operator in ['O'] and not elem.operands[0].is_derived:
                        time_instants.append(elem.operands[0].lower)
                        time_instants.append(elem.operands[0].upper)
    else:
        time_instants = []
        if formula.operator not in {'P'}:
            for elem in formula:
                if elem.operator not in {'P'}:
                    if elem.operator in ['G', 'F', 'U',
                                         'R']:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                        time_instants.append(elem.lower)
                        time_instants.append(elem.upper)
                    elif elem.operator in ['O']:
                        time_instants.append(elem.operands[0].lower)
                        time_instants.append(elem.operands[0].upper)
    time_instants = [Fraction(x) for x in time_instants]
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



def flagging(formula):
    '''
    :param formula:
    :return: la formula controlla che non ci siano operatori nested problematici (GF, GG,until con nesting nel
    primo arg, release con nesting nel secondo arg
    '''
    if len(formula) == 1:
        formula = formula[0]
    if formula[0] == ',':
        for element in formula:
            if element[0] == 'O' and element[1][0] in {'G', 'U'}:
                if element[1][3][0] in {'G', 'F', 'U', 'R'}:
                    return True
                elif element[1][3][0] in {'&&', '||', '->', ','}:
                    for arg in element[3:]:
                        if arg[0] in {'G', 'F', 'U', 'R'}:
                            return True
            elif element[0] == 'O' and element[1][0] in {'R'}:
                if element[1][4][0] in {'G', 'F', 'U', 'R'}:
                    return True
                elif element[1][4][0] in {'&&', '||', '->', ','}:
                    for arg in element[3:]:
                        if arg[0] in {'G', 'F', 'U', 'R'}:
                            return True
    else:
        if formula[0] == 'O' and formula[1][0] in {'G', 'U'}:
            if formula[1][3][0] in {'G', 'F', 'U', 'R'}:
                return True
            elif formula[1][3][0] in {'&&', '||', '->', ','}:
                for arg in formula[1][3][1:]:
                    if arg[0] in {'G', 'F', 'U', 'R'}:
                        return True
        elif formula[0] == 'O' and formula[1][0] in {'R'}:
            if formula[1][4][0] in {'G', 'F', 'U', 'R'}:
                return True
            elif formula[1][4][0] in {'&&', '||', '->', ','}:
                for arg in formula[1][4][1:]:
                    if arg[0] in {'G', 'F', 'U', 'R'}:
                        return True
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

    elif operator == '->':  # Implication
        _, arg1, arg2 = formula
        return f"({formula_to_string(arg1)}) -> ({formula_to_string(arg2)})"


def decompose(node, current_time, mode):
    """
    :param node: lista da decomporre che ha la forma esplicitata sopra
    :param current_time: istante di tempo attuale, per capire quali operatori sono attivi e quali no
    :return: ritorna la lista decomposta (i.e. il successivo nodo del tree)
    """
    if node.operator != 'P':
        counter = 0
        if node.operator == '&&':
            return decompose_and(node, -1)
        elif node.operator == '||':
            return decompose_or(node, [], -1)
        elif node.operator == '->':
            if mode == 'complete' or mode == 'sat':
                return decompose_imply_classic(node.to_list(), node, -1)
            else:
                return decompose_imply_new(node.to_list(), node, -1)
        # Se il nodo iniziale ha solo un elemento (quindi non è un and o or di più sottoformule) lo decompongo con i 5 elif di seguito
        elif node.operator == 'G':
            return decompose_G(node, node, -1)
        elif node.operator == 'F':
            return decompose_F(node, node, -1)
        elif node.operator == 'U':
            return decompose_U(node.to_list(), node, -1)
        elif node.operator == 'R':
            return decompose_R(node.to_list(), node, -1)
        elif node[0] == '!':
            counter += 1
        # Jump
        elif node.operator == 'O':  # se c'è un solo elemento non servono altre condizioni
            res = smt_check(node.to_list())
            if res == 'Rejected':
                return [res]
            else:
                res = decompose_jump(node)
                res[0].current_time = node.current_time
                return res
        # Scrivo un nodo come una virgola (un and) di tutti gli elementi del nodo
        elif node.operator == ',':
            for j in range(len(node.operands)):
                if node.operands[j].operator == '&&':
                    return decompose_and(node, j)
                if node.operands[j].operator == '||':
                    return decompose_or(node.operands[j], node, j)
                elif node.operands[j].operator == '->':
                    if mode == 'complete' or mode == 'sat':
                        return decompose_imply_classic(node.operands[j].to_list(), node, j)
                    else:
                        return decompose_imply_new(node.operands[j].to_list(), node, j)
                elif node.operands[j].operator == 'G' and Fraction(node.operands[j].lower) == current_time:
                    return decompose_G(node.operands[j], node, j)
                elif node.operands[j].operator == 'F' and Fraction(node.operands[j].lower) == current_time:
                    return decompose_F(node.operands[j], node, j)
                elif node.operands[j].operator == 'U' and Fraction(node.operands[j].lower) == current_time:
                    return decompose_U(node.operands[j].to_list(), node, j)
                elif node.operands[j].operator == 'R' and Fraction(node.operands[j].lower) == current_time:
                    return decompose_R(node.operands[j].to_list(), node, j)
                else:  # se arrivo qui vuol dire che non sono entrata in nessun return e quindi non c'era nulla da decomporre
                    # perché l'elemento era già decomposto o non ancora attivo
                    counter += 1
        if counter == len(node.operands):
            # fai qui il check accept/reject, se rigetti non serve nemmeno fare il jump
            res = smt_check(node.to_list())
            if res == 'Rejected':
                return [res]
            else:
                res = decompose_jump(node)
                if res:
                    res[0].current_time = node.current_time
                return res

    return None  # forse non serve


def decompose_G(node, formula, index):
    """
    decompone G sia nei casi nested (aggiornando intervalli temporali degli operatori estratti) sia nei casi non nested
    """
    lower_bound = node.lower
    identifier = node.identifier
    initial_time = node.initial_time

    # Funzione interna ricorsiva per modificare l'argomento
    def modify_argument(arg, identifier):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modifica bounds sommando quelli del nodo G
            extract = copy.deepcopy(arg)
            extract.lower = str(int(arg.lower) + int(lower_bound))
            extract.upper = str(int(arg.upper) + int(lower_bound))
            extract.is_derived = True
            extract.identifier = identifier
            if arg.operator in {'U', 'R'}:
                extract = add_G_for_U(extract, extract.operator, True)
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Applica la modifica ricorsivamente agli operandi
            new_operands = [modify_argument(op, identifier) for op in arg.operands]
            arg.operands = new_operands
            return arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

    # Decomponi il nodo originale
    if index < 0:
        if node.lower == node.upper:  # se sono all'ultimo istante non metto il OG
            new_node = modify_argument(node.operands[0], identifier)
        else:
            new_node = Node(*[',', ['O', node.to_list()]])
            new_node.operands[0].operands[0].identifier = identifier
            new_node.operands[0].operands[0].initial_time = initial_time
            new_node.operands[0].operands[0].is_derived = node.is_derived
            new_operands = modify_argument(node.operands[0], identifier)
            new_node.operands.append(new_operands)
        new_node.current_time = node.current_time
        return [new_node]
    else:
        if node.lower == node.upper:
            new_node = Node(*[',', ['O', node.to_list()]]) #poi il O lo cancelli, qui serve per comodità
            new_operands = modify_argument(node.operands[0], identifier)
            new_node.operands.append(new_operands)
            del new_node.operands[0]
            for operand in new_node.operands[0].operands:
                if not isinstance(operand, str) and operand.operator in {'G', 'F', 'U', 'R'}: #caso &&, || etc?
                    operand.is_derived = False
        else:
            new_node = Node(*[',', ['O', node.to_list()]])
            new_node.operands[0].operands[0].is_derived = node.is_derived
            new_node.operands[0].operands[0].initial_time = initial_time
            new_node.operands[0].operands[0].identifier = identifier
            new_operands = modify_argument(node.operands[0], identifier)
            new_node.operands.append(new_operands)
        del formula.operands[index]
        formula.operands.extend(new_node.operands)
        return [formula]


def decompose_F(node, formula, index):
    lower_bound = node.lower
    current_time = node.current_time

    # Funzione interna ricorsiva per modificare l'argomento
    def modify_argument(arg):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modifica bounds sommando quelli del nodo G
            extract = copy.deepcopy(arg)
            extract.lower = str(int(arg.lower) + int(lower_bound))
            extract.upper = str(int(arg.upper) + int(lower_bound))
            extract.current_time = current_time
            if arg.operator in {'U', 'R'}:
                extract = add_G_for_U(extract, extract.operator, True)
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Applica la modifica ricorsivamente agli operandi
            new_operands = [modify_argument(op) for op in arg.operands]
            arg.operands = new_operands
            return arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

    if index >= 0:
        node_1 = Node(*[',', ['O', node.to_list()]])
        node_1.operands[0].operands[0].is_derived = node.is_derived
        new_operands = modify_argument(node.operands[0])
        node_2 = copy.deepcopy(node_1)
        node_2.operands.append(new_operands)
        del node_2.operands[0]
        del formula.operands[index]
        new_node1 = copy.deepcopy(formula)
        new_node2 = copy.deepcopy(formula)
        new_node1.operands.extend(node_1.operands)
        new_node2.operands.extend(node_2.operands)
    else:
        new_node1 = Node(*['O', node.to_list()])
        new_node1.operands[0].current_time = current_time  # serve??
        new_node2 = modify_argument(node.operands[0])
    return new_node1, new_node2


def decompose_U(node, formula, index):
    '''
    Potrei decomporlo dicende che all'istante 2 può succedere p o q, se succede q il req è già soddisfatto e non mi interessa
    più cosa succede dopo (posso eliminare U da quel ramo. Mentre se succede p dovrò riportare che voglio avere pU[3,5]q all'ora all'istante successivo può succedere di nuovo p,
    oppure può succedere q e così via fino a 5, se a 5 è sempre successo p e mai q elimino il ramo perché U non è soddisfatto
    :return:
    '''
    if node[3][0] in {'G', 'F', 'U', 'R'}:  # caso nested
        new_node = copy.deepcopy(node[3])
        new_node[1] = str(Fraction(new_node[1]) + Fraction(node[1]))
        new_node[2] = str(Fraction(new_node[2]) + Fraction(node[1]))
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
                      'R'}:  # caso nested, in questo caso il salto non crea probelmi, non mi serve initial time
        new_node2 = copy.deepcopy(node[4])
        new_node2[1] = str(Fraction(new_node2[1]) + Fraction(node[1]))
        new_node2[2] = str(Fraction(new_node2[2]) + Fraction(node[1]))
        node_2 = Node(*new_node2)
        node_2_2 = Node(*[',', new_node2])
        if node[4][0] in {'U', 'R'}:
            node_2 = add_G_for_U(node_2, node[4][0], False)
            node_2_2 = add_G_for_U(node_2_2, ',', False)
    else:
        node_2 = Node(*node[4])
        node_2_2 = Node(*[',', node[4]])  # perché poi quando faccio extend lo faccio con gli operands e tolgo ','
    if index >= 0:  # se U è una sottoformula (è in and con altre formule)
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
    else:  # se U è l'unica formula
        formula_1 = node_1
        formula_2 = node_2
    return [formula_1, formula_2]


def decompose_R(node, formula, index):
    '''
    NB: questo fa SOLO da a in poi, per la parte prima di a aggiungo un G nel pre-processing
    p R[a,b] q
    q always holds in [a, b], but if p holds in a position t'' before b, then q holds from a to t''
    Quindi se p succede prima di a, allora q non è mai vero: quindi tra 0 e a ho che se succede p, allora non avrò mai q
    quindi se succede p, puoi cancellare il R dalla formula: quindi tra 0 a a ho p OR (pR[a,b]q)
    tra a e b ho q and O(pRq) OR p

    :param formula:
    :param index:
    :return:
    '''
    if index == -1:  # ho solo l'operatore R
        if node[3][0] not in {'G', 'F', 'U', 'R'}:
            node_1 = Node(*node[3])
        else:
            node_1 = copy.deepcopy(node[3])
            node_1[1] = str(int(node_1[1]) + int(node[1]))
            node_1[2] = str(int(node_1[2]) + int(node[1]))
            node_1 = Node(*node_1)
            if node[3][0] in {'U', 'R'}:
                node_1 = add_G_for_U(node_1, node[3][0], False)
        if node[1] == node[2]:  # se sono all'ultimo istante non ho il O
            if node[4][0] not in {'G', 'F', 'U', 'R'}:
                node_2 = Node(*node[4])
            else:  # QUI potresti togliere is_derived da tutti gli altri operatori generati dal R
                new_node = copy.deepcopy(node[4])
                new_node[1] = str(int(new_node[1]) + int(node[1]))
                new_node[2] = str(int(new_node[2]) + int(node[1]))
                node_2 = Node(*new_node)
                if node[4][0] in {'U', 'R'}:
                    node_2 = add_G_for_U(node_2, node[4][0], False)
        else:
            if node[4][0] not in {'G', 'F', 'U', 'R'}:
                node_2 = Node(*[',', ['O', node], node[4]])
            else:
                new_node = copy.deepcopy(node[4])
                new_node[1] = str(int(new_node[1]) + int(node[1]))
                new_node[2] = str(int(new_node[2]) + int(node[1]))
                node_2 = Node(*[',', ['O', node], new_node])
            node_2.operands[0].operands[0].initial_time = formula.initial_time
            node_2.operands[0].operands[0].identifier = formula.identifier
            node_2.operands[1].is_derived = True
            node_2.operands[1].identifier = formula.identifier
            if node[4][0] in {'U', 'R'}:
                node_2 = add_G_for_U(node_2, ',', True)
        return node_1, node_2
    else:
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
            node_1[1] = str(int(node_1[1]) + int(node[1]))
            node_1[2] = str(int(node_1[2]) + int(node[1]))
            node_1 = Node(*node[1])
            if node[3][0] in {'U', 'R'}:
                node_1 = add_G_for_U(node_1, node[3][0], False)
        if node[1] == node[2]:  # se sono all'ultimo istante non ho O
            if node[4][0] not in {'G', 'F', 'U', 'R'}:
                node_2 = Node(*[',', node[4]])
            else:
                new_node = copy.deepcopy(node[4])
                new_node[1] = str(int(new_node[1]) + int(node[1]))
                new_node[2] = str(int(new_node[2]) + int(node[1]))
                node_2 = Node(*[',', new_node])
                if node[4][0] in {'U', 'R'}:
                    node_2 = add_G_for_U(node_2, ',', False)
        else:
            if node[4][0] not in {'G', 'F', 'U', 'R'}:
                node_2 = Node(*[',', ['O', node], node[4]])
            else:
                new_node = copy.deepcopy(node[4])
                new_node[1] = str(int(new_node[1]) + int(node[1]))
                new_node[2] = str(int(new_node[2]) + int(node[1]))
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


def decompose_and(node, index):
    if index == -1 and node.operator == '&&':
        node.operator = ','
        # Sostituisco ovunque
    else:
        for operand in node.operands:
            # if not isinstance(operand, str):
            # decompose_and(operand)
            if node.operator == ',' and operand.operator == '&&':
                del node.operands[index]
                for element in operand.operands:
                    node.operands.append(element)
    return [node]


def decompose_or(node, formula, index):
    if not formula:
        return node  # basta questo perché se lo restituisci senza parentesi ogni operand di || viene identificato come un nodo
    else:
        # voglio creare un nodo figlio per ogni operand dell'OR, nodo che contiene l'operand dell'or + il resto del nodo padre (tolto l'or)
        del formula.operands[index]
        res = []
        for or_operand in node.operands:
            new_node = copy.deepcopy(formula)
            new_node.operands.append(or_operand)
            res.append(new_node)
            del new_node
        return res

def decompose_imply_classic(node, formula, index):
    '''
    :return: decompone p->q come not(p) OR (p and q), senza evitare il caso vacuously true
    '''
    if index >= 0:
        node_2 = Node(*[',', node[1], node[2]])
        del formula.operands[index]
        new_node1 = copy.deepcopy(formula)
        new_node2 = copy.deepcopy(formula)
        new_node2.operands.extend(node_2.operands)
        node_1 = Node(*[',', ['!', node[1]]])
        new_node1.operands.extend(node_1.operands)
        new_node1 = push_negation(new_node1)
    else:  # se l'imply non è in and con nulla posso direttamente rigettare il ramo negato
        new_node1 = Node(*[',', ['!', node[1]]])
        new_node1 = push_negation(new_node1)
        new_node2 = Node(*[',', node[1], node[2]])
    return new_node1, new_node2


def decompose_imply_new(node, formula, index):
    '''
    :return: decompone p->q come not(p) OR (p and q). Se ci sono più -> in and, viene rigettato il nodo in cui tutti
    gli antecedenti sono negati. Se c'è un solo -> viene rigettato il nodo con antecedente negato
    MODIFICA: voglio che si comporti così solo in strong_sat, altrimenti voglio che non abbia rami rejected perché antecedente è falso
    '''
    if index >= 0:
        node_2 = Node(*[',', node[1], node[2]])
        new_node1 = copy.deepcopy(formula)
        new_node2 = copy.deepcopy(formula)
        del new_node1.operands[index]
        del new_node2.operands[index]
        new_node2.satisfied_implications.append(formula.operands[index].identifier)
        new_node2.operands.extend(node_2.operands)
        if formula.implications > 1:  # quando sono a 1 significa che quello che sto negando ora è l'ultimo e quindi li ho negati tutti
            node_1 = Node(*[',', ['!', node[1]]])
            new_node1.operands.extend(node_1.operands)
            new_node1.implications -= 1  # decremento di 1 ogni volta che passo dal ramo che nega l'antecedente per poter sapere quando li ho negati tutti
            new_node1 = push_negation(new_node1)
        else:
            new_node1 = 'Rejected'
    else:  # se l'imply non è in and con nulla posso direttamente rigettare il ramo negato
        new_node1 = 'Rejected'
        new_node2 = Node(*[',', node[1], node[2]])
    return new_node1, new_node2


def decompose_jump(node):
    '''
    Distingue casi problematici da non problematici

    NB nei casi PROBLEMATICI (flag = True) posso saltare a partire dal minimo tra range dell'operatore esterno
    e a+d (G[a,b]F[c,d]...) e salto fino al minimo successivo della formula completa (senza contare i bound degli op derivati dalla decomposizione dei nested).
    Se il minimo tra i 2 è l'op esterno in realta non devo fare nulla perché avanzo di 1 in 1 finche non sparisce il nesting, a quel punto la
    flag diventa False ed entro nell'altro caso.

    NB: NON CONTARE I BOUND DEGLI OPERATORI DERIVED DAI NESTED
    '''
    flag = flagging(node.to_list())
    time_instants = extract_time_instants(node, flag)
    # Caso in cui input sia della forma [',', [], [], ....] (un and di tante sottoformule)
    new_node = []
    if node.operator == '!':
        return None
    if node.operator == ',':
        new_node = [',']  # scrivo come lista e poi ritrasformo in node
        if not flag:  # non ci sono operatori probelmatici
            for operand in node.operands:
                if operand.operator in {'F', 'G', 'U', 'R'}:
                    new_node.extend([operand.to_list()])
                elif operand.operator in {'O'} and Fraction(operand.operands[0].lower) < Fraction(
                        operand.operands[0].upper):
                    sub_formula = copy.deepcopy(operand.operands[0].to_list())
                    indice = bisect.bisect_right(time_instants, Fraction(
                        sub_formula[1]))  # trovo il primo numero maggiore dell'istante corrente di tempo
                    sub_formula[1] = str(time_instants[indice])
                    new_node.extend([sub_formula])
            if len(new_node) == 2:  # se uno degli elementi iniziale è della forma OG[x,x],
                # cioè ha esaurito l'intervallo e viene eliminato, è possibile  che rimanga un solo elemento, ma preceduto dalla virgola anche se non dovrebbe
                return [Node(*new_node[1])]
            elif new_node != [',']:
                return [Node(*new_node)]
            else:
                return None
        else:  # caso con operatori problematici, uso direttamente i nodi per non perdere info su is_derived e initial_time
            jump = []
            for operand in node.operands:
                # Controllo prima gli operatori nested problematici perché il salto dipende da loro:
                # verifico se ho raggiunto la threshold per cui posso saltare, se l'ho raggiunta cacolo il salto,
                # se non l'ho raggiunta il salto è 1
                # una volta calcolato il salto per ogni operatore problematico, faccio il minimo
                # una volta stabilito il salto da effettuare faccio un altro ciclo negli operands e applico il salto ad ognuno
                # controllando se ogni operatore è derivato da un nested o no (perché saltano in modo diverso)
                if operand.operator in {'O'} and Fraction(operand.operands[0].lower) <= Fraction(
                        operand.operands[0].upper):
                    if operand.operands[0].operator in {'G', 'U'} and operand.operands[0].operands[0].operator in {'G', 'F', 'U', 'R'}:
                        # se operatore interno è esaurito
                        if Fraction(operand.operands[0].lower) >= Fraction(operand.operands[0].initial_time) + Fraction(operand.operands[0].operands[0].upper):
                            sub_formula = copy.deepcopy(operand.operands[0].to_list())
                            indice = bisect.bisect_right(time_instants, Fraction(sub_formula[1]))  # trovo il primo numero maggiore dell'istante corrente di tempo
                            jump.append(time_instants[indice] - Fraction(operand.operands[0].lower))  # il jump che devo fare è l'istante in cui devo arrivare- quello corrente
                        else:  # se sono qui non posso saltare, devo andare avanti di 1 in 1
                            jump.append(Fraction(1))
                    elif operand.operands[0].operator in {'G', 'U'} and operand.operands[0].operands[0].operator in {'&&', '||', ',', '->'}:
                        max_upper = 0
                        # trovo il max tra gli upper bound degli op interni
                        for arg in operand.operands[0].operands[0].operands:
                            if int(arg.upper) > max_upper:
                                max_upper = int(arg.upper)
                        if Fraction(operand.operands[0].lower) >= Fraction(operand.operands[0].initial_time) + Fraction(max_upper):
                            sub_formula = copy.deepcopy(operand.operands[0].to_list())
                            indice = bisect.bisect_right(time_instants, Fraction(sub_formula[1]))
                            jump.append(time_instants[indice] - Fraction(operand.operands[0].lower))
                        else:
                            jump.append(Fraction(1))
                    elif operand.operands[0].operator in {'R'} and operand.operands[0].operands[1].operator in {'G', 'F', 'U', 'R'}:
                        if Fraction(operand.operands[0].lower) >= Fraction(operand.operands[0].initial_time) + Fraction(operand.operands[0].operands[1].upper):
                            sub_formula = copy.deepcopy(operand.operands[0].to_list())
                            indice = bisect.bisect_right(time_instants, Fraction(sub_formula[1]))
                            jump.append(time_instants[indice] - Fraction(operand.operands[0].lower))
                        else:
                            jump.append(Fraction(1))
                    elif operand.operands[0].operator in {'R'} and operand.operands[0].operands[1].operator in {'&&', '||', ',', '->'}:
                        max_upper = 0
                        # trovo il max tra gli upper bound degli op interni
                        for arg in operand.operands[0].operands[1].operands:
                            if int(arg.upper) > max_upper:
                                max_upper = int(arg.upper)
                        if Fraction(operand.operands[0].lower) >= Fraction(operand.operands[0].initial_time) + Fraction(max_upper):
                            sub_formula = copy.deepcopy(operand.operands[0].to_list())
                            indice = bisect.bisect_right(time_instants, Fraction(sub_formula[1]))
                            jump.append(time_instants[indice] - Fraction(operand.operands[0].lower))
                        else:
                            jump.append(Fraction(1))
            jump = min(jump)
            for operand in node.operands:
                if operand.operator in {'F', 'G', 'U', 'R'} and (jump == Fraction(1) or not operand.is_derived):
                    new_node.extend([operand])
                elif operand.operator in {'O'} and Fraction(operand.operands[0].lower) < Fraction(
                        operand.operands[0].upper):
                    if jump == Fraction(1):
                        sub_formula = copy.deepcopy(
                            operand.operands[0])  # node[i][1] dovrebbe essere l'argomenti di 'O'
                        sub_formula.lower = str(Fraction(sub_formula.lower) + jump)
                        new_node.extend([sub_formula])
                    else:
                        if operand.operands[0].is_derived:  # per questi devo aggiungere jump ad entrambi gli estremi dell'intervallo
                            sub_formula = copy.deepcopy(operand.operands[0])
                            sub_formula.lower = str(Fraction(sub_formula.lower) + jump)
                            sub_formula.upper = str(Fraction(sub_formula.upper) + jump)
                            new_node.extend([sub_formula])
                        else:
                            sub_formula = copy.deepcopy(operand.operands[0])
                            sub_formula.lower = str(Fraction(sub_formula.lower) + jump)
                            new_node.extend([sub_formula])
        if new_node[0] == ',' and len(new_node) == 2:  # se uno degli elementi iniziale è della forma OG[x,x],
            # cioè ha esaurito l'intervallo e viene eliminato, è possibile  che rimanga un solo elemento, ma preceduto dalla virgola anche se non dovrebbe
            return [new_node[1]]
        else:
            node.operands = new_node[1:]
            return [node]
    else:  # ho una formula con un solo operatore (quindi un O)
        if not flag and Fraction(node.operands[0].lower) < Fraction(node.operands[0].upper):
            sub_formula = copy.deepcopy(
                node.operands[0].to_list())  # node.operands[0] dovrebbe essere l'argomenti di 'O'
            sub_formula[1] = sub_formula[
                2]  # se ho una formula con un solo elemento posso già saltare all'ultimo istante di tempo
            new_node.extend(sub_formula)
            return [Node(*new_node)]
        else:
            print('Error, invalid formula')
            return None


def smt_check(node):
    """
    :return: restituisce il nodo di partenza se è accepted,  'Rejected' se il nodo è rejected
    """
    new_node = []
    variabili_z3 = {}
    variabili = []
    vincoli = []
    for i in range(len(node)):
        if node[0] == ',':
            if node[i][0] == 'O' and node[i][1][0] in {'F', 'U'} and node[i][1][1] == node[i][1][2]:
                if node[i][1][0] in 'F':
                    print("Node is rejected because finally was never satisfied in this branch")
                else:
                    print("Node is rejected because until was never satisfied in this branch")
                return 'Rejected'
            if node[i][0] not in {'O', 'F', 'G', 'U', ',', 'R', '->'}:
                new_node.extend(node[i])
                if len(node[i]) == 1:
                    new_var = re.findall(r'\b[B|R]_[a-zA-Z]\w*\b', new_node[-1])
                else:
                    new_var = re.findall(r'\b[B|R]_[a-zA-Z]\w*\b', new_node[-1][0])
                variabili.extend(new_var)
        else:  # caso con un solo elemento (succede se ho un ramo con solo un finally)
            if node[0] == 'O' and node[i][0] in 'F' and node[1][1] == node[1][2]:
                print("Node is rejected because finally was never satisfied in this branch")
                return 'Rejected'
            if node[0] not in {'O', 'F', 'G', 'U', ',', 'R', '->'}:
                new_node.extend(node[i])
                new_var = re.findall(r'\b[B|R]_[a-zA-Z]\w*\b', new_node[-1])
                variabili.extend(new_var)
    for var in variabili:
        if var not in variabili_z3:
            if var[0] == 'B':
                var = var[2:]
                variabili_z3[var] = Bool(var)
            else:
                var = var[2:]
                variabili_z3[var] = Real(var)
    new_node = modify_node(new_node)  # tolgo B_ e R_ che non servono più
    for i in range(len(new_node)):
        if new_node[i] == '!':
            new_node[i + 1] = 'Not(' + new_node[i + 1][0] + ')'
        else:
            esp_z3 = new_node[i]
            for var in variabili_z3:  # inserire la variabile nel vincolo
                esp_z3 = re.sub(rf'\b{var}\b', f'variabili_z3["{var}"]', esp_z3)
            vincoli.append(eval(esp_z3))
    solver = Solver()
    # aggiungi vincoli al solver
    solver.add(vincoli)
    # Verifica se vincoli sono sat
    if solver.check() == sat:
        print("Node is accepted, expressions are consistent")
        return node
    else:
        print("Node is rejected, expressions are inconsistent")
        return 'Rejected'


def modify_node(node):
    '''
    :return: dopo aver definito le variabili per smt check, posso togliere B_ e R_ dalla formula per poi definire i
    vincoli
    '''

    def flatten(lst):
        flat_list = []
        for item in lst:
            if isinstance(item, list):
                flat_list.extend(flatten(item))  # Ricorsione per appiattire anche liste più profonde
            else:
                flat_list.append(item)
        return flat_list

    node = flatten(node)
    new_node = [re.sub(r'\b[B|R]_', '', expr) for expr in node]
    return new_node


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
    if formula.operator == '&&':
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


def build_decomposition_tree(root, max_depth, mode = 'complete'):
    G = nx.DiGraph()
    time = extract_min_time(root)
    counter = 0
    root_label = root.to_label(counter)
    G.add_node(root_label)
    print(root_label)

    def add_children(node, depth, current_time, mode):
        nonlocal counter
        global true_implications
        if depth < max_depth:
            node_copy = copy.deepcopy(node)
            current_time = extract_min_time(node_copy)
            node_label = node.to_label(counter)
            children = decompose(node_copy, current_time, mode)
            if children is None:
                print('No more children in this branch')
                if mode == 'sat':
                    return True
                elif mode == 'strong_sat':
                    true_implications.update(node.satisfied_implications)
                    if len(true_implications) == number_of_implications:
                        return True
                    else:
                        return False
            else:
                for child in children:
                    if not isinstance(child, str):
                        print(child.to_list())
                    else:
                        print(child)
            for child in children:
                if child == 'Rejected':
                    counter += 1
                    child_label = " ".join([child, str(counter)])
                    G.add_node(child_label)
                    G.add_edge(node_label, child_label)
                else:
                    counter += 1
                    # Compute child time for the label (for debugging)
                    child_time = extract_min_time(child)
                    child_time = current_time if child_time is None else child_time
                    child_label = child.to_label(counter)
                    G.add_node(child_label)
                    G.add_edge(node_label, child_label)
                    res = add_children(child, depth + 1, current_time, mode)
                    if res and mode in {'sat', 'strong_sat'}:
                        return True
        return False

    add_children(root, 0, time, mode)
    return G


def plot_tree(G):
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=8, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()


def make_tableau(formula, max_depth, mode='complete'):
    global number_of_implications
    formula = add_G_for_U(formula, formula.operator, False)
    formula = assign_identifier(formula)
    formula = count_implications(formula)
    number_of_implications = formula.implications
    set_initial_time(formula)

    # formula = normalize_bounds(formula)

    return build_decomposition_tree(formula, max_depth, mode)

true_implications = set()
number_of_implications = None
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