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
from node import Node


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
    else: # Any non-negated operator
        new_node = copy.copy(node)
        new_node.operands = [push_negation(op) for op in node.operands]
        return new_node

def extract_min_time(formula, node):
    """
    Estrae l'istante di tempo minimo da una formula STL, serve per sapere l'istante corrente
    durante la decomposizione

    """
    min_times = []
    if isinstance(formula, list):
        if len(formula) == 1:
            return extract_min_time(formula[0], node)
        if formula[0] == '!':
            return None
        if formula[0] in {'&&', '||', ',', '->'}:
            for i in range(1, len(formula)):
                if len(formula[i]) > 1 and formula[i][0] not in {'O', '!', '||', '->'}:
                    if formula[i][3][0] in {'G', 'F', 'U', 'R'}:  # caso nested, non O
                        min_time = str(Fraction(formula[i][1]))# + Fraction(formula[i][3][1])) #tolgo la somma perché decompongono subito
                        min_times.append(min_time)
                    elif formula[i][0] in {'U', 'R'} and formula[i][4][0] in {'G', 'F', 'U', 'R'}:  # caso nested U second arg
                        min_time = str(Fraction(formula[i][1]))
                        min_times.append(min_time)
                    else:  # caso non nested e non O
                        min_time = formula[i][1]
                        min_times.append(min_time)
                elif len(formula[i]) > 1 and formula[i][0] in {'O'}:
                    if formula[i][1][0] in {'G', 'F'} and formula[i][1][3][0] in {'G', 'F', 'U', 'R'}:  # caso nested,  O
                        min_time = str(Fraction(formula[i][1][1]))# + Fraction(formula[i][1][3][1]))
                        min_times.append(min_time)
                    elif formula[i][1][0] in {'U', 'R'} and formula[i][1][3][0] in {'G', 'F', 'U', 'R'}:
                        min_time = str(Fraction(formula[i][1][1]))
                        min_times.append(min_time)
                    elif formula[i][1][0] in {'U', 'R'} and formula[i][1][4][0] in {'G', 'F', 'U', 'R'}:  # O U con nesting in second arg
                        min_time = str(Fraction(formula[i][1][1]))
                        min_times.append(min_time)
                    else:  # caso non nested, O
                        min_time = formula[i][1][1]
                        min_times.append(min_time)
        elif formula[0] in {'G', 'F', 'U', 'R'}:  # formula ha un solo elemento
            if formula[3][0] not in {'G', 'F', 'U', 'R'}:  # caso non nested
                min_time = formula[1]
                min_times.append(min_time)
            elif formula[0] in {'U', 'R'} and formula[4][0] not in {'G', 'F', 'U', 'R'}:  # caso non nested until second arg
                min_time = formula[1]
                min_times.append(min_time)
            elif formula[0] in {'U', 'R'} and formula[4][0] in {'G', 'F', 'U', 'R'}:  # caso nested secondo arg
                min_time = str(Fraction(formula[1]))
                min_times.append(min_time)
            elif formula[0] in {'U', 'R'} and formula[3][0] in {'G', 'F', 'U', 'R'}:
                min_time = str(Fraction(formula[1]))
                min_times.append(min_time)
            else:  # tutti gli altri casi nested
                min_time = str(Fraction(formula[1]))# + Fraction(formula[3][1]))
                min_times.append(min_time)
        elif formula[0] in {'O'}:  # formula ha un solo elemento in O
            if formula[1][3][0] not in {'G', 'F', 'U', 'R'} or (
                    formula[1][0] in {'U', 'R'} and formula[1][4][0] not in {'G', 'F', 'U', 'R'}):
                min_time = formula[1][1]
                min_times.append(min_time)
            elif formula[1][0] in {'G', 'F'} and formula[1][3][0] in {'G', 'F', 'U', 'R'}:  # caso nested
                min_time = str(Fraction(formula[1][1]))# + Fraction(formula[1][3][1]))
                min_times.append(min_time)
            elif formula[1][0] in {'U', 'R'} and formula[1][3][0] in {'G', 'F', 'U', 'R'}:
                min_time = str(Fraction(formula[1][1]))
                min_times.append(min_time)
            elif formula[1][0] in {'U', 'R'} and formula[1][4][0] in {'G', 'F', 'U', 'R'}:
                min_time = str(Fraction(formula[1][1]))
                min_times.append(min_time)
    if min_times:
        node.current_time = Fraction(min(min_times))
        return Fraction(min(min_times))
    else:
        return None


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
                    if elem.operator in ['G', 'F', 'U', 'R'] and not elem.is_derived:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
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
                    if elem.operator in ['G', 'F', 'U', 'R']:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
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
            if operand.operator in {'G', 'F'} and operand.operands[0].operator in {'G', 'F', 'U', 'R'}:
                operand.identifier = counter
                counter += 1
            elif operand.operator in {'U', 'R'} and (operand.operands[0].operator in {'G', 'F', 'U', 'R'} or operand.operands[1].operator in {'G', 'F', 'U', 'R'}):
                operand.identifier = counter
                counter += 1
    elif formula.operator in {'G', 'F', 'U', 'R'}:
        if formula.operator in {'G', 'F'} and formula.operands[0].operator in {'G', 'F', 'U', 'R'}:
            formula.identifier = counter
            counter += 1
        elif formula.operator in {'U', 'R'} and (formula.operands[0].operator in {'G', 'F', 'U', 'R'} or formula.operands[1].operator in {'G', 'F', 'U', 'R'}):
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
            #if element[0] in {'G'} and element[3][0] in {'G', 'F'}: #se non sono ancora attivi non creano problemi
                #return True
            #elif element[0] in {'U', 'R'} and element[4][0] in {'G', 'F', 'U', 'R'}: #until/release ha 2 args, il nesting può anche essere nel secondo
                #return True
            if element[0] == 'O' and element[1][0] in {'G'} and element[1][3][0] in {'G', 'F', 'U', 'R'}:
                return True
            elif element[0] == 'O' and element[1][0] in {'R'} and element[1][4][0] in {'G', 'F', 'U', 'R'}:
                return True
            elif element[0] == 'O' and element[1][0] in {'U'} and element[1][3][0] in {'G', 'F', 'U', 'R'}:
                return True
    else:
        #if formula[0] in {'G', 'F', 'U', 'R'} and formula[3][0] in {'G', 'F', 'U', 'R'}:
            #return True
        #elif formula[0] in {'U', 'R'} and formula[4][0] in {'G', 'F', 'U', 'R'}:
            #return True
        if formula[0] == 'O' and formula[1][0] in {'G'} and formula[1][3][0] in {'G', 'F', 'U', 'R'}:
            return True
        elif formula[0] == 'O' and formula[1][0] in {'R'} and formula[1][4][0] in {'G', 'F', 'U', 'R'}:
            return True
        elif formula[0] == 'O' and formula[1][0] in {'U'} and formula[1][3][0] in {'G', 'F', 'U', 'R'}:
            return True
    return False


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

    elif operator == '->':  # Implication
        _, arg1, arg2 = formula
        return f"({formula_to_string(arg1)}) -> ({formula_to_string(arg2)})"

def decompose(node, current_time):
    """
    :param node: lista da decomporre che ha la forma esplicitata sopra
    :param current_time: istante di tempo attuale, per capire quali operatori sono attivi e quali no
    :return: ritorna la lista decomposta (i.e. il successivo nodo del tree)
    """
    if node.operator != 'P':
        counter = 0
        #if len(node) == 1:
            #return decompose(node[0], current_time)
        if node.operator == '&&':
            return decompose_and(node)
        elif node.operator == '||':
            return decompose_or(node, [], -1)
        elif node.operator == '->':
            return decompose_imply(node.to_list(), node, -1)
        # Se il nodo iniziale ha solo un elemento (quindi non è un and o or di più sottoformule) lo decompongo con i 5 elif di seguito
        elif node.operator == 'G' and node.operands[0].operator not in {'F', 'G', 'U', 'R'}:
            return decompose_G(node, [], -1)
        elif node.operator == 'F' and node.operands[0].operator not in {'F', 'G', 'U', 'R'}:
            return decompose_F(node.to_list(), [], -1)
        elif node.operator == 'U':
            return decompose_U(node.to_list(), node, -1)
        elif node.operator == 'R':
            return decompose_R(node.to_list(), node, -1)
        elif node[0] == '!':
            counter += 1
        # Caso nested
        elif node.operator in {'F', 'G'} and node.operands[0].operator in {'F', 'G', 'U', 'R'}:
            return decompose_nested(node.to_list(), node, -1)
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
                if node.operands[j].operator == '||':
                    return decompose_or(node.operands[j], node, j)
                elif node.operands[j].operator == '->':
                    return decompose_imply(node.operands[j].to_list(), node, j)
                elif node.operands[j].operator == 'G' and Fraction(node.operands[j].lower) == current_time and node.operands[j].operands[0].operator not in {'G', 'F', 'U'}:
                    return decompose_G(node.operands[j], node, j)
                elif node.operands[j].operator == 'F' and Fraction(node.operands[j].lower) == current_time and node.operands[j].operands[0].operator not in {'G', 'F', 'U'}:
                    return decompose_F(node.operands[j].to_list(), node, j)
                elif node.operands[j].operator == 'U' and Fraction(node.operands[j].lower) == current_time:
                    return decompose_U(node.operands[j].to_list(), node, j)
                elif node.operands[j].operator == 'R' and Fraction(node.operands[j].lower) == current_time:
                    return decompose_R(node.operands[j].to_list(), node, j)
                # Caso Nested:
                elif node.operands[j].operator in {'G', 'F'} and node.operands[j].operands[0].operator in {'G', 'F', 'U', 'R'} and Fraction(node.operands[j].lower) == current_time:  #+ Fraction(node.operands[j].operands[0].lower)
                    return decompose_nested(node.operands[j].to_list(), node, j)
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
    # index < 0 indica che la formula è unica (non fa già parte di un and) e quindi devo aggiungere ',' all'inizio
    if index < 0:
        if node.lower == node.upper: #se sono all'ultimo istante non metto il OG
            new_node = Node(*node.operands[0].to_list())
        else:
            new_node = Node(*[',', ['O', node.to_list()], node.operands[0].to_list()])
        new_node.current_time = node.current_time
        return [new_node]
    else:
        if node.lower == node.upper:
            new_node = Node(*[',', node.operands[0].to_list()])
        else:
            new_node = Node(*[',', ['O', node.to_list()], node.operands[0].to_list()]) #bisogna mettere la virgola, altrimenti Node() non funziona, poi la tolgo dopo
            new_node.operands[0].operands[0].is_derived = formula.operands[index].is_derived #non voglio perdere info su is_derived nella decomposizione
            new_node.operands[0].operands[0].identifier = formula.operands[index].identifier
        del formula.operands[index]
        formula.operands.extend(new_node.operands)
        return [formula]


def decompose_F(node, formula, index):
    if index >= 0:
        node_1 = [',', ['O', node]]
        node_2 = [',', node[3]]
        node_1 = Node(*node_1)
        node_1.operands[0].operands[0].is_derived = formula.operands[index].is_derived
        node_1.operands[0].operands[0].identifier = formula.operands[index].identifier
        node_2 = Node(*node_2)
        del formula.operands[index]
        new_node1 = copy.deepcopy(formula)
        new_node2 = copy.deepcopy(formula)
        new_node1.operands.extend(node_1.operands)
        new_node2.operands.extend(node_2.operands)
    else:
        new_node1 = Node(*['O', node])
        new_node2 = Node(*node[3])
    return new_node1, new_node2


def decompose_U(node, formula, index):
    '''
    Potrei decomporlo dicende che all'istante 2 può succedere p o q, se succede q il req è già soddisfatto e non mi interessa
    più cosa succede dopo (posso eliminare U da quel ramo. Mentre se succede p dovrò riportare che voglio avere pU[3,5]q all'ora all'istante successivo può succedere di nuovo p,
    oppure può succedere q e così via fino a 5, se a 5 è sempre successo p e mai q elimino il ramo perché U non è soddisfatto
    :return:
    '''
    if node[3][0] in {'G', 'F', 'U', 'R'}: #caso nested
        new_node = copy.deepcopy(node[3])
        new_node[1] = str(Fraction(new_node[1]) + Fraction(node[1]))
        new_node[2] = str(Fraction(new_node[2]) + Fraction(node[1]))
        node_1 = Node(*[',', ['O', node], new_node])
        node_1.operands[1].is_derived = True
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
    if node[4][0] in {'G', 'F', 'U', 'R'}: #caso nested, in questo caso il salto non crea probelmi, non mi serve initial time
        new_node2 = copy.deepcopy(node[4])
        new_node2[1] = str(Fraction(new_node2[1]) + Fraction(node[1]))
        new_node2[2] = str(Fraction(new_node2[2]) + Fraction(node[1]))
        node_2 = Node(*new_node2)
        node_2_2 = Node(*[',', new_node2])
    else:
        node_2 = Node(*node[4])
        node_2_2 = Node(*[',', node[4]]) #perché poi quando faccio extend lo faccio con gli operands e tolgo ','
    if index >= 0:  # se U è una sottoformula (è in and con altre formule)
        formula_1 = copy.deepcopy(formula)
        formula_2 = copy.deepcopy(formula)
        del formula_1.operands[index]  # tolgo U dalla formula di partenza
        del formula_2.operands[index]
        formula_1.operands.extend(
            node_1.operands)  # sdoppio la formula di partenza (senza U) e aggiungo a una un pezzo e all'altra l'altro
        for operand in formula_2.operands:
            if operand.identifier == formula.operands[index].identifier:
                operand.is_derived = False  #nel ramo in or non non voglio che siano su is_derived, perché poi crea problemi nell'estrarre i bound
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
    if index == -1: #ho solo l'operatore R
        if node[3][0] not in {'G', 'F', 'U', 'R'}:
            node_1 = Node(*node[3])
        else:
            node_1 = copy.deepcopy(node[3])
            node_1[1] = str(int(node_1[1]) + int(node[1]))
            node_1[2] = str(int(node_1[2]) + int(node[1]))
            node_1 = Node(*node[1])
        if node[1] == node[2]: #se sono all'ultimo istante non ho il O
            if node[4][0] not in {'G', 'F', 'U', 'R'}:
                node_2 = Node(*node[4])
            else: #QUI potresti togliere is_derived da tutti gli altri operatori generati dal R
                new_node = copy.deepcopy(node[4])
                new_node[1] = str(int(new_node[1]) + int(node[1]))
                new_node[2] = str(int(new_node[2]) + int(node[1]))
                node_2 = Node(*new_node)
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
        return node_1, node_2
    else:
            #p R[a,b] q diventa:
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
        if node[1] == node[2]: #se sono all'ultimo istante non ho O
            if node[4][0] not in {'G', 'F', 'U', 'R'}:
                node_2 = Node(*[',', node[4]])
            else:
                new_node = copy.deepcopy(node[4])
                new_node[1] = str(int(new_node[1]) + int(node[1]))
                new_node[2] = str(int(new_node[2]) + int(node[1]))
                node_2 = Node(*[',', new_node])
        else:
            if node[4][0] not in {'G', 'F', 'U', 'R'}:
                node_2 = Node(*[',', ['O', node], node[4]])
            else:
                new_node = copy.deepcopy(node[4])
                new_node[1] = str(int(new_node[1]) + int(node[1]))
                new_node[2] = str(int(new_node[2]) + int(node[1]))
                node_2 = Node(*[',', ['O', node], new_node])
        if len(node_2.operands) >= 2: #se ho OR
            node_2.operands[1].is_derived = True
            node_2.operands[1].identifier = formula.operands[index].identifier
            node_2.operands[0].operands[0].initial_time = formula.operands[index].initial_time
            node_2.operands[0].operands[0].identifier = formula.operands[index].identifier
        else: #caso in cui sono a R[b,b], togli is_derived dagli operatori derivati da R
            for operand in formula_2.operands: #tolgo solo da qui perché formula_1 non ha is_derived essendo in OR con R
                if operand.identifier == formula.operands[index].identifier:
                    operand.is_derived = False
        formula_1.operands.extend(node_1.operands)
        formula_2.operands.extend(node_2.operands)
    return formula_1, formula_2

def decompose_and(node):  # voglio che tolga TUTTI gli '&&' in una volta per fare prima
    if node.operator == '&&':
        node.operator = ','
        # Sostituisco ovunque
    for operand in node.operands:
        if not isinstance(operand, str):
            decompose_and(operand)
    return [node]


def decompose_or(node, formula, index):
    if not formula:
        return node #basta questo perché se lo restituisci senza parentesi ogni operand di || viene identificato come un nodo
    else:
        #voglio creare un nodo figlio per ogni operand dell'OR, nodo che contiene l'operand dell'or + il resto del nodo padre (tolto l'or)
        del formula.operands[index]
        res = []
        for or_operand in node.operands:
            new_node = copy.deepcopy(formula)
            new_node.operands.append(or_operand)
            res.append(new_node)
            del new_node
        return res

def decompose_imply(node, formula, index):
    '''
    :return: decompone p->q come not(p) OR (p and q). Se ci sono più -> in and, viene rigettato il nodo in cui tutti
    gli antecedenti sono negati. Se c'è un solo -> viene rigettato il nodo con antecedente negato
    '''
    if index >= 0:
        node_2 = Node(*[',', node[1], node[2]])
        del formula.operands[index]
        new_node1 = copy.deepcopy(formula)
        new_node2 = copy.deepcopy(formula)
        new_node2.operands.extend(node_2.operands)
        if formula.implications > 1: #quando sono a 1 significa che quello che sto negando ora è l'ultimo e quindi li ho negati tutti
            node_1 = Node(*[',', ['!', node[1]]])
            new_node1.operands.extend(node_1.operands)
            new_node1.implications -= 1 #decremento di 1 ogni volta che passo dal ramo che nega l'antecedente per poter sapere quando li ho negati tutti
            new_node1 = push_negation(new_node1)
        else:
            new_node1 = 'Rejected'
    else: #se l'imply non è in and con nulla posso direttamente rigettare il ramo negato
        new_node1 = 'Rejected'
        new_node2 = Node(*[',', node[1], node[2]])
    return new_node1, new_node2

def decompose_nested(node, formula, index):
    '''
    :return: decompone i nested che hanno come operatore esterno G o F
    '''
    # se la formula è unica (non un and di sottoformule), allora index==-1
    if index == -1: #node == formula
        if node[0] == 'G':
            extract = copy.deepcopy(node[3])
            extract[1] = str(Fraction(node[1]) + Fraction(
                extract[1]))  # quando estraggo l'op annidato devo modificare l'intervallo temporale
            extract[2] = str(Fraction(node[1]) + Fraction(extract[2]))
            if node[1] < node[2]:
                node = [',', ['O', node], extract]
                res = Node(*node)
                res.operands[1].is_derived = True
                res.operands[1].identifier = formula.identifier #operatore estratto eredita identifier
                res.operands[0].operands[0].initial_time = formula.initial_time
                res.operands[0].operands[0].identifier = formula.identifier #anche il G del OG lo eredita
                if formula.operands[0].operator in {'U', 'R'}:
                    res = add_G_for_U(res, ',', True)
            else:
                node = [extract]
                res = Node(*node)
            return [res]
        elif node[0] == 'F':
            extract = copy.deepcopy(node[3])
            extract[1] = str(Fraction(node[1]) + Fraction(extract[1]))
            extract[2] = str(Fraction(node[1]) + Fraction(extract[2]))
            res_1 = copy.deepcopy(node)
            res_1 = Node(*['O', res_1])
            res_2 = Node(*extract)
            res_1.current_time = formula.current_time
            res_1.operands[0].identifier = formula.identifier
            res_2.current_time = formula.current_time
            if node[3][0] in {'U', 'R'}:
                res_2 = add_G_for_U(res_2, node[3][0], False) #false perché è in OR quindi non serve is_derived
            return res_1, res_2
    else:
        if node[0] == 'G':
            res_1 = copy.deepcopy(formula)
            del res_1.operands[index]  # tolgo il nested dalla formula
            extract = copy.deepcopy(node[3])
            extract[1] = str(Fraction(node[1]) + Fraction(extract[1]))
            extract[2] = str(Fraction(node[1]) + Fraction(extract[2]))
            if node[1] < node[2]:
                node = Node(*[',', ['O', node], extract])
                node.operands[1].is_derived = True
                node.operands[1].identifier = formula.operands[index].identifier #elemento estratto eredita identifier
                node.operands[0].operands[0].initial_time = formula.operands[index].initial_time
                node.operands[0].operands[0].identifier = formula.operands[index].identifier #G di OG eredita identifier
                if formula.operands[index].operands[0].operator in {'U', 'R'}: #verifica che sia giusto
                    node = add_G_for_U(node, ',', True)
            else:
                node = Node(*[',', extract])
                for operand in res_1.operands: #visto che il G esterno è esaurito, togli is_derived dagli op che aveva prodotto
                    if operand.identifier == formula.operands[index].identifier:
                        operand.is_derived = False
                if extract[0] in {'U', 'R'}:
                    node = add_G_for_U(node, ',', False)
            res_1.operands.extend(node.operands)
            return [res_1]
        elif node[0] == 'F':
            res_1 = copy.deepcopy(formula)
            res_2 = copy.deepcopy(formula)
            del res_1.operands[index]
            del res_2.operands[index]
            extract = copy.deepcopy(node[3])
            extract[1] = str(Fraction(node[1]) + Fraction(extract[1]))
            extract[2] = str(Fraction(node[1]) + Fraction(extract[2]))
            extract = Node(*[',', extract])
            if node[3][0] in {'U', 'R'}:
                extract = add_G_for_U(extract, 'F', False)
            node = Node(*[',', ['O', node]])
            node.operands[0].operands[0].identifier = formula.operands[index].identifier
            res_1.operands.extend(node.operands)
            res_2.operands.extend(extract.operands)
            return res_1, res_2
    return


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
        new_node = [','] #scrivo come lista e poi ritrasformo in node
        if not flag: #non ci sono operatori probelmatici
            for operand in node.operands:
                if operand.operator in {'F', 'G', 'U', 'R'}:
                    new_node.extend([operand.to_list()])
                elif operand.operator in {'O'} and Fraction(operand.operands[0].lower) < Fraction(operand.operands[0].upper):
                    sub_formula = copy.deepcopy(operand.operands[0].to_list())
                    indice = bisect.bisect_right(time_instants, Fraction(sub_formula[1]))  # trovo il primo numero maggiore dell'istante corrente di tempo
                    sub_formula[1] = str(time_instants[indice])
                    new_node.extend([sub_formula])
            if len(new_node) == 2:  # se uno degli elementi iniziale è della forma OG[x,x],
                # cioè ha esaurito l'intervallo e viene eliminato, è possibile  che rimanga un solo elemento, ma preceduto dalla virgola anche se non dovrebbe
                return [Node(*new_node[1])]
            elif new_node != [',']:
                return [Node(*new_node)]
            else:
                return None
        else: #caso con operatori problematici, uso direttamente i nodi per non perdere info su is_derived e initial_time
            jump = []
            for operand in node.operands:
                #Controllo prima gli operatori nested problematici perché il salto dipende da loro:
                #verifico se ho raggiunto la threshold per cui posso saltare, se l'ho raggiunta cacolo il salto,
                #se non l'ho raggiunta il salto è 1
                #una volta calcolato il salto per ogni operatore problematico, faccio il minimo
                #una volta stabilito il salto da effettuare faccio un altro ciclo negli operands e applico il salto ad ognuno
                #controllando se ogni operatore è derivato da un nested o no (perché saltano in modo diverso)
                if operand.operator in {'O'} and Fraction(operand.operands[0].lower) <= Fraction(operand.operands[0].upper):
                    if operand.operands[0].operator in {'G', 'U'} and operand.operands[0].operands[0].operator in {'G', 'F', 'U', 'R'}:
                        if Fraction(operand.operands[0].lower) >= Fraction(operand.operands[0].initial_time) + Fraction(operand.operands[0].operands[0].upper): #se operatore interno è esaurito
                            sub_formula = copy.deepcopy(operand.operands[0].to_list())
                            #NB problema, in time_instants non dovrei includere quelli degli op che derivano dalla dec dei nested
                            indice = bisect.bisect_right(time_instants, Fraction(
                                sub_formula[1]))  # trovo il primo numero maggiore dell'istante corrente di tempo
                            jump.append(time_instants[indice] - Fraction(operand.operands[0].lower)) #il jump che devo fare è l'istante in cui devo arrivare- quello corrente
                        else: #se sono qui non posso saltare, devo andare avanti di 1 in 1
                            jump.append(Fraction(1))
                    elif operand.operands[0].operator in {'R'} and operand.operands[0].operands[1].operator in {'G', 'F', 'U','R'}:
                        if Fraction(operand.operands[0].lower) >= Fraction(operand.operands[0].initial_time) + Fraction(operand.operands[0].operands[1].upper): #VERIFICA INDICE upper
                            sub_formula = copy.deepcopy(operand.operands[0].to_list())
                            indice = bisect.bisect_right(time_instants, Fraction(
                                sub_formula[1]))  # trovo il primo numero maggiore dell'istante corrente di tempo
                            jump.append(time_instants[indice] - Fraction(operand.operands[0].lower))
                        else:
                            jump.append(Fraction(1))
            jump = min(jump)
            for operand in node.operands:
                if operand.operator in {'F', 'G', 'U', 'R'} and (jump == Fraction(1) or not operand.is_derived):
                    new_node.extend([operand])
                elif operand.operator in {'O'} and Fraction(operand.operands[0].lower) < Fraction(operand.operands[0].upper):
                    if jump == Fraction(1):
                        sub_formula = copy.deepcopy(operand.operands[0])  # node[i][1] dovrebbe essere l'argomenti di 'O'
                        sub_formula.lower = str(Fraction(sub_formula.lower) + jump)
                        new_node.extend([sub_formula])
                    else:
                        if operand.operands[0].is_derived == True: #per questi devo aggiungere jump ad entrambi gli estremi dell'intervallo
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
    else: #ho una formula con un solo operatore (quindi un O)
        if not flag and Fraction(node.operands[0].lower) < Fraction(node.operands[0].upper):
            sub_formula = copy.deepcopy(node.operands[0].to_list())  # node.operands[0] dovrebbe essere l'argomenti di 'O'
            sub_formula[1] = sub_formula[2]  # se ho una formula con un solo elemento posso già saltare all'ultimo istante di tempo
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
            for var in variabili_z3: #inserire la variabile nel vincolo
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
    if formula.operator in {'&&', '||', ',', '!', '->'}:
        for operand in formula.operands:
            if operand.operator in {'G'} and operand.operands[0].operator in {'F', 'G', 'U', 'R'}:
                operand.initial_time = operand.lower
            elif operand.operator in {'U'} and operand.operands[0].operator in {'F', 'G', 'U', 'R'}:
                operand.initial_time = operand.lower
            elif operand.operator in {'R'} and operand.operands[1].operator in {'F', 'G', 'U', 'R'}:
                operand.initial_time = operand.lower
    elif formula.operator in {'G'} and formula.operands[0].operator in {'F', 'G', 'U', 'R'}:
        formula.initial_time = formula.lower
    elif formula.operator in {'U'} and formula.operands[0].operator in {'F', 'G', 'U', 'R'}:
        formula.initial_time = formula.lower
    elif formula.operator in {'R'} and formula.operands[1].operator in {'F', 'G', 'U', 'R'}:
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
                elif operand.operator == 'R' and operand.lower != '0': #qui non serve is_derived perché F è in OR
                    new_G_node = Node(*['||', ['F', '0', operand.lower, operand.operands[0].to_list()], operand.to_list()])
                    new_operands.append(new_G_node)
                else:
                    # Se non è un nodo 'U', richiamiamo ricorsivamente la funzione
                    add_G_for_U(operand, ',', False)
                    new_operands.append(operand)
            else:
                new_operands.append(operand)

        # Aggiorna gli operandi del nodo corrente con quelli modificati
        node.operands = new_operands
        return node
    elif single in {'U', 'R'}: #nel caso in cui U e R escano dalla decomp di nested non sono mai qui
        if single == 'U' and node.lower != '0':
            new_G_node = Node(*['G', '0', node.lower, node.operands[0].to_list()])
            # Ritorna un nodo con ',' come operatore che include sia 'U' sia 'G'
            return Node(*[',', node.to_list(), new_G_node.to_list()])
        elif single == 'R' and node.lower != '0':
            new_G_node = Node(*['||', ['F', '0', node.lower, node.operands[0].to_list()], node.to_list()])
            return new_G_node
    else:
        return node

def count_implications(formula):
    if formula.operator == '&&':
        # Conta quante implicazioni ('->') ci sono tra gli operandi
        implication_count = sum(1 for operand in formula.operands if operand.operator == '->')
        # Aggiungi l'attributo 'implications' al nodo e assegna il conteggio
        formula.implications = implication_count
    else:
        # Se il nodo non è un '&&', esplora ricorsivamente i suoi operandi
        for operand in formula.operands:
            if isinstance(operand, Node):
                count_implications(operand)
    return formula

def build_decomposition_tree(root, max_depth):
    G = nx.DiGraph()
    time = extract_min_time(root.to_list(), root)
    counter = 0
    root_label = root.to_label(counter)
    G.add_node(root_label)
    print(root_label)

    def add_children(node, depth, current_time):
        nonlocal counter
        if depth < max_depth:
            node_copy = copy.deepcopy(node)
            current_time = extract_min_time(node_copy.to_list(), node_copy)
            node_label = node.to_label(counter)
            children = decompose(node_copy, current_time)
            if children is None:
                print('No more children in this branch')
                return
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
                    child_time = extract_min_time(child.to_list(), child)
                    child_time = current_time if child_time is None else child_time
                    child_label = child.to_label(counter)
                    G.add_node(child_label)
                    G.add_edge(node_label, child_label)
                    add_children(child, depth + 1, current_time)

    add_children(root, 0, time)
    return G


def plot_tree(G):
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=8, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()


'''
Come scrivere le formule:
gli estremi degli intervalli possono essere scritti come numeri interi, frazioni o numeri decimali (ma razionali)
le variabili devono essere precedute da B_ se sono booleane e R_ se sono reali
l'argomento di un operatore temporale, se non contiene un alto op temporale, deve essere scritto già come vincolo SMT
(vedi sintassi all'inizio)
'''

# formula = [['&&', ['G', '1/3', '9', ['B_p']], ['F', '4', '7', ['B_q']]]]
# formula = [['&&', ['G', '0.5', '9', ['B_p']], ['F', '4', '7', ['B_q']]]]
# formula = [['&&', ['G', '0.0', '9.0', ['B_p']], ['F', '4.0', '7.0', ['B_q']]]] #ok
# formula = [['&&', ['G', '0', '2', ['B_p']], ['F', '1', '3', ['!', ['B_p']]]]] #ok
# formula = [['G', '0', '2', ['&&', ['p'], ['q']]]] #come gestirlo? vedi sotto
# formula = [['G', '0', '2', ['And(B_p, B_q)']]]
# formula = [['F', '0', '5', ['B_q']]]
# formula = [['||', ['G', '0', '2', ['B_p']], ['F', '1', '3', ['B_q']]]] #ok
# formula = [['&&', ['F', '0', '2', ['B_p']], ['F', '1', '3', ['B_q']]]] #ok
# formula = [['G', '0', '3', ['F', '0', '2', ['B_p']]]]
# formula = [['F', '0', '3', ['G', '1', '4', ['B_p']]]]
# formula = [['G', '0', '5', ['G', '1', '3', ['B_p']]]]
# formula = [['F', '0', '5', ['F', '1', '4', ['B_p']]]]
# formula = [['&&', ['F', '0', '3', ['G', '1', '4', ['B_p']]], ['G', '0', '3', ['B_y']]]]
# formula = [['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['B_p']]]]]
# formula = [['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['F', '1', '3', ['B_p']]]]]] #problemi con la funz che plotta se depth >5
# formula = [['&&', ['F', '0', '3', ['G', '1', '4', ['B_p']]], ['G', '1', '6', ['!', ['B_p']]]]] #ok
# formula = [['&&', ['G', '0', '3', ['F', '1', '4', ['B_p']]], ['F', '1.0', '3.0', ['B_q']]]] #ok
# formula = [['&&', ['G', '0', '4', ['R_x>5']], ['F', '2', '4', ['R_x<2']]]] #consistency check ok
# formula = [['&&', ['G', '0', '4', ['R_x>5']], ['F', '2', '4', ['R_y<2']]]] #consistency check ok
# formula = [['&&', ['G', '0', '4', ['R_x>5']], ['F', '2', '4', ['R_y<2']], ['F', '1', '5', ['R_x == 4']]]] #ok
# formula = [['&&', ['G', '0', '4', ['Implies(B_q, R_x>2)']], ['F', '0', '4', ['Implies(B_q, R_x<1)']]]] #il ris mi confonde
# formula = [['&&', ['G', '0', '4', ['Implies(B_q, Not(B_p))']], ['F', '0', '4', ['Implies(B_q, B_p)']]]]
# formula = [['G', '0', '4', ['And(Implies(B_q, Not(B_p)), Implies(B_q, B_p))']]]
# formula = [['G', '0', '4', ['And(B_q, Not(B_q))']]]
# formula = [['&&', ['G', '0', '4', ['And(B_p, Not(B_p))']], ['F', '0', '4', ['R_x>9']]]]
# formula = [['&&', ['G', '0', '4', ['And(B_p, Not(B_p))']], ['F', '0', '4', ['R_x>9']]]]
# formula = [['U', '0', '5', ['B_p'], ['B_q']]]
# formula = [['&&', ['U', '0', '5', ['B_p'], ['B_q']], ['G', '0', '4', ['B_p']]]]
# formula = [['U', '1', '3', ['G', '1', '4', ['B_p']], ['B_q']]]
# formula = [['U', '1', '3', ['B_q'], ['G', '1', '4', ['B_p']]]]
# formula = [['U', '1', '3', ['G', '1', '4', ['B_p']], ['G', '2', '5', ['B_q']]]]
# formula = [['&&', ['G', '0', '7', ['F', '1', '3', ['B_p']]], ['G', '2', '9', ['B_y']]]]
# formula = [['G', '0', '7', ['F', '1', '3', ['B_p']]]]

# Crea nuovi nodi così:
# formula = Node(*['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['F', '1', '3', ['B_p']]]]])
#formula = Node(*['&&', ['G', '0', '9', ['R_x>5']], ['F', '4', '7', ['R_x<4']]])
#formula = Node(*['&&', ['G', '0', '9', ['B_p']], ['F', '4', '7', ['!', ['B_p']]]])
#formula = Node(*['||', ['G', '0', '9', ['B_p']], ['F', '4', '7', ['B_q']], ['G', '1', '6', ['B_z']]])
#formula = Node(*['F', '4', '7', ['B_q']])
#formula = Node(*[',', ['G', '1', '9', ['F', '2', '5', ['B_q']]], ['G', '0', '10', ['B_p']]])
#formula = Node(*['&&', ['G', '0', '10', ['F', '1', '2', ['B_p']]], ['G', '6', '9', ['B_q']]]) #sembra ok
#formula = Node(*['&&', ['G', '0', '10', ['F', '1', '2', ['B_p']]], ['F', '3', '10', ['F', '1', '2', ['B_p']]]])
#formula = Node(*['&&', ['G', '0', '2', ['F', '1', '10', ['B_p']]], ['G', '6', '9', ['B_q']]])
#formula = Node(*['U', '5', '8', ['B_q'], ['B_p']])
#formula = Node(*['U', '1', '5', ['G', '1', '2', ['B_p']], ['B_q']])
#formula = Node(*['U', '1', '3', ['B_p'], ['B_q']])
#formula = Node(*['&&', ['G', '3', '5', ['B_p']], ['U', '0', '7', ['B_q'], ['G', '0', '3', ['B_z']]]])
#formula = Node(*['R', '2', '9', ['B_p'], ['B_q']])
#formula = Node(*['R', '0', '9', ['G', '0', '9', ['B_p']], ['B_q']]) #no problemi
#formula = Node(*['R', '2', '9', ['B_q'], ['B_p']])
#formula = Node(*['&&', ['G', '0', '5', ['B_z']], ['R', '0', '9', ['B_q'], ['G', '0', '9', ['B_p']]]])
#formula = Node(*['U', '0', '9', ['G', '0', '2', ['B_p']], ['B_q']]) #problematico il salto
#formula = Node(*['U', '0', '9', ['B_q'], ['F', '0', '3', ['B_p']]]) #no problemi
#formula = Node(*['&&', ['G', '0', '9', ['B_p']], ['R', '2', '4', ['B_q'], ['B_z']]])
#formula = Node(*['&&', ['G', '0', '9', ['B_p']], ['G', '1', '7', ['||', ['B_q'], ['B_z']]]])
formula = Node(*['G', '0', '6', ['U', '2', '4', ['B_p'], ['B_q']]])
#formula = Node(*['F', '1', '6', ['G', '1', '3', ['B_p']]])
#formula = Node(*['G', '0', '2', ['G', '1', '4', ['B_p']]])
#formula = Node(*['U', '0', '2', ['G', '1', '4', ['B_p']], ['B_q']])
#formula = Node(*['->', ['G', '1', '4', ['B_p']], ['B_q']])
#formula = Node(*['&&', ['->', ['G', '1', '4', ['B_p']], ['B_q']], ['G', '1', '7', ['||', ['B_x'], ['B_z']]]])
#formula = Node(*['&&', ['->', ['G', '1', '4', ['B_p']], ['B_q']], ['->', ['G', '1', '7', ['B_p']], ['B_z']]])
#formula = Node(*['->', ['B_p'], ['B_q']])
#formula = Node(*['&&', ['->', ['G', '1', '4', ['B_p']], ['B_q']], ['->', ['F', '2', '3', ['!', ['B_p']]], ['B_z']]])

# Benchmark: (requisiti Leonardo)
# 1) stabilire un time horizon (T)
# formula = Node(*['G', '0', 'T', ['||', ['&&', ['B_active'], ['!', [B_inactive]], ['!', ['B_armed']] ], ['&&', ['B_inactive'], ['!', [B_active]], ['!', ['B_armed']]], ['&&', ['B_armed'], ['!', [B_inactive]], ['!', ['B_active']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['B_inactive'], ['R_n_s == 1'],  ['R_X_c-R_X_b <= 5'], ['R_X_c-R_X_b>= -5'], ['G', '0', '5', ['R_airspeed>= R_Vmin']], ['!', ['B_X_over']], ['B_X_Activation_Request']], ['F', '0', '2', ['&&', ['!', ['inactive']], ['active']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['active'], ['||', ['!', ['R_n_s == 1']], ['F', '0', '10', ['B_X_ch']], ['G', '0', '5', ['R_airspeed < R_Vmin']],  ['!', ['B_r_actuation']], ['!', ['B_X_Activation_Request']]], ['F', '0', '2', ['&&', ['!', ['B_active']], ['B_inactive']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['B_armed'], ['||', ['!', ['R_n_s ==1']], ['F', '0', '5', ['B_X_ch']], ['!', ['B_X_Activation_Request']], ['!', ['B_r_actuation']]]], ['F', '0', '2', ['&&', ['!', ['B_armed']], ['B_inactive']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['B_inactive'], ['R_n_s ==1'], ['||', ['R_X_c - R_X_b >5'], ['R_X_c - R_X_b <-5']], ['B_X_Activation_Request'] ], ['F', '0', '2', ['&&', ['!', ['B_inactive']], ['B_armed']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['B_armed'], ['!', ['B_X_over']], ['R_X_c - R_X_b <=5'], ['R_X_c - R_X_b >=-5'], ['G', '0', '5', ['R_airspeed >= R_Vmin']] ], ['F', '0', '2', ['&&', ['!', ['B_armed']], ['B_active']]]]]) #DOPPIONE
# formula = Node(*['G', '0', 'T', ['||', ['&&', ['B_active'], ['B_A'] ], ['&&', ['B_active'], ['B_B']], ['&&', ['B_active'], ['B_C']]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['B_active'], ['B_A'], ['!', ['B_X_over']], ['R_Delta_T_Error_reference < |T Error|'], ['R_Delta_T_Error_reference > -|R_T_Error|]], ['F', '0', '1', ['&&', ['!', ['B_A']], ['B_B']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['B_active'], ['B_B'], ['!', ['B_X_over']], ['R_T_Error < | 3'], ['R_T_Error  > -3] ,  ['R_Roll_attitude < 0.8'], ['R_Roll_attitude > -0.8'],  ['R_X_deviation < 0.5'], ['R_X_deviation > -0.5'] , ['R_dalfa/dt < 0.002'], ['R_dalfa/dt > -0.002'], ['!', ['B_h_on]], ['!', ['B_f_on']]], ['F', '0', '1', ['&&', ['!', ['B_B']], ['B_C']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['B_active'], ['B_C'], ['!', [B_X_over]], ['||', ['R_T_Error > 5'], ['R_T_Error < -5']], ['||', ['R_Roll_attitude > 2.6'], ['R_Roll_attitude < -2.6']], ['||', ['R_X_deviation > 1.5'], ['R_X_deviation < -1.5']], ['||', ['R_dalfa/dt > 0.075'], ['R_dalfa/dt < -0.075']], ['||', ['B_h_on'], ['B_f_on']]], ['F', '0', '1', ['&&', ['!', ['B_C']], ['B_B']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['B_active'], ['!', ['B_X_over']]], ['F', '0', '5', ['R_LME_cr == 1']]]])
# formula = Node(*['G', '0', 'T', ['->', ['B_inactive'], ['F', '0', '5', ['R_LME_cr == 0']]]])
# formula = Node(*['G', '0', 'T', ['->', ['B_armed'], ['F', '0', '5', ['R_LMA_cr == 1']]]])
# formula = Node(*['G', '0', 'T', ['->', ['B_active'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['B_inactive'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['B_X_over'] , ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['B_X_over'], ['B_active'] ] , ['F', '0', '5', ['B_LME_cr']]]])
# formula = Node(*['G', '0', 'T', ['->', ['B_active'] , ['F', '0', '1', ['R_Y_pushbutton == 1']]]])
# formula = Node(*['G', '0', 'T', ['->', ['B_armed'] , ['F', '0', '1', ['R_Y_pushbutton == 2']]]])
# formula = Node(*['G', '0', 'T', ['->', ['&&', ['R_airspeed < Vmin'], [????]] , ['F', '0', '5', ['B_LS_amr']]]])

#Range parametri:

# formula = Node(*['G', '0', 'T', ['&&', ['R_X_c >=0'], ['R_X_c <= 360']]])
# formula = Node(*['G', '0', 'T', ['&&', ['R_X_b >=0'], ['R_X_b <= 360']]])
# formula = Node(*['G', '0', 'T', ['&&', ['R_airspeed >=0'], ['R_airspeed <= 200']]])
# formula = Node(*['G', '0', 'T', ['&&', ['R_a >= 0'], ['R_a <= 360']]])
# formula = Node(*['G', '0', 'T', ['||', ['R_n_s == 0'], ['R_n_s == 1'], ['R_n_s == 2']]])
# formula = Node(*['G', '0', 'T', ['&&', ['R_T_Error >= -180'], ['R_T_Error <= 180']]])
# formula = Node(*['G', '0', 'T', ['&&', ['R_Roll_attitude >= -50'], ['R_Roll_attitude <= 50']]])
# formula = Node(*['G', '0', 'T', ['&&', ['R_X_deviation >= -180'], ['R_X_deviation <= 180'] ]])
# formula = Node(*['G', '0', 'T', ['||', ['R_LME_cr == 0'], ['R_LME_cr == 1'], ['R_LME_cr == 2']]])
# formula = Node(*['G', '0', 'T', ['||', ['R_LMA_cr == 0'], ['R_LMA_cr == 1'], ['R_LMA_cr == 2']]])
# formula = Node(*['G', '0', 'T', ['||', ['R_Y_pushbutton == 0'], ['R_Y_pushbutton == 1'], ['R_Y_pushbutton == 2']]])


formula = add_G_for_U(formula, formula.operator, False)
formula = assign_identifier(formula)
formula = count_implications(formula)
set_initial_time(formula)
max_depth = 5

# formula = normalize_bounds(formula)


tree = build_decomposition_tree(formula, max_depth)
print(tree)
plot_tree(tree)



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