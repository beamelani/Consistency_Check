#Nuova versione del codice Tableau test che prende come input una lista del tipo:

"""
[['&&', 'sottof1', 'sottof2',...]]
|| come sopra
! come sopra
[['G', 'lowerb', 'upperb', 'arg']]
F come sopra
[['O', 'arg']]
[['U', 'lowerb', 'upperb', 'arg1', 'arg2']]

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

#utente deve solo inserire in input la max_depth dell'albero

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

def extract_min_time(formula):
    """
    Estrae l'istante di tempo minimo da una formula STL, serve per sapere l'istante corrente
    durante la decomposizione

    """
    min_times = []
    if isinstance(formula, list):
        if len(formula) == 1:
            return extract_min_time(formula[0])
        if formula[0] == '!':
            return None
        if formula[0] in {'&&', '||', ','}:
            for i in range(1, len(formula)):
                if len(formula[i]) > 1 and formula[i][0] not in {'O', '!'}:
                    if formula[i][3][0] in {'G', 'F', 'U'}: #caso nested, non O
                        min_time = str(Fraction(formula[i][1]) + Fraction(formula[i][3][1]))
                        min_times.append(min_time)
                    elif formula[i][0] in 'U' and formula[i][4][0] in {'G', 'F', 'U'}: #caso nested U second arg
                        min_time = str(Fraction(formula[i][1]) + Fraction(formula[i][4][1]))
                        min_times.append(min_time)
                    else:  #caso non nested e non O
                        min_time = formula[i][1]
                        min_times.append(min_time)
                elif len(formula[i]) > 1 and formula[i][0] in {'O'}:
                    if formula[i][1][3][0] in {'G', 'F', 'U'}: #caso nested,  O
                        min_time = str(Fraction(formula[i][1][1]) + Fraction(formula[i][1][3][1]))
                        min_times.append(min_time)
                    elif formula[i][1][0] in 'U' and formula[i][1][4][0] in {'G', 'F', 'U'}: # O U con nesting in second arg
                        min_time = str(Fraction(formula[i][1][1]) + Fraction(formula[i][1][4][1]))
                        min_times.append(min_time)
                    else: #caso non nested, O
                        min_time = formula[i][1][1]
                        min_times.append(min_time)
        elif formula[0] in {'G', 'F', 'U'}: #formula ha un solo elemento
            if formula[3][0] not in {'G', 'F', 'U'}: #caso non nested
                min_time = formula[1]
                min_times.append(min_time)
            elif formula[0] in 'U' and formula[4][0] not in {'G', 'F', 'U'}: #caso non nested until second arg
                min_time = formula[1]
                min_times.append(min_time)
            elif formula[0] in 'U' and formula[4][0] in {'G', 'F', 'U'}: #caso nested secondo arg
                min_time = str(Fraction(formula[1]) + Fraction(formula[4][1]))
                min_times.append(min_time)
            else: #tutti gli altri casi nested
                min_time = str(Fraction(formula[1]) + Fraction(formula[3][1]))
                min_times.append(min_time)
        elif formula[0] in {'O'}: #formula ha un solo elemento in O
            if formula[1][3][0] not in {'G', 'F', 'U'} or (formula[1][0] in 'U' and formula[1][4][0] not in {'G', 'F', 'U'}):
                min_time = formula[1][1]
                min_times.append(min_time)
            elif formula[1][3][0] in {'G', 'F', 'U'}: #caso nested  modificare per inserire anche until con nesting in secondo arg
                min_time = str(Fraction(formula[1][1]) + Fraction(formula[1][3][1]))
                min_times.append(min_time)
            elif formula[1][0] in 'U' and formula[1][4][0] in {'G', 'F', 'U'}:
                min_time = str(Fraction(formula[1][1]) + Fraction(formula[1][4][1]))
                min_times.append(min_time)
    if min_times:
        return Fraction(min(min_times))
    else:
        return None


def calculate_min_step(formula):
    """
    Calcola il passo discreto minimo necessario per una formula temporale, quando intervalli hanno
    estremi frazionari
    """

    def extract_intervals(formula):
        intervals = []
        if isinstance(formula, list):
            for elem in formula:
                if isinstance(elem, list):
                    if elem[0] in ['G', 'F', 'U']:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                        start = Fraction(elem[1])
                        end = Fraction(elem[2])
                        difference = end-start
                        if difference > 0:
                            intervals.append(difference)
                    intervals.extend(extract_intervals(elem))  # Ricorsione per esplorare strutture annidate
        return intervals
    # Estrazione degli intervalli dalla formula
    intervals = extract_intervals(formula)
    #Verifica se tutti gli intervalli sono interi
    res = all(f == Fraction(int(f)) for f in intervals)
    # Se non ci sono intervalli validi o se tutti gli intervalli sono interi, restituisce 1 (avanzamento di default)
    if not intervals or res:
        return 1

    # Trova il minimo comune multiplo

    denominatori = [i.denominator for i in intervals]

    mcm_denominatori = reduce(lambda x, y: abs(x * y) // gcd(x, y), denominatori)

    risultato = Fraction(1, mcm_denominatori)

    return risultato


def calculate_time_quantum(formula):
    """
    Compute the maximum time length `quantum` such that all interval bounds are integer multiples of `quantum`.
    """
    def extract_bounds(formula):
        bounds = []
        if isinstance(formula, list):
            for elem in formula:
                if isinstance(elem, list):
                    if elem[0] in ['G', 'F', 'U']:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
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
        return str(int(Fraction(bound)/quantum))

    def recompute_bounds(formula):
        if isinstance(formula, list) and formula[0]:
            if isinstance(formula[0], list):
                return list(map(recompute_bounds, formula))
            elif formula[0] in {'&&', '||', ','}:
                return [formula[0]] + list(map(recompute_bounds, formula[1:]))
            elif formula[0] in {'G', 'F'}:
                return [formula[0], norm_bound(formula[1]), norm_bound(formula[2]), recompute_bounds(formula[3])]
            elif formula[0] == 'U':
                return [formula[0], norm_bound(formula[1]), norm_bound(formula[2]), recompute_bounds(formula[3]), recompute_bounds(formula[4])]
            elif len(formula) == 1 and isinstance(formula[0], str):
                return formula
            else:
                raise ValueError('Malformed formula ' + str(formula))
        return formula

    return recompute_bounds(formula)


def extract_time_instants(formula):
    """
    :return: funzione che restituisce gli estremi di tutti gli intervalli della formula in un vettore ordinato
    Come fare per operatori annidati? Forse la funzione andrebbe richiamata ogni volta e non solo una, perché
    si generano nuovi elementi
    """
    time_instants = []
    if isinstance(formula, list):
        for elem in formula:
            if isinstance(elem, list):
                if elem[0] in ['G', 'F', 'U']:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                    time_instants.append(elem[1])
                    time_instants.append(elem[2])
                elif elem[0] in ['O']:
                    time_instants.append(elem[1][1])
                    time_instants.append(elem[1][2])
    time_instants = [Fraction(x) for x in time_instants]
    time_instants = sorted(time_instants)
    return time_instants


def check_nested(formula):
    '''
    :param formula:
    :return: la formula controlla che non ci siano operatori nested (serve per fare i salti)
    Restituisce true se ci sono, false se non ci sono
    '''
    if len(formula) == 1:
        formula = formula[0]
    if formula[0] == ',':
        for element in formula:
            if element[0] in {'G', 'F', 'U'} and element[3][0] in {'G', 'F', 'U'}:
                return True
            elif element[0] in {'U'} and element[4][0] in {'G', 'F', 'U'}: #until ha 2 args, il nesting può anche essere nel secondo
                return True
            elif element[0] == 'O' and element[1][0] in {'G', 'F', 'U'} and element[1][3][0] in {'G', 'F', 'U'}:
                return True
            elif element[0] == 'O' and element[1][0] in 'U' and element[1][4][0] in {'G', 'F', 'U'}:
                return True
    else:
        if formula[0] in {'G', 'F', 'U'} and formula[3][0] in {'G', 'F', 'U'}:
            return True
        elif formula[0] in {'U'} and formula[4][0] in {'G', 'F','U'}:
            return True
        elif formula[0] == 'O' and formula[1][0] in {'G', 'F', 'U'} and formula[1][3][0] in {'G', 'F', 'U'}:
            return True
        elif formula[0] == 'O' and formula[1][0] in 'U' and formula[1][4][0] in {'G', 'F', 'U'}:
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

    elif operator == '&&':
        subformulas = [f"({formula_to_string(subformula)})" for subformula in formula[1:]]
        return " && ".join(subformulas)

    elif operator == ',':
        subformulas = [f"({formula_to_string(subformula)})" for subformula in formula[1:]]
        return " , ".join(subformulas)

    elif operator == '||':
        subformulas = [f"({formula_to_string(subformula)})" for subformula in formula[1:]]
        return " || ".join(subformulas)

    #elif operator == '->':  # Implication
        #subformulas = [f"({formula_to_string(subformula)})" for subformula in formula[1:]]
        #return " -> ".join(subformulas)


def decompose(node, current_time):
    """
    :param node: lista da decomporre che ha la forma esplicitata sopra
    :param current_time: istante di tempo attuale, per capire quali operatori sono attivi e quali no
    :return: ritorna la lista decomposta (i.e. il successivo nodo del tree)
    """
    if isinstance(node, list):
        counter = 0
        if len(node) == 1:
            return decompose(node[0], current_time)
        if node[0] == '&&':
            return decompose_and(node)
        elif node[0] == '||':
            return decompose_or(node)
        #Se il nodo iniziale ha solo un elemento (quindi non è un and o or di più sottoformule) lo decompongo con i 5 elif di seguito
        elif node[0] == 'G' and node[3][0] not in {'F', 'G', 'U'}: #non credo che in questi serva controllare il tempo perché se ho un solo elemento è sicuramente attivo perché considero solo il suo intervallo temp
            return decompose_G(node, 1)
        elif node[0] == 'F' and node[3][0] not in {'F', 'G', 'U'}:
            return decompose_F(node, [], 0)
        elif node[0] == 'U' and node[3][0] not in {'F', 'G', 'U'} and node[4][0] not in {'F', 'G', 'U'}:
            return decompose_U(node, [], 0)
        elif node[0] == '!':
            counter += 1
        #Caso nested
        elif node[0] in {'F', 'G'} and node[3][0] in {'F', 'G', 'U'}:
            return decompose_nested(node, [], 0)
        elif node[0] in 'U' and (node[3][0] in {'F', 'G', 'U'} or node[4][0] in {'F', 'G', 'U'}):
            #return decompose_nested(node, [], 0) serve??
            return decompose_U(node, [], 0) #dovrebbe estrarli già questo
        #Jump
        elif node[0] == 'O': #se c'è un solo elemento non servono altre condizioni
            res = smt_check(node)
            if res == 'Rejected':
                return [res]
            else:
                return decompose_jump(node)
        #Scrivo un nodo come una virgola (un and) di tutti gli elementi del nodo
        elif node[0] == ',':
            for j in range(1, len(node)):
                if node[j][0] == 'G' and Fraction(node[j][1]) == current_time and node[j][3][0] not in {'G', 'F', 'U'}:
                    result = decompose_G(node[j], 0) #meglio passare una copia???
                    new_node = copy.deepcopy(node)
                    new_node.extend(result)
                    del new_node[j]
                    return [new_node]
                elif node[j][0] == 'F' and Fraction(node[j][1]) == current_time and node[j][3][0] not in {'G', 'F', 'U'}:
                    result = decompose_F(node[j], node, j)
                    return result
                elif node[j][0] == 'U' and Fraction(node[j][1]) == current_time and node[j][3][0] not in {'G', 'F', 'U'} and node[j][4][0] not in {'G', 'F', 'U'}:
                    return decompose_U(node[j], node, j)
                #Caso Nested:
                elif node[j][0] in {'G', 'F'} and node[j][3][0] in {'G', 'F', 'U'} and Fraction(node[j][1]) + Fraction(node[j][3][1]) == current_time:
                    return decompose_nested(node[j], node, j)
                elif node[j][0] in 'U':
                    if node[j][3][0] in {'G', 'F'} and Fraction(node[j][1]) + Fraction(node[j][3][1]) == current_time:
                        #return decompose_nested(node[j], node, j)
                        return decompose_U(node[j], node, j)
                    elif node[j][4][0] in {'G', 'F', 'U'} and Fraction(node[j][1]) + Fraction(node[j][4][1]) == current_time:
                        #return decompose_nested(node[j], node, j)
                        return decompose_U(node[j], node, j)
                else: #se arrivo qui vuol dire che non sono entrata in nessun return e quindi non c'era nulla da decomporre
                    #perché l'elemento era già decomposto o non ancora attivo
                    counter += 1
        if counter == len(node) - 1: #-1 perché un elemento del nodo è la virgola
            #fai qui il check accept/reject, se rigetti non serve nemmeno fare il jump
            res = smt_check(node)
            if res == 'Rejected':
                return [res]
            else:
                return decompose_jump(node)

    return None #se non c'è niente da decomporre


def decompose_G(node, single):
    #single==1 indica che la formula è unica (non fa già parte di un and) e quindi devo aggiungere ',' all'inizio
    if single == 1:
        node = [[',', ['O', node], node[3]]]
    else:
        node = [['O', node], node[3]]
    return node


def decompose_F(node, formula, index):
    node_1 = [['O', node]]
    node_2 = [node[3]]
    if index > 0: #se il F è una sottoformula (è in and con altre formule)
        formula_1 = copy.deepcopy(formula)
        formula_2 = copy.deepcopy(formula)
        del formula_1[index] #tolgo il F dalla formula di partenza
        del formula_2[index]
        formula_1.extend(node_1) #sdoppio la formula di partenza (senza il F) e aggiungo a una un pezzo e all'altra l'altro
        formula_2.extend(node_2)
    else: #se il F è l'unica formula
        formula_1 = node_1
        formula_2 = node_2
    return [formula_1, formula_2]


def decompose_U(node, formula, index):
    # esempio :['U', '2', '5', ['p'], ['q']] come lo decompongo?
    '''
    Potrei decomporlo dicende che all'istante 2 può succedere p o q, se succede q il req è già soddisfatto e non mi interessa
    più cosa succede dopo (posso eliminare U da quel ramo. Mentre se succede p dovrò riportare che voglio avere pU[3,5]q all'ora all'istante successivo può succedere di nuovo p,
    oppure può succedere q e così via fino a 5, se a 5 è sempre successo p e mai q elimino il ramo perché U non è soddisfatto
    :return:
    '''
    if formula:
        if node[3][0] in {'G', 'F', 'U'}:
            new_node = copy.deepcopy(node[3])
            new_node[1] = str(Fraction(new_node[1]) + Fraction(node[1]))
            new_node[2] = str(Fraction(new_node[2]) + Fraction(node[1]))
            node_1 = [['O', node], new_node]
        else:
            node_1 = [['O', node], node[3]]
    else:
        if node[3][0] in {'G', 'F', 'U'}:
            new_node = copy.deepcopy(node[3])
            new_node[1] = str(Fraction(new_node[1]) + Fraction(node[1]))
            new_node[2] = str(Fraction(new_node[2]) + Fraction(node[1]))
            node_1 = [',', ['O', node], new_node]
        else:
            node_1 = [',', ['O', node], node[3]]
    if node[4][0] in {'G', 'F', 'U'}:
        new_node2 = copy.deepcopy(node[4])
        new_node2[1] = str(Fraction(new_node2[1]) + Fraction(node[1]))
        new_node2[2] = str(Fraction(new_node2[2]) + Fraction(node[1]))
        node_2 = [new_node2]
    else:
        node_2 = [node[4]]
    if index > 0: #se U è una sottoformula (è in and con altre formule)
        formula_1 = copy.deepcopy(formula)
        formula_2 = copy.deepcopy(formula)
        del formula_1[index] #tolgo U dalla formula di partenza
        del formula_2[index]
        formula_1.extend(node_1) #sdoppio la formula di partenza (senza U) e aggiungo a una un pezzo e all'altra l'altro
        formula_2.extend(node_2)
    else: #se U è l'unica formula
        formula_1 = node_1
        formula_2 = node_2
    return [formula_1, formula_2]


def decompose_and(node): #voglio che tolga TUTTI gli '&&'
    for i in range(len(node)):
        if isinstance(node[i], list):
            decompose_and(node[i])
        elif node[i] == '&&':
            node[i] = ','
    print(node)
    return [node]


def decompose_or(node): #basta togliere l'or e fare in modo che la lista venga restituita alla funzione add children
    #come lista di tot elementi, dove ogni elemento è un argomento dell'or, in modo che add children la interpreti come
    #tanti children diversi
    node = node[1:]
    return node


def decompose_nested(node, formula, index):
    #se la formula è unica (non un and di sottoformule), allora index==0 e formula=[]
    if index == 0:
        if node[0] == 'G':
            extract = copy.deepcopy(node[3])
            extract[1] = str(Fraction(node[1]) + Fraction(extract[1])) #quando estraggo l'op annidato devo modificare l'intervallo temporale
            extract[2] = str(Fraction(node[1]) + Fraction(extract[2]))
            node = [[',', ['O', node], extract]]
            return node
        elif node[0] == 'F':
            extract = copy.deepcopy(node[3])
            extract[1] = str(Fraction(node[1]) + Fraction(extract[1])) #quando estraggo l'op annidato devo modificare l'intervallo temporale
            extract[2] = str(Fraction(node[1]) + Fraction(extract[2]))
            res_1 = copy.deepcopy(node)
            res_1 = ['O', res_1]
            node = [res_1, extract]
            return node
        #elif node[0] == 'U':
            #completa
            #return node
    else:
        if node[0] == 'G':
            res_1 = copy.deepcopy(formula)
            del res_1[index] #tolgo il nested dalla formula
            extract = copy.deepcopy(node[3])
            extract[1] = str(Fraction(node[1]) + Fraction(extract[1]))  # quando estraggo l'op annidato devo modificare l'intervallo temporale
            extract[2] = str(Fraction(node[1]) + Fraction(extract[2]))
            node = [['O', node], extract]
            res_1.extend(node)
            return [res_1]
        elif node[0] == 'F':
            res_1 = copy.deepcopy(formula)
            res_2 = copy.deepcopy(formula)
            del res_1[index]
            del res_2[index]
            extract = copy.deepcopy(node[3])
            extract[1] = str(Fraction(node[1]) + Fraction(extract[1]))
            extract[2] = str(Fraction(node[1]) + Fraction(extract[2]))
            node = [['O', node]]
            res_1.extend(node)
            res_2.extend([extract])
            return [res_1, res_2] #ricontrolla se le parentesi vanno bene
        #elif node[0] == 'U':
            #completa
    return


def decompose_jump(node):
    """
    dovrebbe essere ok: fa fare il salto agli elementi con 0, lascia come sono quelli con F,G non ancora attivi
    ed elimina il resto
    Se la formula di partenza NON ha operatori annidati, il salto è COMPLETO

    """
    nested = check_nested(node) #meglio controllare qui, perché anche se la formula di partenza è nested,
    #posso avere rami in cui non ho operatori nested e quindi posso accorciarli
    time_instants = extract_time_instants(node)
    #Caso in cui input sia della forma [',', [], [], ....] (un and di tante sottoformule)
    new_node = []
    if node[0] == '!':
        return None
    if node[0] == ',':
        new_node = [',']
        for i in range(1, len(node)):
            if node[i][0] in {'F', 'G', 'U'}:
                new_node.extend([node[i]])
            elif node[i][0] in {'O'} and Fraction(node[i][1][1]) < Fraction(node[i][1][2]): #incremento solo se lb < ub
                if node[i][1][0] == 'G' and len(node) == 3 and node[i][1][3][0] not in {'G', 'F', 'U'} and nested:
                    #ho solo un G nel ramo (ma è generato dalla dec di un operatore nested), posso passare all'ultimo istante
                    sub_formula = copy.deepcopy(node[i][1])
                    sub_formula[1] = sub_formula[2]
                    new_node.extend([sub_formula])
                elif not nested: #se non ho operatori annidati salto al prossimo istante in cui cambia qualcosa
                    sub_formula = copy.deepcopy(node[i][1])
                    indice = bisect.bisect_right(time_instants, Fraction(sub_formula[1])) #trovo il primo numero maggiore dell'istante corrente di tempo
                    sub_formula[1] = str(time_instants[indice])
                    new_node.extend([sub_formula])
                else:
                    sub_formula = copy.deepcopy(node[i][1]) #node[i][1] dovrebbe essere l'argomenti di 'O'
                    sub_formula[1] = str(Fraction(sub_formula[1]) + step)
                    new_node.extend([sub_formula])
        if len(new_node) == 2: #se uno degli elementi iniziale è della forma OG[x,x],
            # cioè ha esaurito l'intervallo e viene eliminato, è possibile  che rimanga un solo elemento, ma preceduto dalla virgola anche se non dovrebbe
            return [new_node[1]]
        elif new_node != [',']:
            return [new_node]
        else:
            return None
    else: #caso in cui ho una formula con un unico operatore
        if Fraction(node[1][1]) < Fraction(node[1][2]):
            #nel caso GF non posso skippare, perché devo attraversare tutto l'intervallo temporale del F
            if len(node[1][3]) > 2 and node[1][0] == 'G' and node[1][3][0] in {'F', 'G'}: #SBAGLIATO, non entri mai qui, perché appena decomponi hai già almeno 2 elementi in questo caso
                sub_formula = copy.deepcopy(node[1])  # node[1] dovrebbe essere l'argomenti di 'O'
                sub_formula[1] = str(Fraction(sub_formula[1]) + step)
                new_node.extend([sub_formula])
            else:
                sub_formula = copy.deepcopy(node[1])  # node[1] dovrebbe essere l'argomenti di 'O'
                sub_formula[1] = sub_formula[2] #se ho una sola formula posso già saltare all'ultimo istante di tempo, tranne se è GF
                new_node.extend([sub_formula])
            return [new_node]
        else:
            return None


def smt_check(node):
    """
    NB : Potresti avere anche variabili Bool, qui setti tutte le variabili come Real
    in realtà però dovrebbe già esistere un data dictionary con tutte le variabili del problema (serve per riempire
    i pattern, quindi il tipo di ogni variabile potrebbe essere automaticamente estratto da lì, così come i vincoli
    sui bound della variabile che possono essere aggiunti come espressioni atomiche nel nodo
    :param node:
    :return: ritorna il nodo di partenza se è accepted, ritorna None se il nodo è rejected
    """
    new_node = []
    variabili_z3 = {}
    variabili = []
    vincoli = []
    for i in range(len(node)):
        if node[0] == ',': #caso con più elementi
            if node[i][0] == 'O' and node[i][1][0] in {'F', 'U'} and node[i][1][1] == node[i][1][2]:
                if node[i][1][0] in 'F':
                    print("Node is rejected because finally was never satisfied in this branch")
                else:
                    print("Node is rejected because until was never satisfied in this branch")
                return 'Rejected'
            if node[i][0] not in {'O', 'F', 'G', 'U', ','}:
                new_node.extend(node[i])
                if len(node[i]) == 1:
                    new_var = re.findall(r'\b[B|R]_[a-zA-Z]\w*\b', new_node[-1])
                else:
                    new_var = re.findall(r'\b[B|R]_[a-zA-Z]\w*\b', new_node[-1][0])
                variabili.extend(new_var)
        else:  #caso con un solo elemento (succede se ho un ramo con solo un finally)
            if node[0] == 'O' and node[i][0] in 'F' and node[1][1] == node[1][2]:
                print("Node is rejected because finally was never satisfied in this branch")
                return 'Rejected'
            if node[0] not in {'O', 'F', 'G', 'U', ','}:
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
    new_node = modify_node(new_node) #tolgo B_ e R_ che non servono più
    for i in range(len(new_node)):
        #devo estrarre le espressioni e definirle in SMT tipo
        #x= Real('x')
        if new_node[i] == '!':
            new_node[i+1] = 'Not(' + new_node[i+1][0] + ')'
        #Scrivere vincoli (in realtà sono già scritti in new node, bisogna solo inserirci le variabili z
        else:
            esp_z3 = new_node[i]
            for var in variabili_z3:
                #esp_z3 = esp_z3.replace(var, f'variabili_z3["{var}"]')
                esp_z3 = re.sub(rf'\b{var}\b', f'variabili_z3["{var}"]', esp_z3)
            vincoli.append(eval(esp_z3))
    solver = Solver()
    #aggiungi vincoli al solver
    solver.add(vincoli)
    #Verifica se vincoli sono sat
    if solver.check() == sat:
        print("Node is accepted, expressions are consistent")
        #print(solver.model())
        return node
    else:
        print("Node is rejected, expressions are inconsistent")
        return 'Rejected'


def modify_node(node):
    '''

    :param node:
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


def build_decomposition_tree(root, max_depth):
    G = nx.DiGraph()
    time = extract_min_time(root)
    counter = 0
    root_label = " ".join([formula_to_string(root), str(time), str(counter)])
    G.add_node(root_label)
    print(formula_to_string(root))

    def add_children(node, depth, current_time):
        nonlocal counter
        if depth < max_depth:
            node_copy = copy.deepcopy(node)
            current_time = extract_min_time(node_copy)
            node_label = " ".join([formula_to_string(node), str(current_time), str(counter)])
            children = decompose(node_copy, current_time)
            if children is None:
                print('No more children in this branch')
                return
            else:
                print(formula_to_string(children))
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
                    child_label = " ".join([formula_to_string(child), str(child_time), str(counter)])
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


#formula = [['&&', ['G', '1/3', '9', ['B_p']], ['F', '4', '7', ['B_q']]]]
#formula = [['&&', ['G', '0.5', '9', ['B_p']], ['F', '4', '7', ['B_q']]]]
#formula = [['&&', ['G', '0', '9', ['B_p']], ['F', '4', '7', ['B_q']]]] #ok
formula = [['F', '1', '9', ['G', '2', '5', ['B_q']]]]
#formula = [['&&', ['G', '0', '2', ['B_p']], ['F', '1', '3', ['!', ['B_p']]]]] #ok
#formula = [['G', '0', '2', ['&&', ['p'], ['q']]]] #come gestirlo? vedi sotto
#formula = [['G', '0', '2', ['And(B_p, B_q)']]]
#formula = [['F', '0', '5', ['B_q']]]
#formula = [['||', ['G', '0', '2', ['B_p']], ['F', '1', '3', ['B_q']]]] #ok
#formula = [['&&', ['F', '0', '2', ['B_p']], ['F', '1', '3', ['B_q']]]] #ok
#formula = [['G', '0', '3', ['F', '0', '2', ['B_p']]]]
#formula = [['F', '0', '3', ['G', '1', '4', ['B_p']]]]
#formula = [['G', '0', '5', ['G', '1', '3', ['B_p']]]]
#formula = [['F', '0', '5', ['F', '1', '4', ['B_p']]]]
#formula = [['&&', ['F', '0', '3', ['G', '1', '4', ['B_p']]], ['G', '0', '3', ['B_y']]]]
#formula = [['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['B_p']]]]]
#formula = [['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['F', '1', '3', ['B_p']]]]]] #problemi con la funz che plotta se depth >5
#formula = [['&&', ['F', '0', '3', ['G', '1', '4', ['B_p']]], ['G', '1', '6', ['!', ['B_p']]]]] #ok
#formula = [['&&', ['G', '0', '3', ['F', '1', '4', ['B_p']]], ['F', '1.0', '3.0', ['B_q']]]] #ok
#formula = [['&&', ['G', '0', '4', ['R_x>5']], ['F', '2', '4', ['R_x<2']]]] #consistency check ok
#formula = [['&&', ['G', '0', '4', ['R_x>5']], ['F', '2', '4', ['R_y<2']]]] #consistency check ok
#formula = [['&&', ['G', '0', '4', ['R_x>5']], ['F', '2', '4', ['R_y<2']], ['F', '1', '5', ['R_x == 4']]]] #ok
#formula = [['&&', ['G', '0', '4', ['Implies(B_q, R_x>2)']], ['F', '0', '4', ['Implies(B_q, R_x<1)']]]] #il ris mi confonde
#formula = [['&&', ['G', '0', '4', ['Implies(B_q, Not(B_p))']], ['F', '0', '4', ['Implies(B_q, B_p)']]]]
#formula = [['G', '0', '4', ['And(Implies(B_q, Not(B_p)), Implies(B_q, B_p))']]]
#formula = [['G', '0', '4', ['And(B_q, Not(B_q))']]]
#formula = [['&&', ['G', '0', '4', ['And(B_p, Not(B_p))']], ['F', '0', '4', ['R_x>9']]]]
#formula = [['&&', ['G', '0', '4', ['And(B_p, Not(B_p))']], ['F', '0', '4', ['R_x>9']]]]
#formula = [['U', '0', '5', ['B_p'], ['B_q']]]
#formula = [['&&', ['U', '0', '5', ['B_p'], ['B_q']], ['G', '0', '4', ['B_p']]]]
#formula = [['U', '1', '3', ['G', '1', '4', ['B_p']], ['B_q']]]
#formula = [['U', '1', '3', ['B_q'], ['G', '1', '4', ['B_p']]]]
#formula = [['U', '1', '3', ['G', '1', '4', ['B_p']], ['G', '2', '5', ['B_q']]]]
#formula = [['&&', ['G', '0', '7', ['F', '1', '3', ['B_p']]], ['G', '2', '9', ['B_y']]]]
#formula = [['G', '0', '7', ['F', '1', '3', ['B_p']]]]

# Crea nuovi nodi così:
# formula = Node(*['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['F', '1', '3', ['B_p']]]]])
#formula = Node(*['&&', ['G', '0', '9', ['B_p']], ['F', '4', '7', ['B_q']]])


max_depth = 6

#formula = normalize_bounds(formula)
step = calculate_min_step(formula) #va poi inserito per fare i jump
#nested = check_nested(formula)
tree = build_decomposition_tree(formula, max_depth)
print(tree)
plot_tree(tree)


"""
Implementare i jump, osservazioni:
1)Se non ho op annidati (nested = False)  è facile, passo da un minimo al minimo successivo, tipo:
formula = [['&&', ['G', '0', '10', ['B_p']], ['F', '5', '8', ['B_q']]]]
faccio G in 0 e poi salto a 5, faccio G e F in 5 e poi salto a 8, faccio G e F in 8 e poi G nel resto

2) se ho operatori annidati GF o GG è un problema perché ad ogni istante di tempo si aggiunge un F (o G) e inizio a
trovare un pattern quando il primo F che si è generato decomponendo GF (o il primo G che si è generato decomponendo 
GG) esaurisce il suo intervallo e quindi i F smettono di aumentare. Devo avanzare di 1 in 1 almeno per l'orizz temp 
del F (o G) interno.

esempio:
G[0, 3] (F[1, 2] (B_p))

(O(G[0, 3] (F[1, 2] (B_p)))), (F[1, 2] (B_p))
                ...
(G[1, 3] (F[1, 2] (B_p))) , (F[2, 2] (B_p))  <-----
                ...
(O(G[1, 3] (F[1, 2] (B_p)))), (F[2, 2] (B_p)), (F[2, 3] (B_p)) (F[2,2] è esaurito è scompare al passaggio succ)
                ...
(G[2, 3] (F[1, 2] (B_p))) , (F[3, 3] (B_p))  <-----

3) se invece ho un FG (o FF), trovo la stessa espressione shiftata di un istante di tempo ad ogni salto temporale

F[0, 3] (G[1, 2] (B_p))   <-----

genera: O(F[0, 3] (G[1, 2] (B_p)))  E  G[1, 2] (B_p)

dal primo ottengo: F[1, 3] (G[1, 2] (B_p))    <-----

che di nuovo si divide in un ramo con OF e uno con G.
I rami con G hanno poi tutti la stessa evoluzione (che però inizia shiftata di 1 in avanti a mano a mano che scendo nell'albero)

Come implemento i salti?
Forse dovrei preprocessare la formula per stabilire a priori quando poter saltare (in teoria a seconda degli operatori che
ci sono nella formula e dei loro intervalli temporali, dovrebbe potersi stabilire a priori il numero minimo di 
istanti necessari per arrivare ad un nodo ripetuto (shiftato nel tempo di tot)

formula = [['&&', ['F', '0', '3', ['G', '1', '4', ['B_p']]], ['G', '0', '3', ['F', '0', '2', ['B_y']]]]]

(F[0, 3] (G[1, 4] (B_p))) , (G[1, 3] (F[0, 2] (B_y))) , (F[1, 2] (B_y))   <----

(F[1, 3] (G[1, 4] (B_p))) , (G[2, 3] (F[0, 2] (B_y))) , (F[2, 3] (B_y))   <---- Ottengo il nodo uguale all'istante 2
ovvero dopo 2 istanti di tempo che corrispondono al range temporale del F interno al FG (che è il maggior nella formula,
perché il GF si ripete ad ogni istante di tempo, come detto sopra).


SALTO NEI CASI COMPLICATI (GF, GG):
esempio: G[0,7]F[1,3]p && G[2,9]q

quando arrivo a:
G[2,7]F[1,3]p, F[3,3]p, F[3,4]p, G[3,9]q
decompongo (considero solo il ramo in cui skippo tutti i F):
OG[2,7]F[1,3]p, OF[3,3]p, OF[3,4]p, OF[3,5]p, OG[3,9]q, q
al salto successivo ottengo:
G[3,7]F[1,3]p, F[4,4]p, F[4,5]p, G[5,9]q (uguale al precedente, ma shiftato), a questo punto decompongo e poi posso saltare.
OG[3,7]F[1,3]p, OF[4,4]p, OF[4,5]p, OF[4,6]p, OG[4,9]q, q

QUINDI per saltare se ho una formula del tipo G[a,b]F[c,d] (o G[a,b]G[c,d]) devo aspettare che new_a sia == a + d
e a quel punto posso saltare di new_a* floor(b/new_a) [nel caso dell'esempio: 3*floor(7/3)=6]

QUANDO SALTI PERò NON è semplice, siccome salti da 3 a 6 (nel caso dell'esempio) devi aggiungere 3, ma in modo diverso 
per elementi diversi. Mi spiego:
1) all'operatore esterno del nesting aggiungi 3 SOLO al primo estremo dell'intervallo temporale esterno: G[6,7]F[1,3]p
2) agli operatori generati dalla decomposizione dell'operatore nested aggiungi 3 a ENTRAMBI gli estremi:
   F[7,7]p, F[7,8]p (non li aggiungo a OF[4,6] perché F[7,9] esce dalla decomposizione del nuovo GF: G[6,7]F[1,3]p)
3) agli operatori che non derivano da quello nested aggiungo 3 SOLO al primo estremo dell'intervallo: G[7,9]q

In definitiva dopo il salto ottengo:
G[6,7]F[1,3]p, F[7,7]p, F[7,8]p, G[7,9]q

che decomposto diventa

OG[6,7]F[1,3]p, OF[7,7]p, OF[7,8]p, OF[7,9]p, OG[7,9]q, q (ovvero OG[3,7]F[1,3]p, OF[4,4]p, OF[4,5]p, OF[4,6]p, OG[4,9]q, q)
shiftato in avanti


COSA succede invece se non riesco a saltare del passo calcolato? Mi spiego:

Se la formula iniziale fosse 
G[1,7]F[1,3]p (lascio perdere l'extra globally, perché non fa differenza)
avrei che posso saltare quando new_a == a + d e quindi a 4

ovvero: OG[4,7]F[1,3]p, OF[5,5]p, OF[5,6]p, OF[5,7]p

e posso saltare di new_a* floor(b/new_a) = 4*floor(7/4)= 4. Ma new_a+4=4+4=8 che è > b (=7). Cosa faccio??

Perché non posso direttamente saltare sempre all'ultimo istante???

Se saltassi all'ultimo istante avrei:
G[7,7]F[1,3]p, F[8,8]p, F[8,9]p che è corretto. Quindi mi sembra che una volta che arrivi a new_a == a + d tu possa sempre
arrivare direttamente all'istante finale, perché in quel lasso di tempo non ci sono differenze nel comportamento della
formula (a meno che ovviamente tu non abbia anche altri operatori oltre al nested che potrebbero interferire)

----------------------------------------------------------------------------------------------------------

Release Operator

p R q
meaning: q always holds, but it is released as soon as p holds 
(i.e.: q must remain true up to and including the moment when p becomes true (if there is one))

Cosa succede se inserisco i bound? p R[a,b] q

forse il significato è: q always holds (anche prima di a), but if p happens between a and b, then q is released. Therefore if p DOES NOT
happen between a and b, q keeps holding until the end
"""