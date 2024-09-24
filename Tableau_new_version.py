#Nuova versione del codice Tableau test che prende come input una lista del tipo:

"""
[['&&', 'sottof1', 'sottof2',...]]
|| come sopra
! come sopra
[['G', 'lowerb', 'upperb', 'arg']]
F come sopra
[['O', 'arg']]
[['U', 'lowerb', 'upperb', 'arg1', 'arg2']]
"""
import re

#NB: usa .extend invece di .append per riassemblare la lista dopo averne decomposta una parte

#PRIMA scrivo la funzione decompose e verifico che funzioni, poi cerco di integrarla alla funzione add children per
#creare l'albero

#Scrivi funzione che verifica se un nodo è uno stato ed estrae le espressioni atomiche e le codifica in un problema SMT.
#Prima dovrebbe verificare che non ci siano espressioni del tipo OF[a,a], in quel caso il nodo va rigettato senza nemmeno
#passare da SMT
import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import graphviz_layout
import copy
from z3 import *

def extract_min_time(formula):
    """
    Estrae l'istante di tempo minimo da una formula STL, serve per sapere a quale istante mi trovo
    durante la decomposizione

    """
    min_times = []
    if isinstance(formula, list):
        if len(formula) == 1:
            return extract_min_time(formula[0])
        if formula[0] in {'&&', '||', ','}:
            for i in range(1, len(formula)):
                if len(formula[i]) > 1 and formula[i][0] not in {'O'}:
                    if formula[i][3][0] in {'G', 'F'}: #caso nested, non O
                        min_time = str(int(formula[i][1]) + int(formula[i][3][1]))
                        min_times.append(min_time)
                    else:  #caso non nested e non O
                        min_time = formula[i][1]
                        min_times.append(min_time)
                elif len(formula[i]) > 1 and formula[i][0] in {'O'}:
                    if formula[i][1][3][0] in {'G', 'F'}: #caso nested,  O
                        min_time = str(int(formula[i][1][1]) + int(formula[i][1][3][1]))
                        min_times.append(min_time)
                    else: #caso non nested, O
                        min_time = formula[i][1][1]
                        min_times.append(min_time)
        elif formula[0] in {'G', 'F', 'U'}: #formula ha un solo elemento
            if formula[3][0] not in {'G', 'F'}: #caso non nested
                min_time = formula[1]
                min_times.append(min_time)
            else:
                min_time = str(int(formula[1]) + int(formula[3][1]))
                min_times.append(min_time)
        elif formula[0] in {'O'}: #formula ha un solo elemento in O
            if formula[1][3][0] not in {'G', 'F'}:
                min_time = formula[1][1]
                min_times.append(min_time)
            else: #caso nested
                min_time = str(int(formula[1][1]) + int(formula[1][3][1]))
                min_times.append(min_time)
    if min_times:
        return int(min(min_times))
    else:
        return None



def formula_to_string(formula):
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


"""
def formula_to_string(lista):
    elementi = []
    for elem in lista:
        if isinstance(elem, list):
            elementi.append(f'({formula_to_string(elem)})')
        else:
            elementi.append(str(elem))
    return ", ".join(elementi)
"""

def decompose(node, current_time):
    """

    :param node: lista da decomporre che ha la forma esplicitata sopra
    :param current_time: istante di tempo attuale, per capire quali operatori sono attivi e quali no
    :return: ritorna la lista decomposta (i.e. il successivo nodo del tree
    """
    if isinstance(node, list):
        if len(node) == 1:
            return decompose(node[0], current_time)
        if node[0] == '&&':
            return decompose_and(node)
        elif node[0] == '||':
            return decompose_or(node)
        #Se il nodo iniziale ha solo un elemento (quindi non è un and o or di più sottoformule) lo decompongo con i 5 elif di seguito
        elif node[0] == 'G' and node[3][0] not in {'F', 'G'}: #non credo che in questi serva controllare il tempo perché se ho un solo elemento è sicuramente attivo perché considero solo il suo intervallo temp
            return decompose_G(node, 1)
        elif node[0] == 'F' and node[3][0] not in {'F', 'G'}:
            return decompose_F(node, [], 0)
        elif node[0] == 'U':
            return decompose_U()
        #Caso nested
        elif node[0] in {'F', 'G'} and node[3][0] in {'F', 'G'}:
            return decompose_nested(node, [], 0)
        #Jump
        elif node[0] == 'O': #se c'è un solo elemento non servono altre condizioni
            return decompose_jump(node)
        #Scrivo un nodo come una virgola (un and) di tutti gli elementi del nodo
        elif node[0] == ',':
            counter = 0
            for j in range(1, len(node)):
                # Devo controllare se è un G, se è attivo (lowerb=current_time) e se non è nested
                # perché se è nested devo controllare se è attivo sommando i lb degli intervalli e poi di nuovo
                # sommare i lb degli intervalli quando estraggo l'argomento
                if node[j][0] == 'G' and node[j][1] == str(current_time) and node[j][3][0] not in {'G', 'F'}:
                    result = decompose_G(node[j], 0) #meglio passare una copia???
                    new_node = copy.deepcopy(node)
                    new_node.extend(result)
                    del new_node[j]
                    return [new_node]
                elif node[j][0] == 'F' and node[j][1] == str(current_time) and node[j][3][0] not in {'G', 'F'}:
                    result = decompose_F(node[j], node, j)
                    return result
                elif node[j][0] == 'U' and node[j][1] == str(current_time):
                    return decompose_U()
                #Caso Nested:
                elif node[j][0] in {'G', 'F'} and node[j][3][0] in {'G', 'F'} and int(node[j][1]) + int(node[j][3][1]) == current_time:
                    return decompose_nested(node[j], node, j)
                else: #se arrivo qui vuol dire che non sono entrata in nessun return e quindi non c'era nulla da decomporre
                    #perché l'elemento era già decomposto o non ancora attivo
                    counter += 1
        if counter == len(node) - 1: #-1 perché un elemento del nodo è la virgola
            #fai qui il check accept/reject, se rigetti non serve nemmeno fare il jump
            res = smt_check(node)
            if res is None:
                return None
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


def decompose_U():
    return


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
            extract[1] = str(int(node[1]) + int(extract[1])) #quando estraggo l'op annidato devo modificare l'intervallo temporale
            extract[2] = str(int(node[1]) + int(extract[2]))
            node = [[',', ['O', node], extract]]
            return node
        if node[0] == 'F':
            extract = copy.deepcopy(node[3])
            extract[1] = str(int(node[1]) + int(extract[1])) #quando estraggo l'op annidato devo modificare l'intervallo temporale
            extract[2] = str(int(node[1]) + int(extract[2]))
            res_1 = copy.deepcopy(node)
            res_1 = ['O', res_1]
            node = [res_1, extract]
            return node
    else:
        if node[0] == 'G':
            res_1 = copy.deepcopy(formula)
            del res_1[index] #tolgo il nested dalla formula
            extract = copy.deepcopy(node[3])
            extract[1] = str(int(node[1]) + int(extract[1]))  # quando estraggo l'op annidato devo modificare l'intervallo temporale
            extract[2] = str(int(node[1]) + int(extract[2]))
            node = [['O', node], extract]
            res_1.extend(node)
            return [res_1]
        elif node[0] == 'F':
            res_1 = copy.deepcopy(formula)
            res_2 = copy.deepcopy(formula)
            del res_1[index]
            del res_2[index]
            extract = copy.deepcopy(node[3])
            extract[1] = str(int(node[1]) + int(extract[1]))
            extract[2] = str(int(node[1]) + int(extract[2]))
            node = [['O', node]]
            res_1.extend(node)
            res_2.extend([extract])
            return [res_1, res_2] #ricontrolla se le parentesi vanno bene
    return


def decompose_jump(node):
    """
    dovrebbe essere ok: fa fare il salto agli elementi con 0, lascia come sono quelli con F,G non ancora attivi
    ed elimina il resto

    """
    #Caso in cui input sia della forma [',', [], [], ....] (un and di tante sottoformule)
    new_node = []
    if node[0] == ',':
        new_node = [',']
        for i in range(1, len(node)):
            if node[i][0] in {'F', 'G', 'U'}:
                new_node.extend([node[i]])
            elif node[i][0] in {'O'} and int(node[i][1][1]) < int(node[i][1][2]): #incremento solo se lb < ub
                sub_formula = copy.deepcopy(node[i][1]) #node[i][1] dovrebbe essere l'argomenti di 'O'
                sub_formula[1] = str(int(sub_formula[1])+1)
                new_node.extend([sub_formula])
        if len(new_node) == 2: #se uno degli elementi iniziale è della forma OG[x,x],
            # cioè ha esaurito l'intervallo e viene eliminato, è possibile  che rimanga un solo elemento, ma preceduto dalla virgola anche se non dovrebbe
            return [new_node[1]]
        elif new_node != [',']:
            return [new_node]
        else:
            return None
    else: #caso in cui ho una sola formula
        if int(node[1][1]) < int(node[1][2]):
            sub_formula = copy.deepcopy(node[1])  # node[1] dovrebbe essere l'argomenti di 'O'
            sub_formula[1] = str(int(sub_formula[1]) + 1)
            new_node.extend([sub_formula])
            return [new_node]
        else:
            return None

def smt_check(node):
    """
    NB : Potresti avere anche variabili Bool, qui setti tutte le variabili come Real
    :param node:
    :return: ritorna il nodo di partenza se è accepted, ritorna None se il nodo è rejected
    """
    new_node = []
    variabili_z3 = {}
    for i in range(len(node)):
        if node[i][0] == 'O' and node[i][1][0] in 'F' and node[i][1][1] == node[i][1][2]:
            print("node is rejected because finally was never satisfied")
            return None
        if node[i][0] not in {'O', 'F', 'G', 'U', ','}:
            new_node.extend(node[i])
    variabili = []
    vincoli = []
    for esp in new_node:
        #devo estrarre le espressioni e definirle in SMT tipo
        #x= Real('x')
        new_var = re.findall(r'\b[a-zA-Z_]\w*\b', esp)
        variabili.extend(new_var)
        for var in variabili:
            if var not in variabili_z3:
                variabili_z3[var] = Real(var)
        #Scrivere vincoli (in realtà sono già scritti in new node, bisogna solo inserirci le variabili z
        esp_z3 = esp
        for var in variabili_z3:
            esp_z3 = esp_z3.replace(var, f'variabili_z3["{var}"]')
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
        print("Node is rejected, expressions are incosistent")
        return None

def build_decomposition_tree(root, max_depth):
    G = nx.DiGraph()
    time = extract_min_time(root)
    counter = 0
    root_label = " ".join([formula_to_string(root), str(counter)])
    G.add_node(root_label)
    print(formula_to_string(root))

    def add_children(node, depth, current_time):
        nonlocal counter
        if depth < max_depth:
            node_copy = copy.deepcopy(node)
            current_time = extract_min_time(node_copy)
            node_label = " ".join([formula_to_string(node), str(counter)])
            children = decompose(node_copy, current_time)
            if children is None:
                print('No more children in this branch')
                return
            else:
                #print(children)
                print(formula_to_string(children))
            for child in children:
                    counter += 1
                    child_label = " ".join([formula_to_string(child), str(counter)])
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


#formula = [['&&', ['G', '0', '2', ['p']], ['F', '1', '3', ['q']]]] #ok
#formula = [['||', ['G', '0', '2', ['p']], ['F', '1', '3', ['q']]]] #ok
#formula = [['&&', ['F', '0', '2', ['p']], ['F', '1', '3', ['q']]]] #ok
#formula = [['G', '0', '3', ['F', '1', '4', ['p']]]] #credo venga giusto, ma non si capisce niente perché i nodi sono troppo appiccicati
#formula = [['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['p']]]]]
#formula = [['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['F', '1', '3', ['p']]]]]]
#formula = [['F', '0', '3', ['G', '1', '4', ['p']]]] #ok
#formula = [['&&', ['G', '0', '3', ['F', '1', '4', ['p']]], ['F', '1', '3', ['q']]]] #ok
formula = [['&&', ['G', '0', '4', ['x>5']], ['F', '2', '4', ['x<2']]]] #consistency check ok
#formula = [['&&', ['G', '0', '4', ['x>5']], ['F', '2', '4', ['y<2']]]] #consistency check ok
max_depth = 10

tree = build_decomposition_tree(formula, max_depth)
print(tree)
plot_tree(tree)