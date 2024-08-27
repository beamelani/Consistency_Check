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
#NB: usa .extend invece di .append per riassemblare la lista dopo averne decomposta una parte

#PRIMA scrivo la funzione decompose e verifico che funzioni, poi cerco di integrarla alla funzione add children per
#creare l'albero

import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import graphviz_layout
import copy


def extract_min_time(formula):
    """
    Estrae l'istante di tempo minimo da una formula STL, serve per sapere a quale istante mi trovo
    durante la decomposizione
    """
    min_times = []
    if isinstance(formula, list):
        if len(formula) == 1:
            return extract_min_time(formula[0])
        for i in range(1, len(formula)):
            min_time = formula[i][1]
            min_times.append(min_time)
    return min(min_times)

def formula_to_string(formula):
    """

    :param formula: prende come input la lista
    :return: la trasforma nella stringa che verrà rappresentata nel nodo del tree
    """
    return

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
            return decompose_G()
        elif node[0] == 'F' and node[3][0] not in {'F', 'G'}:
            return decompose_F()
        elif node[0] == 'U':
            return decompose_U()
        #Caso nested
        elif node[0] in {'F', 'G'} and node[3][0] in {'F', 'G'}:
            return decompose_nested()
        #Jump
        elif node[0] == 'O': #se c'è un solo elemento non servono altre condizioni
            return decompose_jump(node)
        #Scrivo un nodo come una virgola (un and) di tutti gli elementi del nodo
        elif node[0] == ',':
            for j in range(1, len(node)):
                # Devo controllare se è un G, se è attivo (lowerb=current_time) e se non è nested
                # perché se è nested devo controllare se è attivo sommando i lb degli intervalli e poi di nuovo
                # sommare i lb degli intervalli quando estraggo l'argomento
                if node[j][0] == 'G' and node[j][1] == str(min_time) and node[j][3][0] not in {'G', 'F'}:
                    result = decompose_G(node[j]) #meglio passare una copia???
                    new_node = copy.deepcopy(node)
                    new_node.extend(result)
                    del new_node[j]
                    print(new_node)
                    return new_node
                elif node[j][0] == 'F' and node[j][1] == str(min_time) and node[j][3][0] not in {'G', 'F'}:
                    result = decompose_F(node[j], node, j)
                    print(result[0])
                    print(result[1])
                    return result
                elif node[j][0] == 'U'and node[j][1] == str(min_time):
                    return decompose_U()
                #Caso Nested:
                elif node[j][0] in {'G', 'F'} and node[j][3][0] in {'G', 'F'} and int(node[j][1]) + int(node[j][3][1]) == min_time:
                    return decompose_nested(node[j])
        else: #se arrivo qui vuol dire che non sono entrata in nessun return e quindi non c'era nulla da decomporre
            #perché era gia tutto decomposto o non ancora attivo
            counter = 0
            for i in range(1, len(node)): #controllo che ci sia almeno un 0, altrimenti non serve fare jump
                if node[i][0] == 'O':
                    counter += 1
            if counter > 0:
                return decompose_jump(node)
#Bisogna ancora aggiungere il JUMP
    return None #se non c'è niente da decomporre



def decompose_G(node):
    node = [['O', node], node[3]]
    return node


def decompose_F(node, formula, index):
    node_1 = [['0', node]]
    node_2 = [node[3]]
    formula_1 = copy.deepcopy(formula)
    formula_2 = copy.deepcopy(formula)
    del formula_1[index]
    del formula_2[index]
    formula_1.extend(node_1)
    formula_2.extend(node_2)
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


def decompose_or(node): #voglio che resituisca come liste SEPARATE le diverse sottoformule unite da || (perché dovranno essere children diversi nell'albero)
    for element in node[1:]:
        print(element)
        yield element


def decompose_nested():
    return


def decompose_jump(node):
    """

    :return: se niente può essere decomposto e c'è almeno un operatore O, devo fare il salto temporale
    """
    #Caso 1: ho un solo operatore, è quindi O è in posizione 0
    #Modifica questa versione (perché siccome devi togliere anche le cose come ['p'], è più facile scrivere la funzione
    #in modo che crei un nuovo nodo prendendo dal vecchio solo le cose che ci interessano, invece di modificare il nodo esistente
    if node[0] == 'O' and int(node[1][1]) < int(node[1][2]):
        node = node[1] #tolgo 'O'
        node[1][1] = str(int(node[1][1])+1)
    elif node [0] == ',':
        for i in range(1, len(node)):
            if node[i][0] == 'O' and int(node[i][1][1]) < int(node[i][1][2]):
                node[i] = node[i][1:]
    return

#Queste funzioni sono copiate dal vecchio codice, andranno riadattate
"""
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
            if children == None or len(flatten_list(children)) == 0:
                print('No more children in this branch')
                return
            else:
                #print(children)
                print(formula_to_string(children))
            for child in children:
                    counter = counter + 1
                    child_label = " ".join([formula_to_string(child), str(counter)])
                    G.add_node(child_label)
                    G.add_edge(node_label, child_label)
                    add_children(child, depth + 1, current_time)
    root_copy =copy.deepcopy(root)
    new_root = modify_formula(root_copy, time)
    if new_root != root[0]:
        counter = counter + 1
        new_root_label = " ".join([formula_to_string(new_root), str(counter)])
        G.add_node(new_root_label)
        G.add_edge(root_label, new_root_label)
    add_children(new_root, 0, time)
    return G


def plot_tree(G):
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=8, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()

"""
#formula = [['&&', ['G', '0', '2', ['p']], ['F', '1', '3', ['q']]]]
formula = [[',', ['G', '0', '2', ['p']], ['F', '1', '3', ['q']]]]
formula = [['G', '0', '3', ['F', '1', '4', ['p']]]]
max_depth = 10
min_time = extract_min_time(formula)
result = decompose(formula, min_time)
print(result)
#tree = build_decomposition_tree(formula, max_depth)
#print(tree)
#plot_tree(tree)