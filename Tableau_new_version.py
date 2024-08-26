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
        elif node[0] == 'G':
            return decompose_G()
        elif node[0] == 'F':
            return decompose_F()
        elif node[0] == 'U':
            return decompose_U()
        elif node[0] == ',':
            for j in range(1, len(node)):
                if node[j][0] == 'G' and node[j][1] == str(min_time):
                    result = decompose_G(node[j]) #meglio passare una copia???
                    new_node = copy.deepcopy(node)
                    new_node.extend(result)
                    del new_node[j]
                    print(new_node)
                    return new_node
                elif node[j][0] == 'F'and node[j][1] == str(min_time):
                    result = decompose_F(node[j], node, j)
                    print(result[0])
                    print(result[1])
                    return result
                elif node[j][0] == 'U'and node[j][1] == str(min_time):
                    return decompose_U()

    return



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


def decompose_jump():
    """

    :return: se niente può essere decomposto e c'è almeno un operatore O, devo fare il salto temporale
    """
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
max_depth = 10
min_time = extract_min_time(formula)
result = decompose(formula, min_time)
print(result)
#tree = build_decomposition_tree(formula, max_depth)
#print(tree)
#plot_tree(tree)