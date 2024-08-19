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

import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import graphviz_layout
import copy


def extract_min_time(formula):
    """
    Estrae l'istante di tempo minimo da una formula STL, serve per sapere a quale istante mi trovo
    durante la decomposizione
    """
    return

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
    return


def decompose_G():
    return


def decompose_until():
    return


def decompose_and():
    return


def decompose_or():
    return


def decompose_nested():
    return


def decompose_jump():
    """

    :return: se niente può essere decomposto e c'è almeno un operatore O, devo fare il salto temporale
    """
    return

#Queste funzioni sono copiate dal vecchio codice, andranno riadattate
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


formula = [['&&', ['G', '0', '2', ['p']], ['F', '1', '3', ['q']]]]
max_depth = 10
tree = build_decomposition_tree(formula, max_depth)
print(tree)
plot_tree(tree)