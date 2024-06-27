#Queste funzioni andranno poi aggiunte al main che contiene già il parser che restituisce la formula stl
#nella forma utilizzata come input in questo codice.
#Cose ancora da fare:
#1)aggiungere un controllo sugli istanti di tempo (per decomporre solo le sottoformule attive all'istante corrente)
#2)aggiungere il salto temporale
#3) aggiungere l'until
#ISSUE: si creano troppe liste annidate durante la decomposizione, diventa un problema gestirle

import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import graphviz_layout
import copy


def formula_to_string(formula):
    if isinstance(formula, list):
        if len(formula) == 1:
            return formula_to_string(formula[0])
        elif len(formula) == 3 and formula[1] in ['&&', '||']:
            return f"({formula_to_string(formula[0])} {formula[1]} {formula_to_string(formula[2])})"
        elif isinstance(formula[0][0], str) and formula[0] in ['G', 'F','0G', 'OF']:
            return f"{formula[0]}[{formula[2]},{formula[4]}]({formula_to_string(formula[6])})"
        else:
            return ''.join(map(formula_to_string, formula))
    else:
        return str(formula)

def flatten_list(nested_list):
    """
    Appiattisce una lista annidata rimuovendo un livello di annidamento.
    """
    flat_list = []
    for item in nested_list:
        if isinstance(item, list):
            flat_list.extend(flatten_list(item))
        else:
            flat_list.append(item)
    return flat_list
#voglio modificare decompose in modo che lavori sulla lista e poi trasformi il contenuto del nodo in una stringa
#passandolo alla funzione formula_to_string
def decompose(node):
    # Determine the type of the node and call the appropriate visit method
    if isinstance(node, list):
        if len(node) == 1:
            # Single element (either a terminal or a unary expression)
            if isinstance(node[0], str) and len(node[0]) == 1:
                #return decompose_binary_variable(node[0])
                return None
            return decompose(node[0])
        for i in range(len(node)):
            if node[i] == '&&':
                return decompose_and(node)
            elif node[i] == '||':
                return decompose_or(node[i], node[0:i], node[i+1:])
        for i in range(len(node)):
            #if isinstance(node[i], list) and isinstance(node[i][1], str) and node[i][1] in {'U'} and node[i][2] in {'['}:
                #node[i] = [['G', '[', '0', ',', node[i][3], ']', node[i][0]], ',', ['F', '[', node[i][3], ',', node[i][5], ']', node[i][7]], ',', ['F', '[', node[i][3], ',', node[i][3], ']', [node[i][0], 'U', node[i][7]]]]
                #return [node]
            if isinstance(node[i][0], str) and node[i][0] in {'G'}: #aggiungi condizioni sul tempo
                return decompose_G(node)
            #elif isinstance(node[i][0], list) and node[i][0][0] in {'G'} and node[i][0][0] not in {'O'}:
                #return decompose_G(node[i][0])
        for i in range(len(node)):
            if isinstance(node[i][0], str) and node[i][0] in {'F'}: #aggiungi condizioni sul tempo
                return decompose_F(node[i], node[0:i], node[i+1:])
        for i in range(len(flatten_list(node))):
            if flatten_list(node)[i] not in {'G', 'F'}: #può andare se metto qualcosa davanti ai F e G inattivi in quel momento, tipo _F, _G
                return decompose_jump(node)
    elif isinstance(node, str):
        return None



def decompose_G(node):
    for i in range(len(node)):
        if node[i][0] == 'G': #qui aggiungi condizione and node[i][2]== time (perché decompongo G solo se è attivo)
            node[i] = [node[i][6], ',', ['0G', '[', node[i][2], ',', node[i][4], ']', node[i][6]]]
    return [node]


def decompose_F(self, left, right):
    if len(left) > 0 and len(right) > 0:
        decomposed_node_1 = [left[0: len(left)-1], ',', right[1:], ',', self[6]]
        decomposed_node_2 = [left[0: len(left)-1], right[1:], ',', ['OF', '[', self[2], ',', self[4], ']', self[6]]]
    elif len(left) == 0 and len(right) > 0:
        decomposed_node_1 = [self[6], ',', right[1:]]
        decomposed_node_2 = [['OF', '[', self[2], ',', self[4], ']', self[6]], ',', right[1:]]
    elif len(right) == 0 and len(left) > 0:
        decomposed_node_1 = [left[0: len(left)-1], ',', self[6]]
        decomposed_node_2 = [left[0: len(left)-1], ',', ['OF', '[', self[2], ',', self[4], ']', self[6]]]
    elif len(right) == 0 and len(left) == 0:
        decomposed_node_1 = [self[6]]
        decomposed_node_2 = ['OF', '[', self[2], ',', self[4], ']', self[6]]
    return [decomposed_node_1, decomposed_node_2]


def decompose_and(node):
    for i in range(len(node)):
        if node[i] == '&&':
            node[i] = ','
    return [node] #parentesi perché il child deve avere dim=1, altrimenti viene interpretato come 2 children distinti


def decompose_or(self, left, right):
    decomposed_node_1 = [left]
    decomposed_node_2 = [right]
    return [decomposed_node_1, decomposed_node_2]


def decompose_jump(node):
    #questa funzione dovrà anche modificare il parametro che indica qual è l'istante temporale corrente
    return None


def update_intervals(formula, increment):
    if "OG[" in formula or "OF[" in formula:
        temporal_operator = formula[:2]  # OG or OF
        interval = formula.split('[')[1].split(']')[0]
        start, end = interval.split(',')
        new_start = int(start) + increment
        new_interval = f"[{new_start},{end}]"
        phi = formula.split('](')[1][:-1]
        new_formula = f"{temporal_operator[1:]}{new_interval}({phi})"  # G or F with updated interval
        return new_formula
    return formula


def build_decomposition_tree(root, max_depth):
    G = nx.DiGraph()
    G.add_node(formula_to_string(root))
    print(formula_to_string(root))

    def add_children(node, depth):
        if depth < max_depth:
            node_copy = copy.deepcopy(node)
            children = decompose(node_copy)
            print(formula_to_string(children))
            if not children:  # devo ancora aggiungere la regola per il salto temporale, aggiunta quella non ho children solo quando ho esplorato tutto il ramo
                #new_value = update_intervals(node.value, 1)
                #new_node = STLNode(new_value)
                #G.add_node(new_node)
                #G.add_edge(node, new_node)
                #add_children(new_node, depth + 1)
                depth = max_depth
                add_children(node, depth)
            else:
                for child in children:
                    G.add_node(formula_to_string(child))
                    G.add_edge(formula_to_string(node), formula_to_string(child))
                    add_children(child, depth + 1)

    add_children(root, 0)
    return G


def plot_tree(G):
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=8, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()


# Esempio di formula e costruzione dell'albero
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']]]]
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '||', ['F', '[', '0', ',', '3', ']', ['q']]]]
#formula = ['G', '[', '0', ',', '3', ']', ['p']]
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']], '||', ['G', '[', '0', ',', '5', ']', ['x']], '&&', ['F', '[', '0', ',', '2', ']', ['y']]]]
#formula = [[['a'], 'U', '[', '2', ',', '5', ']', ['b']]]
#formula = [[['G', '[', '0', ',', '5', ']', ['x']], '&&', [['a'], 'U', '[', '2', ',', '5', ']', ['b']]]]
#formula = [[[['a'], 'U', '[', '2', ',', '5', ']', ['b']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
formula = [[['F', '[', '0', ',', '3', ']', ['q']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
max_depth = 6
tree = build_decomposition_tree(formula, max_depth)
print(tree)
plot_tree(tree)





















