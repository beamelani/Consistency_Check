#Queste funzioni andranno poi aggiunte al main che contiene già il parser che restituisce la formula stl
#nella forma utilizzata come input in questo codice.
#Cose ancora da fare:
#1)aggiungere un controllo sugli istanti di tempo (per decomporre solo le sottoformule attive all'istante corrente)
#2)aggiungere il salto temporale
#3) aggiungere l'until
#4) operatori annidati
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
        elif isinstance(formula[0][0], str) and formula[0] in ['G', 'F', 'OG', 'OF']:
            return f"{formula[0]}[{formula[2]},{formula[4]}]({formula_to_string(formula[6])})"
        else:
            return ''.join(map(formula_to_string, formula))
    else:
        return str(formula)

def extract_min_time(formula):
    """
    Estrae l'istante di tempo minimo da una formula STL, serve per sapere a quale istante mi trovo
    durante la decomposizione
    """
    min_times = []

    def traverse(formula):
        if isinstance(formula, list):
            if formula[0] in ('G', 'F', 'OG', 'OF'):
                # Se l'elemento è un operatore temporale 'G' o 'F'
                if len(formula) > 4 and formula[1] == '[' and formula[3] == ',' and formula[5] == ']':
                    try:
                        min_time = int(formula[2])
                        min_times.append(min_time)
                    except ValueError:
                        pass
                # Ricorsivamente attraversa i sottooperatori
                for item in formula[4:]:
                    traverse(item)
            else:
                # Altri operatori, ricorsivamente attraversa la lista
                for item in formula:
                    traverse(item)

    traverse(formula)
    #return sum(min_times) if min_times else None  #devo restituire la somma solo se sono annidati
    return min(min_times) if min_times else None


def modify_formula(formula, current_time):
    """
    La funzione prende una formula e valuta per ogni operatore se l'operatore sia attivo o meno
    all'istante di tempo corrente, contrassegnando con _ gli operatori non attivi,
    in modo che non vengano decomposti dalla funzione decompose

    """
    if isinstance(formula,list):
        if len(formula) == 1:
            return modify_formula(formula[0],current_time)
        for i in range(len(formula)):
            if isinstance(formula[i], list):
                if len(formula[i]) > 1 and isinstance(formula[i][0], str):
                    if formula[i][0].startswith('_') and formula[i][2]== str(current_time):
                        formula[i][0] = formula[i][0][1:]  # Rimuove il prefisso '_'
                    if formula[i][0].startswith('G') and formula[i][2] != str(current_time):
                        formula[i][0] = '_G'
                    if formula[i][0].startswith('F') and formula[i][2] != str(current_time):
                        formula[i][0] = '_F'
    return formula


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
def decompose(node, current_time):
    # Determine the type of the node and call the appropriate visit method
    if isinstance(node, list):
        if len(node) == 1:
            # Single element (either a terminal or a unary expression)
            if isinstance(node[0], str) and len(node[0]) == 1:
                #return decompose_binary_variable(node[0])
                return None
            return decompose(node[0], current_time)
        for i in range(len(node)):
            if node[i] == '&&':
                return decompose_and(node, current_time)
            elif node[i] == '||':
                return decompose_or(node[i], node[0:i], node[i+1:], current_time)
        for i in range(len(node)):
            #if isinstance(node[i], list) and isinstance(node[i][1], str) and node[i][1] in {'U'} and node[i][2] in {'['}:
                #node[i] = [['G', '[', '0', ',', node[i][3], ']', node[i][0]], ',', ['F', '[', node[i][3], ',', node[i][5], ']', node[i][7]], ',', ['F', '[', node[i][3], ',', node[i][3], ']', [node[i][0], 'U', node[i][7]]]]
                #return [node]
            if isinstance(node[i][0], str) and node[i][0] in {'G'}: #aggiungi condizioni sul tempo
                return decompose_G(node, current_time)
            #elif isinstance(node[i][0], list) and node[i][0][0] in {'G'} and node[i][0][0] not in {'O'}:
                #return decompose_G(node[i][0])
        for i in range(len(node)):
            if isinstance(node[i][0], str) and node[i][0] in {'F'}: #aggiungi condizioni sul tempo
                return decompose_F(node[i], node[0:i], node[i+1:], current_time)
        k = 0
        for i in range(len(flatten_list(node))):
            if flatten_list(node)[i] not in {'G', 'F'}:
                k = k+1
                if k==len(flatten_list(node)):
                    return decompose_jump(flatten_list(node), current_time)
    elif isinstance(node, str):
        return None



def decompose_G(node, current_time):
    for i in range(len(node)):
        if i < len(node) and isinstance(node[i], list) and node[i][0] == 'G' and node[i][2] == str(current_time): #qui aggiungi condizione and node[i][2]== time (perché decompongo G solo se è attivo)
            node[i] = [[node[i][6]], ',', ['OG', '[', node[i][2], ',', node[i][4], ']', [node[i][6]]]]
        elif i < len(node) and isinstance(node[i], str) and node[i] == 'G':
            node = [[node[6]], ',', ['OG', '[', node[i+2], ',', node[i+4], ']', [node[6]]]]
    return [node], current_time


def decompose_F(self, left, right, current_time):
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
    return [decomposed_node_1, decomposed_node_2], current_time


def decompose_and(node, current_time):
    for i in range(len(node)):
        if node[i] == '&&':
            node[i] = ','
    return [node], current_time #parentesi perché il child deve avere dim=1, altrimenti viene interpretato come 2 children distinti


def decompose_or(self, left, right, current_time):
    decomposed_node_1 = [left]
    decomposed_node_2 = [right]
    return [decomposed_node_1, decomposed_node_2], current_time


def decompose_jump(node, current_time):
    #forse è meglio passare alla funzione la lista flat e poi sarà la funzione a inserire le parentesi dove servono
    #questa funzione dovrà anche modificare il parametro che indica qual è l'istante temporale corrente
    new_node = []
    for i in range(len(node)):
        if node[i] in {'OG'}:
            elemento = ['G', node[i+1], str(int(node[i+2])+1), node[i+3], node[i+4], node[i+5], [node[i+6]]]#probelma se argomento di G non è un solo elemento
            new_node.append(elemento)
        elif node[i] in {'OF'}:
            elemento = ['F', node[i + 1], str(int(node[i + 2]) + 1), node[i + 3], node[i + 4], node[i + 5], [node[i + 6]]]  # i+6 compreso, verifica
            new_node.append(elemento)
        elif node[i] in {'_G', '_F'}:
            elemento = [node[i:i+6]]
            new_node.append(elemento) #così poi mancano le virgole tra i diversi elementi
    #current_time = current_time + 1
    return [[new_node]]



def build_decomposition_tree(root, max_depth):
    G = nx.DiGraph()
    time = extract_min_time(root)
    G.add_node(formula_to_string(root))
    print(formula_to_string(root))

    def add_children(node, depth, current_time):
        if depth < max_depth:
            node_copy = copy.deepcopy(node)
            current_time = extract_min_time(node_copy)
            children = decompose(node_copy, current_time)[0]
            print(formula_to_string(children))
            if not children:  # devo ancora aggiungere la regola per il salto temporale, aggiunta quella non ho children solo quando ho esplorato tutto il ramo
                #new_value = update_intervals(node.value, 1)
                #new_node = STLNode(new_value)
                #G.add_node(new_node)
                #G.add_edge(node, new_node)
                #add_children(new_node, depth + 1)
                depth = max_depth
                add_children(node, depth, current_time)
            else:
                for child in children:
                    G.add_node(formula_to_string(child))
                    G.add_edge(formula_to_string(node), formula_to_string(child))
                    add_children(child, depth + 1, current_time)
    root_copy =copy.deepcopy(root)
    new_root = modify_formula(root_copy, time)
    if new_root != root[0]:
        G.add_node(formula_to_string(new_root))
        G.add_edge(formula_to_string(root), formula_to_string(new_root))
    add_children(new_root, 0, time)
    return G


def plot_tree(G):
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=8, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()


# Esempio di formula e costruzione dell'albero
formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']]]]
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '||', ['F', '[', '0', ',', '3', ']', ['q']]]]
#formula = ['G', '[', '0', ',', '3', ']', ['p']]
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']], '||', ['G', '[', '0', ',', '5', ']', ['x']], '&&', ['F', '[', '0', ',', '2', ']', ['y']]]]
#formula = [[['a'], 'U', '[', '2', ',', '5', ']', ['b']]]
#formula = [[['G', '[', '0', ',', '5', ']', ['x']], '&&', [['a'], 'U', '[', '2', ',', '5', ']', ['b']]]]
#formula = [[[['a'], 'U', '[', '2', ',', '5', ']', ['b']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
#formula = [[['F', '[', '0', ',', '3', ']', ['q']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
#formula = [['F', '[', '0', ',', '5', ']', ['G', '[', '1', ',', '7', ']', ['a']]]]
#formula = [[['G', '[', '3', ',', '5', ']', ['b']], '&&', ['F', '[', '0', ',', '5', ']', ['G', '[', '1', ',', '7', ']', ['a']]]]]
#formula = [[['G', '[', '2', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']]]]
max_depth = 5
tree = build_decomposition_tree(formula, max_depth)
print(tree)
plot_tree(tree)





















