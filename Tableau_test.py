import networkx as nx
import matplotlib.pyplot as plt



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
            if node[i]=='&&':
                return decompose_and(node)
            elif node[i] =='||':
                return decompose_or(node[i], node[0:i], node[i+1:])
        for i in range(len(node)):
            if  isinstance(node[i][0], str) and node[i][0] in {'G'}:
                return decompose_G(node)
            elif isinstance(node[i][0], str) and node[i][0] in {'F'}:
                return decompose_F(node[i],node[0:i], node[i+1:])
    elif isinstance(node, str):
        return decompose_identifier(node)



def decompose_G(node):
    for i in range(len(node)):
        if node[i][0]=='G':
            node[i] = [node[i][6], ',', ['0G','[',node[i][2],',', node[i][4], ']',node[i][6]]]
    return [node]


def decompose_F(self, left, right):
    if len(left) > 0 and len(right) > 0:
        decomposed_node_1 = [left, right, ',', self[6]]
        decomposed_node_2 = [left, right, ',', ['OF', '[', self[2], ',', self[4], ']', self[6]]]
    elif len(left) == 0 and len(right) > 0:
        decomposed_node_1 = [self[6],right]
        decomposed_node_2 = [['OF', '[', self[2], ',', self[4], ']', self[6]], right]
    elif len(right) == 0 and len(left) > 0:
        decomposed_node_1 = [left, self[6]]
        decomposed_node_2 = [left, ['OF', '[', self[2], ',', self[4], ']', self[6]]]
    elif len(right) == 0 and len(left) == 0:
        decomposed_node_1 = [self[6]]
        decomposed_node_2 = ['OF', '[', self[2], ',', self[4], ']', self[6]]
    return [decomposed_node_1, decomposed_node_2]

def decompose_and(node):
    for i in range(len(node)):
        if node[i]== '&&':
            node[i] = ','
    return [node] #parentesi perché il child deve avere dim=1, altrimenti viene interpretato come 2 children distinti
def decompose_or(self, left, right):
    decomposed_node_1 = [left]
    decomposed_node_2 = [right]
    return [decomposed_node_1, decomposed_node_2]

def decompose_jump(self, right):
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
            children = decompose(node)
            print(formula_to_string(children))
            if not children: #devo ancora aggiungere la regola per il salto temporale, aggiunta quella non ho children solo quando ho esplorato tutto il ramo
                #new_value = update_intervals(node.value, 1)
                #new_node = STLNode(new_value)
                #G.add_node(new_node)
                #G.add_edge(node, new_node)
                #add_children(new_node, depth + 1)
                depth=max_depth
                add_children(node,depth)
            else:
                for child in children:
                    G.add_node(formula_to_string(child))
                    G.add_edge(formula_to_string(node), formula_to_string(child))
                    add_children(child, depth + 1)

    add_children(root, 0)
    return G

def plot_tree(G):
    pos = nx.spring_layout(G)
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=10, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()

# Esempio di formula e costruzione dell'albero
formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']]]]
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '||', ['F', '[', '0', ',', '3', ']', ['q']]]]
#formula = ['G', '[', '0', ',', '3', ']', ['p']]
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
#formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']], '||', ['G', '[', '0', ',', '5', ']', ['x']], '&&', ['F', '[', '0', ',', '2', ']', ['y']]]]
max_depth = 6
tree = build_decomposition_tree(formula, max_depth)
print(tree)
plot_tree(tree)





















