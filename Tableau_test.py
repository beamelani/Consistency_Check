import networkx as nx
import matplotlib.pyplot as plt



def formula_to_string(formula):
    if isinstance(formula, list):
        if len(formula) == 1:
            return formula_to_string(formula[0])
        elif len(formula) == 3 and formula[1] in ['&&', '||']:
            return f"({formula_to_string(formula[0])} {formula[1]} {formula_to_string(formula[2])})"
        elif formula[0] in ['G', 'F']:
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
        elif len(node) == 3 and isinstance(node[0], str) and isinstance(node[1], str) and isinstance(node[2], str):
            if node[1] in {'<', '<=', '>', '>=', '==', '!='}:
                return decompose_binary_relational(node[1], node[0], node[2])
        elif not isinstance(node[0], list):
            if node[0] in {'!'}:
                return decompose_unary_logical(node[0], node[1])
            elif node[0] in {'('} and node[len(node) - 1] in {')'}:
                return decompose_parenthesis(node[0], node[len(node) - 1], node[1])
            elif node[0] in {'G'}:
                if (int(node[2]) > int(node[4])):
                    raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                return decompose_G(node[0], node[2], node[4], node[6])
            elif node[0] in {'F'}:
                if (int(node[2]) > int(node[4])):
                    raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                return decompose_F(node[0], node[2], node[4], node[6])
            elif node[0] in {'OG', 'OF'}: #aggiungi condizioni, li decompongo solo nel jump
                return decompose_jump(node[0],node[1])
        elif isinstance(node[1], str):
            if node[1] in {'U'}:  # Temporal operators with two argument
                if (int(node[3]) > int(node[5])):
                    raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                return decompose_U(node[1], node[3], node[5], node[0], node[7])
            elif node[1] in {'&&'}:  # Binary logical operators
                #return decompose_and(node[1], node[0], node[2:])
                return decompose_and(node[1], node[0], node[2])
            elif node[1] in {'||'}:
                return decompose_or(node[1], node[0], node[2:])

    elif isinstance(node, str):
        return decompose_identifier(node)

def decompose_G(operator, time_interval_low, time_interval_high, expr):
    #ret = self.decompose(expr)
    decomposed_node = [[expr], ['OG', '[', time_interval_low,',',time_interval_high,']', [expr]]]
    return [decomposed_node]

def decompose_F(operator, time_interval_low, time_interval_high, expr):
    #ret = self.decompose(expr)
    decomposed_node_1 = [expr]
    decomposed_node_2 = ['OF', '[', time_interval_low,',',time_interval_high,']', expr]
    return [decomposed_node_1, decomposed_node_2]
def decompose_and(self, left, right):
    decomposed_node = [left, right]
    return [decomposed_node] #parentesi perché il child deve avere dim=1, altrimenti viene interpretato come 2 children distinti
def decompose_or(self, left, right):
    decomposed_node_1 = [left]
    decomposed_node_2 = [right]
    return [decomposed_node_1, decomposed_node_2]
#def decompose_comma(self, left, right):
    #return[decompose(left), right]
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

    def add_children(node, depth):
        if depth < max_depth:
            children = decompose(node)
            print(children)
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
max_depth = 6
tree = build_decomposition_tree(formula, max_depth)
print(tree)
plot_tree(tree)





















