#Queste funzioni andranno poi aggiunte al main che contiene già il parser che restituisce la formula stl
#nella forma utilizzata come input in questo codice.
#Cose ancora da fare:
#1) aggiungere l'until
#2)controlla bug nested, voglio che l'operatore interno sia sempre in una sottolista del tipo
# F[....[G...]]



import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import graphviz_layout
import copy


#Scrive la lista come stringa per metterla come nome del nodo
def formula_to_string(formula):  #HA DEI PROBLEMI
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
            if formula[0] in ('G', 'F', 'OG', 'OF', '_G', '_F') and formula[6][0] not in ('G', 'F', 'OG', 'OF', '_G', '_F'):
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
            elif formula[0] in ('G', 'F', 'OG', 'OF', '_G', '_F') and formula[6][0] in ('G', 'F', 'OG', 'OF', '_G', '_F'):
                try:
                    min_time = int(formula[2]) + int(formula[6][2])
                    min_times.append(min_time)
                except ValueError:
                    pass
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
    if isinstance(formula, list):
        if len(formula) == 1:
            return modify_formula(formula[0], current_time)
        for i in range(len(formula)):
            if isinstance(formula[i], str) and formula[i][0] in {'G', 'F'} and i+6 <= len(formula) and isinstance(formula[i+6][0], str) and formula[i+6][0] in {'G', 'F'} and int(formula[i+2]) + int(formula[i+6][2]) > current_time: #caso annidato
                formula[i] = '_' + formula[i]
                formula[i+6][0] = '_' + formula[i+6][0]
            elif isinstance(formula[i], str) and formula[i][0] in {'_G', '_F'} and i + 6 <= len(formula) and formula[i + 6][0] in {'_G', '_F'} and int(formula[i+2]) + int(formula[i+6][2]) <= current_time: #caso annidato
                formula[i][0] = formula[i][0].lstrip('_')
                formula[i + 6][0] = formula[i+6][0].lstrip('_')
            elif isinstance(formula[i], list) and isinstance(formula[i][0], str) and formula[i][0] in {'G', 'F'} and len(formula[i])>= 6 and isinstance(formula[i][6][0], str) and formula[i][6][0] in {'G', 'F'} and int(formula[i][2]) + int(formula[i][6][2]) > current_time:
                formula[i][0] = '_' + formula[i][0]
                formula[i][6][0] = '_' + formula[i][6][0]
            elif isinstance(formula[i], list) and isinstance(formula[i][0], str) and formula[i][0] in {'_G', '_F'} and len(formula[i]) >= 6 and formula[i][6][0] in {'_G', '_F'} and int(formula[i][2]) + int(formula[i][6][2]) <= current_time:
                formula[i][0] = formula[i][0].lstrip('_')
                formula[i][6][0] = formula[i][6][0].lstrip('_')
            elif isinstance(formula[i], list) and i+1 < len(formula) and formula[i+1] in {'&&', '||', ','} and isinstance(formula[i][0], str) and formula[i][0] in {'G', 'F', '_G','_F'}:
                if formula[i][0] in {'G', 'F'} and int(formula[i][2]) > current_time:
                    formula[i][0] = '_' + formula[i][0]
                elif formula[i][0] in {'_G', '_F'} and int(formula[i][2]) <= current_time:
                    formula[i][0] = formula[i][0].lstrip('_')
            elif isinstance(formula[i], list) and i-1 > 0 and formula[i-1] in {'&&', '||', ','} and isinstance(formula[i][0], str) and formula[i][0] in {'G', 'F', '_G', '_F'} and isinstance(formula[i][6][0], str) and formula[i][6][0] not in {'G', 'F', '_G', '_F'}:
                if formula[i][0] in {'G', 'F'} and int(formula[i][2]) > current_time:
                    formula[i][0] = '_' + formula[i][0]
                elif formula[i][0] in {'_G', '_F'} and int(formula[i][2]) <= current_time:
                    formula[i][0] = formula[i][0].lstrip('_')
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


def decompose(node, current_time):
    # Determine the type of the node and call the appropriate visit method
    if isinstance(node, list):
        if len(node) == 1:
            # Single element (either a terminal or a unary expression)
            if isinstance(node[0], str) and len(node[0]) == 1:
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
            #Questo vale solo a volte, perché?
            if isinstance(node[i][0], str) and len(node) >= 6 and node[i][0] in {'G', 'F'} and len(node) > i+6 and isinstance(node[i+6], list) and node[i+6][0] in {'F', 'G'}:
                if i != 0:
                    return decompose_nested(node[i:i+7], node[i+6], node[0:i-1], node[i+8:], current_time)
                if i == 0:
                    return decompose_nested(node[i:i+7], node[i+6], [], node[i+8:], current_time)
            #Questo vale se l'operatore interno annidato ha una sua sottolista
            if isinstance(node[i][0], str) and isinstance(node[i], list) and len(node[i]) >= 6 and node[i][0] in {'G', 'F'} and isinstance(node[i][6], list) and isinstance(node[i][6][0], str) and node[i][6][0] in {'G', 'F'}:
                if i != 0:
                    return decompose_nested(node[i], node[i][6], node[0:i-1], node[i+2:], current_time)
                elif i == 0:
                    return decompose_nested(node[i], node[i][6], [], node[i + 2:], current_time)
            if isinstance(node[i][0], str) and node[i][0] in {'G'}: #NB: Fai in modo che non si attivi per un annidato
                return decompose_G(node, current_time)
            #elif isinstance(node[i][0], list) and node[i][0][0] in {'G'} and node[i][0][0] not in {'O'}:
                #return decompose_G(node[i][0])
        for i in range(len(node)):
            if isinstance(node[i], list) and isinstance(node[i][0], str) and node[i][0] in {'F'}:
                if i != 0:
                    return decompose_F(node[i], node[0:i-1], node[i+2:], current_time)
                if i == 0:
                    return decompose_F(node[i], [], node[i + 2:], current_time)
            elif isinstance(node[i], str) and node[i] in {'F'}:
                if i != 0:
                    return decompose_F(node[i:i+7], node[0:i], node[i+8:], current_time)#left e right erano vuote per qualche ragione???
                if i == 0:
                    return decompose_F(node[i:i+7], [], node[i+8:], current_time)
        k = 0
        o = 0
        for i in range(len(flatten_list(node))): #check per vedere che tutto sia stato decomposto prima di fare il jump temporale
            if flatten_list(node)[i] not in {'G', 'F'}: #basta perché i G e F ancora inattivi vengono scritti come _G, _F
                k = k+1
                if flatten_list(node)[i] in {'OG', 'OF'}:
                    o = o+1
                if k == len(flatten_list(node)) and o != 0:
                    return decompose_jump(flatten_list(node), current_time)
                elif k == len(flatten_list(node)) and o == 0:
                    #metto la o per cotrollare se la formula ha operatori OG o OF, perché se ha solo op _G, _F e
                    # lettere, non devo fare salto temp, devo solo rimuovere lettere e attivare operatori _. Questa
                    # soluzione non va bene perché toglie _, ma non toglie le lettere
                    node = modify_formula(node, current_time)
                    return [[node]]
    elif isinstance(node, str):
        return None



def decompose_G(node, current_time):
    for i in range(len(node)):
        if i < len(node) and isinstance(node[i], list) and node[i][0] == 'G' and node[i][2] == str(current_time): #node[i][2]== time (perché decompongo G solo se è attivo)
            node[i] = [[node[i][6]], ',', ['OG', '[', node[i][2], ',', node[i][4], ']', [node[i][6]]]]
        elif i < len(node) and isinstance(node[i], str) and node[i] == 'G' and node[i+2] == str(current_time):
            node = [[node[6]], ',', ['OG', '[', node[i+2], ',', node[i+4], ']', [node[6]]]]
    return [node], current_time


def decompose_F(self, left, right, current_time):
    if len(left) > 0 and len(right) > 0:
        left = left[0] #controlla che non creino problemi
        right = right[0]
        decomposed_node_1 = [left, ',', right, ',', self[6]]
        decomposed_node_2 = [left, right, ',', ['OF', '[', self[2], ',', self[4], ']', self[6]]]
    elif len(left) == 0 and len(right) > 0:
        right = right[0]
        decomposed_node_1 = [self[6], ',', right]
        decomposed_node_2 = [['OF', '[', self[2], ',', self[4], ']', self[6]], ',', right]
    elif len(right) == 0 and len(left) > 0:
        left = left[0]
        decomposed_node_1 = [left, ',', self[6]]
        decomposed_node_2 = [left, ',', ['OF', '[', self[2], ',', self[4], ']', self[6]]]
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


def decompose_nested(self, argument, pre, post, current_time): #pre, post sono ciò che sta prima e dopo l'elemento nested e va riportato
    decomposed_node1 = []
    decomposed_node2 = []
    if self[0] in {'F'}:
        decomposed_node1 = [argument[0], '[', str(int(self[2]) + int(argument[2])), ',', str(int(self[2]) + int(argument[4])), ']', argument[6]]
        self[0] = 'OF'
        self[6][0] = 'O' + self[6][0] #marco anche operatore interno, così non viene decomposto erroneamente
        decomposed_node2 = self
        if not pre and not post:
            decomposed_node = [decomposed_node1, decomposed_node2]
        elif pre and post:
            pre = pre[0]
            post = post[0]
            decomposed_node1 = [pre, ',', decomposed_node1, ',', post]
            decomposed_node2 = [pre, ',', decomposed_node2, ',', post]
            decomposed_node = [decomposed_node1, decomposed_node2]
        elif pre and not post:
            pre = pre[0]
            decomposed_node1 = [pre, ',', decomposed_node1]
            decomposed_node2 = [pre, ',', decomposed_node2]
            decomposed_node = [decomposed_node1, decomposed_node2]
        elif post and not pre:
            post = post[0]
            decomposed_node1 = [decomposed_node1, ',', post]
            decomposed_node2 = [decomposed_node2, ',', post]
            decomposed_node = [decomposed_node1, decomposed_node2]
    elif self[0] in {'G'}:
        self[0] = 'OG'
        self[6][0] = 'O' + self[6][0] #non capisco perché aggiunge O anche ad argument
        decomposed_node1 = [argument[0], '[', str(int(self[2]) + int(argument[2])), ',', str(int(self[2]) + int(argument[4])), ']', argument[6], ',', self]
        decomposed_node1[0] = decomposed_node1[0].lstrip('O')
        if not pre and not post:
            decomposed_node = [decomposed_node1]
        elif pre and post:
            pre = pre[0]
            post = post[0]
            decomposed_node = [pre, ',', decomposed_node1, ',', post]
        elif pre and not post:
            pre = pre[0]
            decomposed_node = [pre, ',', decomposed_node1]
        elif post and not pre:
            post = post[0]
            decomposed_node = [decomposed_node1, ',', post]
    return decomposed_node, current_time

def decompose_jump(node, current_time): #bisogna aggiungere casi nested
    new_node = []
    for i in range(len(node)):
        #CASI NON NESTED
        if node[i] in {'OG'} and len(node) >= i+6 and node[i+6] not in {'OF', 'OG'} and int(node[i+2]) < int(node[i+4]):
            elemento = ['G', node[i+1], str(int(node[i+2])+1), node[i+3], node[i+4], node[i+5], [node[i+6]]]#probelma se argomento di G non è un solo elemento
            if new_node:
                new_node.append(',')
            new_node.append(elemento)
        elif node[i] in {'OF'} and len(node) >= i+6 and node[i+6] not in {'OF', 'OG'} and int(node[i+2]) < int(node[i+4]):
            elemento = ['F', node[i + 1], str(int(node[i + 2]) + 1), node[i + 3], node[i + 4], node[i + 5], [node[i + 6]]]  # i+6 compreso, verifica
            if new_node:
                new_node.append(',')
            new_node.append(elemento)
        elif node[i] in {'_G', '_F'} and len(node) >= i+6 and node[i+6] not in {'_F', '_G'}:
            if i != 0 and node[i-1] not in {']'}: #non voglio che sia l'operatore interno di un op annidato
                elemento = node[i:i+7]
                if new_node:  #condizione per cui aggiungo la virgola prima di aggiungere l'elemento solo se la lista non è vuota
                    new_node.append(',')
                new_node.append(elemento) #così poi mancano le virgole tra i diversi elementi
            elif i == 0:
                elemento = node[i:i+7]
                if new_node:
                    new_node.append(',')
                new_node.append(elemento)
        #CASI NESTED
        elif node[i] in {'OG'} and len(node) >= i+6 and node[i+6] in {'OF', 'OG'} and int(node[i+2]) < int(node[i+4]):
            node[i+6] = node[i+6].lstrip('O')
            elemento = ['G', node[i + 1], str(int(node[i + 2]) + 1), node[i + 3], node[i + 4], node[i + 5], node[i + 6:]] #non so se fare fino alla fine va sempre bene
            if new_node:
                new_node.append(',')
            new_node.append(elemento)
        elif node[i] in {'OF'} and len(node) >= i + 6 and node[i + 6] in {'OF', 'OG'} and int(node[i+2]) < int(node[i+4]):
            node[i+6] = node[i+6].lstrip('O')
            elemento = ['F', node[i + 1], str(int(node[i + 2]) + 1), node[i + 3], node[i + 4], node[i + 5], node[i + 6:]]  # non so se fare fino alla fine va sempre bene
            if new_node:
                new_node.append(',')
            new_node.append(elemento)
        elif node[i] in {'_G', '_F'} and len(node) >= i+6 and node[i+6] in {'_F', '_G'}:
            #node[i + 12] = [node[i + 12]]
            #elemento = node[i:i + 13]
            elemento = [node[i], '[', node[i+2], ',', node[i+4], ']', node[i+6:i+13]]
            if new_node:
                new_node.append(',')
            new_node.append(elemento)
    current_time = current_time + 1
    new_node = modify_formula(new_node, current_time)
    return [[new_node]]



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
            if children: #serve perché se children è vuoto non posso estrarre children[0]
                children = children[0]
            if children and len(flatten_list(children[0])) > 0:
                print(children)
                print(formula_to_string(children))
            else:
                print('No more children in this branch')
                return
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


# Esempio di formula e costruzione dell'albero
#OK formula = [[['G', '[', '0', ',', '2', ']', ['p']], '&&', ['F', '[', '1', ',', '3', ']', ['q']]]]
#OK formula = [[['G', '[', '0', ',', '3', ']', ['p']], '||', ['F', '[', '0', ',', '3', ']', ['q']]]]
#OK formula = ['G', '[', '0', ',', '3', ']', ['p']]
#OK formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
#OK formula = [[['G', '[', '0', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']], '||', ['G', '[', '0', ',', '5', ']', ['x']], '&&', ['F', '[', '0', ',', '2', ']', ['y']]]]
#formula = [[['a'], 'U', '[', '2', ',', '5', ']', ['b']]]
#formula = [[['G', '[', '0', ',', '5', ']', ['x']], '&&', [['a'], 'U', '[', '2', ',', '5', ']', ['b']]]]
#formula = [[[['a'], 'U', '[', '2', ',', '5', ']', ['b']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
#OK formula = [[['F', '[', '0', ',', '3', ']', ['q']], '&&', ['G', '[', '0', ',', '5', ']', ['x']]]]
#OK formula = [['F', '[', '0', ',', '5', ']', ['G', '[', '1', ',', '7', ']', ['a']]]] #OK
#formula = [['G', '[', '1', ',', '10', ']', ['F', '[', '1', ',', '7', ']', ['a']]]] #children sono ok, ma la funzione formula_to_string tronca l'espressione non so perché
#OK formula = [[['G', '[', '0', ',', '5', ']', ['b']], '&&', ['F', '[', '0', ',', '5', ']', ['G', '[', '1', ',', '7', ']', ['a']]]]] #NON FUNZIONA
#OK formula = [[['F', '[', '0', ',', '5', ']', ['G', '[', '1', ',', '7', ']', ['a']]], '&&' , ['G', '[', '0', ',', '5', ']', ['b']]]]
#formula = [[['G', '[', '2', ',', '3', ']', ['p']], '&&', ['F', '[', '0', ',', '3', ']', ['q']]]]
max_depth = 5
tree = build_decomposition_tree(formula, max_depth)
print(tree)
plot_tree(tree)





















