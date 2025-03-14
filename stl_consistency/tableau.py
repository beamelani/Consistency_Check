# MIT License
#
# Copyright (c) 2024 Ezio Bartocci, Michele Chiari, Beatrice Melani
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import graphviz_layout
import bisect
import concurrent.futures as fs
from stl_consistency.node import Node
from stl_consistency.local_solver import LocalSolver


def push_negation(node):
    if node.operator == '!':
        operand = node[0]
        match operand.operator:
            case 'P':
                return node
            case '!':
                return push_negation(operand[0])

        new_node = operand.shallow_copy()
        match operand.operator:
            case ',' | '&&':
                new_node.operator = '||'
                new_node.operands = [push_negation(Node('!', op)) for op in operand]
            case '||':
                new_node.operator = ','
                new_node.operands = [push_negation(Node('!', op)) for op in operand]
            case '->':
                new_node.operator = ','
                new_node.operands = [operand[0], push_negation(Node('!', operand[1]))]
            case 'O':
                new_node.operator = operand.operator
                new_node.operands = [push_negation(Node('!', operand[0]))]
            case 'G':
                new_node.operator = 'F'
                new_node.lower, new_node.upper = operand.lower, operand.upper
                new_node.operands = [push_negation(Node('!', operand[0]))]
            case 'F':
                new_node.operator = 'G'
                new_node.lower, new_node.upper = operand.lower, operand.upper
                new_node.operands = [push_negation(Node('!', operand[0]))]
            case 'U':
                new_node.operator = 'R'
                new_node.lower, new_node.upper = operand.lower, operand.upper
                new_node.operands = [push_negation(Node('!', operand[0])), push_negation(Node('!', operand[1]))]
            case 'R':
                new_node.operator = 'U'
                new_node.lower, new_node.upper = operand.lower, operand.upper
                new_node.operands = [push_negation(Node('!', operand[0])), push_negation(Node('!', operand[1]))]
            case _:
                raise ValueError('Bad formula')
        return new_node
    elif node.operator == 'P':
        return node
    else:  # Any non-negated operator
        new_node = node.shallow_copy()
        new_node.operands = [push_negation(op) for op in node.operands]
        return new_node

def extract_time_instants(formula, flag):
    """
    :return: funzione che restituisce gli estremi di tutti gli intervalli della formula in un vettore ordinato
    (non quelli degli op derivati, eccezione se op is_derived è estratto da -> o ||)
    """
    if flag:
        time_instants = []
        if formula.operator not in {'P'}:
            for elem in formula:
                if elem.operator not in {'P'}:
                    if elem.operator in ['G', 'F', 'U', 'R'] and not elem.is_derived:
                        # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                        time_instants.append(elem.lower)
                        time_instants.append(elem.upper)
                    #caso in cui op is_derived è estratto da un -> che era dentro a un G o U o R (flag == True)
                    elif elem.operator in ['G', 'F', 'U', 'R'] and elem.is_derived and (not elem.id_implication == -1 or not elem.or_element == -1):
                        time_instants.append(elem.lower)
                        time_instants.append(elem.upper) #va fatto anche nel caso 'O' ??
                    elif elem.operator in ['O'] and not elem.operands[0].is_derived:
                        time_instants.append(elem.operands[0].lower)
                        time_instants.append(elem.operands[0].upper)
    else:
        time_instants = []
        if formula.operator not in {'P'}:
            for elem in formula:
                if elem.operator not in {'P'}:
                    if elem.operator in ['G', 'F', 'U', 'R']:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                        time_instants.append(elem.lower)
                        time_instants.append(elem.upper)
                    elif elem.operator in ['O']:
                        time_instants.append(elem.operands[0].lower)
                        time_instants.append(elem.operands[0].upper)
    assert all(isinstance(t, int) for t in time_instants)
    time_instants = sorted(time_instants)
    return time_instants


def assign_identifier(formula):
    '''
    :param formula:
    :return: la formula assegna un identificatore agli operatori nested, in modo che nella decomposizione gli operatori
    derivati dalla decomposizione di un nested siano riconducibili all'operatore originario
    '''
    counter = 0
    if formula.operator in {'&&', '||', ',', '->'}:
        for operand in formula.operands:
            if operand.operator in {'G', 'F'} and operand.operands[0].operator not in {'P', '!'}:
                operand.identifier = counter
                counter += 1
            elif operand.operator in {'U', 'R'} and (
                    operand.operands[0].operator not in {'P', '!'} or operand.operands[1].operator not in {'P', '!'}):
                operand.identifier = counter
                counter += 1
    elif formula.operator in {'G', 'F', 'U', 'R'}:
        if formula.operator in {'G', 'F'} and formula.operands[0].operator not in {'P', '!'}:
            formula.identifier = counter
            counter += 1
        elif formula.operator in {'U', 'R'} and (
                formula.operands[0].operator not in {'P', '!'} or formula.operands[1].operator not in {'P', '!'}):
            formula.identifier = counter
            counter += 1
    return formula

# TODO Can we merge this with assign_identifier?
def assign_real_expr_id(node):
    id_counter = 0
    # We use a list instead of a set because lists (node.operands) are unhashable
    already_assigned = []

    def do_assign(node):
        nonlocal id_counter
        if node.operator == 'P' and len(node.operands) > 1:
            prev_id = next(filter(lambda expr_id: expr_id[0] == node.operands, already_assigned), None)
            if prev_id:
                node.real_expr_id = prev_id[1]
            else:
                node.real_expr_id = id_counter
                already_assigned.append((node.operands, id_counter))
                id_counter += 1
        elif node.operator != 'P':
            for operand in node.operands:
                do_assign(operand)

    do_assign(node)


def has_temporal_operator(node):
    '''
    :param node: Node containing a formula
    :return: True if the formula contains any temporal operator
    '''
    match node.operator:
        case 'G' | 'F' | 'U' | 'R':
            return True
        case '&&' | '||' | ',' | '!' | '->':
            return any(has_temporal_operator(operand) for operand in node)
    return False

def flagging(node):
    '''
    :param node:
    :return: True if the node contains any `problematic` operators
    '''
    match node.operator:
        case ',' | '&&' | '||' | '!' | '->':
            return any(flagging(operand) for operand in node)
        case 'O':
            match node[0].operator:
                case 'G' | 'U':
                    return has_temporal_operator(node[0][0])
                case 'R':
                    return has_temporal_operator(node[0][1])
            return False
    return False


def decompose(tableau_data, local_solver, node, current_time):
    """
    :param node: nodo da decomporre che ha operatore ','
    :param current_time: istante di tempo attuale, per capire quali operatori sono attivi e quali no
    :return: ritorna la lista decomposta (i.e. il successivo nodo del tree)
    """
    # fai qui il check accept/reject, se rigetti non serve andare avanti
    if not local_consistency_check(local_solver, node):
        return ['Rejected']

    res, has_decomposed = decompose_and(node)
    if has_decomposed:
        return res
    
    res, has_decomposed = decompose_all_G_nodes(node, current_time)
    if has_decomposed:
        return res

    res = None
    for j in range(len(node.operands)):
        match node.operands[j].operator:
            case '||':
                res = decompose_or(node, j)
                break
            case '->':
                if tableau_data.mode == 'complete' or tableau_data.mode == 'sat':
                    res = decompose_imply_classic(node, j)
                else:
                    res = decompose_imply_new(node, j)
                break
            case 'F':
                if node.operands[j].lower == current_time:
                    res = decompose_F(node, j)
                    break
            case 'U':
                if node.operands[j].lower == current_time:
                    res = decompose_U(node, j)
                    break
            case 'R':
                if node.operands[j].lower == current_time:
                    res = decompose_R(node, j)
                    break

    if res is not None:
        for child in res:
            child.current_time = node.current_time
        return res

    # se arrivo qui vuol dire che non sono entrata in nessun return e quindi non c'era nulla da decomporre
    return decompose_jump(node)


def decompose_all_G_nodes(outer_node, current_time):
    """
    Decompone tutti i nodi G nella formula con lower bound uguale a current_time.
    """
    assert outer_node.operator == ','
    # Funzione interna ricorsiva per modificare l'argomento
    def modify_argument(arg, G_node, identifier, short, simple):
        if arg.operator in {'P', '!'}:
            return arg
        elif simple and arg.operator == 'F' and G_node.lower + 2 <= G_node.upper:
            # We expand with the equivalence G[a,b]F[c,d] q = (F[a+c+1,a+d] q || (G[a+c,a+c] q && G[a+d+1,a+d+1] q)) && G[a+2,b]F[c,d] q
            a = G_node.lower
            c, d = arg.lower, arg.upper
            q = arg.operands[0]
            G_node.lower += 1 # this implements G[a+2,b]F[c,d] q because decompose_jump adds 1 again
            return Node('||', Node('F', a+c+1, a+d, q), Node(',', Node('G', a+c, a+c, q), Node('G', a+d+1, a+d+1, q)))
        elif arg.operator in {'U', 'R', 'F'} or (arg.operator == 'G' and (not short or G_node.lower == G_node.initial_time)):
            # Modifica bounds sommando quelli del nodo G
            extract = arg.shallow_copy()
            extract.lower = arg.lower + lower_bound
            extract.upper = arg.upper + lower_bound
            extract.is_derived = G_node.lower < G_node.upper
            extract.identifier = identifier
            return extract
        elif short and arg.operator == 'G' and G_node.lower > G_node.initial_time: #non aggiungo un altro G, ma allungo intervallo di quello già esistente
            G_counter = 0
            for i, operand in enumerate(outer_node.operands):
                if operand.operator == 'G' and operand.is_derived and operand.identifier == G_node.identifier and operand.and_element == arg.and_element:
                    outer_node.operands[i] = operand.shallow_copy()
                    outer_node.operands[i].upper += 1
                    G_counter += 1
                    if G_node.lower == G_node.upper:
                        outer_node.operands[i].is_derived = False
                elif operand.operator == 'O' and operand.operands[0].operator == 'G' and operand.operands[0].is_derived and operand.operands[0].identifier == G_node.identifier and operand.operands[0].and_element == arg.and_element:
                    operand.operands[0] = operand.operands[0].shallow_copy()
                    operand.operands[0].upper += 1
                    G_counter += 1
                    if G_node.lower == G_node.upper:
                        operand.operands[0].is_derived = False
            if G_counter == 0:
                extract = arg.shallow_copy()
                extract.lower = arg.lower + lower_bound
                extract.upper = arg.upper + lower_bound
                extract.is_derived = True
                extract.identifier = identifier
                return extract
            else:
                return None # non ritorno niente perché è bastato modificare il nodo esistente
        elif arg.operator in {'&&', ','}:
            # Applica la modifica ricorsivamente agli operandi
            arg = arg.shallow_copy()
            new_operands = (modify_argument(op, G_node, identifier, short, False) for op in arg.operands)
            arg.operands = [x for x in new_operands if x is not None]
            if arg.operands:
                return arg
            else:
                return None
        elif arg.operator in {'||', '->'}:
            arg = arg.shallow_copy()
            new_operands = (modify_argument(op, G_node, identifier, False, False) for op in arg.operands)
            arg.operands = [x for x in new_operands if x is not None]
            return arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

    outer_node = outer_node.shallow_copy()
    G_nodes = []
    for i, operand in enumerate(outer_node.operands):
        if operand.operator == 'G' and operand.lower == current_time:
            # We need a shallow_copy for GF because it changes operand.lower
            new_operand = operand.shallow_copy() if operand[0].operator == 'F' else operand
            G_nodes.append(new_operand)
            if operand.lower < operand.upper:
                # Sostituisco con ['O', ['G', 'a', 'b', ['p']]]
                outer_node.operands[i] = Node('O', new_operand)
            else:
                # Setto jump1 a True se necessario
                if (operand[0].check_boolean_closure(lambda n: n.operator == 'P') and
                    any(other.lower == operand.lower for j, other in enumerate(outer_node.operands) if (j != i and other is not None))):
                    outer_node.jump1 = True
                # Elimino l'elemento se a == b
                outer_node.operands[i] = None
    outer_node.operands = [x for x in outer_node.operands if x is not None]

    for G_node in G_nodes:
        lower_bound = G_node.lower
        identifier = G_node.identifier
        #initial_time = node.initial_time
        # a volte se il G annidato viene dalla dec di un altro op annidato diverso da G (tipo F), non ha l'initial time settato
        if G_node.initial_time == '-1':
            set_initial_time(G_node)
        # Decomponi il nodo originale
        new_operands = modify_argument(G_node.operands[0], G_node, identifier, True, True)
        if new_operands:
            outer_node.operands.append(new_operands)
    return [outer_node], len(G_nodes) > 0


def decompose_F(node, index):
    assert index >= 0 and node is not None

    F_formula = node[index]
    lower_bound = F_formula.lower
    current_time = F_formula.current_time

    # Funzione interna ricorsiva per modificare l'argomento
    def modify_argument(arg):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modifica bounds sommando quelli del nodo G
            extract = arg.shallow_copy()
            extract.lower = arg.lower + lower_bound
            extract.upper = arg.upper + lower_bound
            extract.current_time = current_time
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Applica la modifica ricorsivamente agli operandi
            new_arg = arg.shallow_copy()
            new_arg.operands = [modify_argument(op) for op in arg.operands]
            return new_arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

    # Node where we postpone satisfaction of F
    new_node1 = node.shallow_copy()
    new_node1.replace_operand(index, Node('O', F_formula))

    # Node where the operand holds
    new_node2 = node.shallow_copy()
    new_node2.replace_operand(index, modify_argument(F_formula.operands[0]))

    return new_node2, new_node1 #conviene fare prima return del node_2


def decompose_U(formula, index):
    '''
    NB: versione senza i DEEPCOPY
    Potrei decomporlo dicende che all'istante 2 può succedere p o q, se succede q il req è già soddisfatto e non mi interessa
    più cosa succede dopo (posso eliminare U da quel ramo. Mentre se succede p dovrò riportare che voglio avere pU[3,5]q all'ora all'istante successivo può succedere di nuovo p,
    oppure può succedere q e così via fino a 5, se a 5 è sempre successo p e mai q elimino il ramo perché U non è soddisfatto
    :return:
    pUq diventa q OR p and OU
    '''
    assert index >= 0 and formula is not None
    U_formula = formula[index]
    first_operand = formula[index].operands[0]
    second_operand = formula[index].operands[1]
    lower_bound = U_formula.lower
    current_time = U_formula.current_time
    def modify_argument(arg, derived):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modifica bounds sommando quelli del nodo
            extract = arg.shallow_copy()
            extract.lower = arg.lower + lower_bound
            extract.upper = arg.upper + lower_bound
            extract.current_time = current_time
            extract.identifier = U_formula.identifier
            if derived:
                extract.is_derived = True
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Applica la modifica ricorsivamente agli operandi
            new_arg = arg.shallow_copy()
            new_arg.operands = [modify_argument(op, derived) for op in arg.operands]
            return new_arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

    # If the U operator comes from the argument of another operator, its initial time may not be set
    if U_formula.initial_time == '-1':
            set_initial_time(U_formula)

    # Node in which U is not satisfied (p, OU)
    new_node1 = formula.shallow_copy()
    new_operand = modify_argument(first_operand.shallow_copy(), True) #derived indica se is_derived deve essere True (quindi è vero nel nodo con p, OU quando p è G,F...)
    new_node1.replace_operand(index, Node('O', U_formula))
    new_node1.operands.extend([new_operand])
    # Node where U is satisfied (q)
    new_node2 = formula.shallow_copy()
    new_node2.replace_operand(index, modify_argument(second_operand.shallow_copy(), False))

    return [new_node2, new_node1]



def decompose_R(formula, index):
    '''
    NB: questo fa SOLO da a in poi, per la parte prima di a aggiungo un F[0,2]p nel pre-processing
    p R[a,b] q
    q always holds in [a, b], but if p holds in a position t'' before b, then q holds from a to t''
    Quindi se p succede prima di a, allora q non è mai vero: quindi tra 0 e a ho che se succede p, allora non avrò mai q
    quindi se succede p, puoi cancellare il R dalla formula
    :return:    p R[a,b] q diventa: (q and O(pRq)) OR p
    '''
    assert index >= 0 and formula is not None
    R_formula = formula[index]
    first_operand = formula[index].operands[0]
    second_operand = formula[index].operands[1]
    lower_bound = R_formula.lower
    current_time = R_formula.current_time

    def modify_argument(arg, derived):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modifica bounds sommando quelli del nodo
            extract = arg.shallow_copy()
            extract.lower = arg.lower + lower_bound
            extract.upper = arg.upper + lower_bound
            extract.current_time = current_time
            extract.identifier = R_formula.identifier
            if derived:
                extract.is_derived = True
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Applica la modifica ricorsivamente agli operandi
            new_arg = arg.shallow_copy()
            new_arg.operands = [modify_argument(op, derived) for op in arg.operands]
            return new_arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

    # If the R operator comes from the argument of another operator, its initial time may not be set
    if R_formula.initial_time == '-1':
            set_initial_time(R_formula)

    # Node in which U is not satisfied (q, OU)
    new_node1 = formula.shallow_copy()
    if R_formula.lower < R_formula.upper:
        # derived indica se is_derived deve essere True (quindi è vero nel nodo con p, OU quando p è G,F...)
        new_operand = modify_argument(second_operand.shallow_copy(), True)
        new_node1.replace_operand(index, Node('O', R_formula))
        new_node1.operands.extend([new_operand])
    else:
        new_operand = modify_argument(second_operand.shallow_copy(), False)
        new_node1.replace_operand(index, new_operand)
        for operand in new_node1.operands:  # quando R va via tolgo is_derived dagli operatori
            if operand.is_derived and operand.identifier == R_formula.identifier:
                operand.is_derived = False
        if (second_operand.check_boolean_closure(lambda n: n.operator == 'P') and
            any(op.lower == R_formula.lower for j, op in enumerate(new_node1.operands) if j != index)):
            new_node1.jump1 = True

    # Node where U is satisfied (p)
    new_node2 = formula.shallow_copy()
    new_node2.replace_operand(index, modify_argument(first_operand.shallow_copy(), False), modify_argument(second_operand.shallow_copy(), False))

    return [new_node2, new_node1]

def decompose_and(node):
    assert node.operator == ','
    new_node = node.shallow_copy()
    # We decomose all AND operators, but only at the first level
    has_decomposed = False
    for i, operand in enumerate(node.operands):
        if operand.operator in {'&&', ','}:
            new_node.replace_operand(i, *operand.operands)
            has_decomposed = True

    return [new_node], has_decomposed


def decompose_or(node, index):
    assert index >= 0 and node is not None
    # Funzione di ordinamento basata sulla complessità
    def complexity_score(or_node, node):
        def check_match(sub1, sub2):
            return sub1.operator == sub2.operator and ((sub1.operator == 'P' and sub1.operands == sub2.operands) or (
                        sub1.operator == '!' and sub1[0].operands == sub2[0].operands))
        """Calcola un punteggio di complessità per ordinare i nodi, penalizzando gli annidamenti temporali."""
        # 1. Operatori con solo 'P' → Migliori
        if or_node.operator in {'P', '!'}:
            for operand in node.operands:
                if check_match(or_node, operand):
                    return -1 #se operatore di OR è uguale ad un operatore del node, restituisco score + basso almeno viene messo per primo
            return 0
        if or_node.operator in {'&&', ','} and all(op.operator == 'P' for op in or_node.operands):
            return 1
        if or_node.operator == '->' and all(op.operator == 'P' for op in or_node.operands):
            return 2
        if or_node.operator == '||' and all(op.operator == 'P' for op in or_node.operands):
            return 3

        # 2. Operatori temporali senza annidamenti complessi
        if or_node.operator in {'G', 'F', 'U', 'R'}:
            # Penalizzo in base all'orizzonte temporale
            score = 10 + (or_node.upper - or_node.lower)

            # Penalizzazione extra se l'operando è un altro temporale
            if or_node.operator == 'G' and or_node.operands[0].operator in {'G', 'F', 'U', 'R'}:
                score += 20  # G annidato → peggior caso
            elif or_node.operator == 'U' and or_node.operands[0].operator in {'G', 'F', 'U', 'R'}:
                score += 15  # U con temporale nel primo operand → peggio
            elif or_node.operator == 'R' and or_node.operands[1].operator in {'G', 'F', 'U', 'R'}:
                score += 15  # R con temporale nel secondo operand → peggio

            return score

        # 3. Operatori logici misti (nessun solo P)
        if or_node.operator == '->':
            return 30 + len(or_node.operands)
        elif or_node.operator == '&&':
            return 40 + len(or_node.operands)
        elif or_node.operator == '||':
            return 50 + len(or_node.operands)
        elif or_node.operator == ',':
            return 60 + len(or_node.operands)
        
        raise ValueError(f"Operatore non gestito: {or_node.operator}")

    # voglio creare un nodo figlio per ogni operand dell'OR, nodo che contiene l'operand dell'or + il resto del nodo padre (tolto l'or)
    res = []
    # Ordino i nodi secondo l’euristica
    #for or_operand in sorted(node[index].operands, key=complexity_score):
    for or_operand in sorted(node[index].operands, key=lambda op: complexity_score(op, node)):
        new_node = node.shallow_copy()
        if or_operand.is_derived and or_operand.or_element > -1:
            z = 0
            for element in new_node.operands:
                if element.operator == 'G' and element.identifier == or_operand.identifier and element.or_element == or_operand.or_element:
                    z += 1
                    element.upper = or_operand.upper
                elif element.operator == 'O' and element.operands[0].operator == 'G' and element.operands[0].is_derived and element.operands[0].identifier == or_operand.identifier and element.operands[0].or_element == or_operand.or_element:
                    z += 1
                    element.operands[0].upper = or_operand.upper
            if z == 0: #se il G non era ancora mai stato estratto
                new_node.replace_operand(index, or_operand)
            else:
                # We modified some exisiting G, so we don't need to add more formulas
                del new_node.operands[index]
        else:
            new_node.replace_operand(index, or_operand)
        res.append(new_node)
    return res


def decompose_imply_classic(node, index):
    '''
    :return: decompone p->q come not(p) OR (p and q), senza evitare il caso vacuously true
    '''
    assert index >= 0 and node is not None

    imply_formula = node[index]
    lhs = imply_formula.operands[0]
    rhs = imply_formula.operands[1]
    
    if lhs.id_implication == -1:
        lhs = lhs.shallow_copy() # Can we avoid these shallow copies?
        lhs.id_implication = 0
    if rhs.id_implication == -1:
        rhs = rhs.shallow_copy()
        rhs.id_implication = 1

    def merge_derived_g_nodes(imply_op, new_node):
        # Cerca nodi 'G' derivati nel nuovo nodo
        for i, operand in enumerate(new_node.operands):
            if operand.operator == 'G' and operand.identifier == imply_op.identifier and operand.is_derived and operand.id_implication == imply_op.id_implication:
                # We are modifying the existing G node, so we need to make a copy
                new_node.operands[i] = operand.shallow_copy()
                # TODO Investigate if this is correct
                new_node.operands[i].upper = operand.upper+1
                return None
        return imply_op

    # lhs of the implication
    new_node1 = node.shallow_copy()
    new_node1.replace_operand(index, push_negation(Node('!', lhs)))

    # rhs of the implication
    new_node2 = node.shallow_copy()
    new_lhs, new_rhs = lhs, rhs
    if lhs.operator == 'G' and lhs.is_derived:
        new_lhs = merge_derived_g_nodes(lhs, new_node2)
    if rhs.operator == 'G' and rhs.is_derived:
        new_rhs = merge_derived_g_nodes(rhs, new_node2)
    new_node2.replace_operand(index, *(x for x in [new_lhs, new_rhs] if x is not None))

    # euristica per ottimizzare, se nella formula ho già antecedente che deve essere vero
    # resituisco prima nodo in cui antecedente è vero, altrimenti il contrario
    def check_match(sub1, sub2):
        return sub1.operator == sub2.operator and ((sub1.operator == 'P' and sub1.operands == sub2.operands) or (sub1.operator == '!' and sub1[0].operands == sub2[0].operands))

    if lhs.operator in {'P', '!'}:
        for operand in node.operands:
            if check_match(lhs, operand):
                return new_node2, new_node1
    elif lhs.operator in {'&&', ',', '||'}:
        for element in lhs.operands:
            for operand in node.operands:
                if check_match(element, operand):
                    return new_node2, new_node1
    return new_node1, new_node2



def decompose_imply_new(node, index):
    '''
    :return: decompone p->q come not(p) OR (p and q). Se ci sono più -> in and, viene rigettato il nodo in cui tutti
    gli antecedenti sono negati. Se c'è un solo -> viene rigettato il nodo con antecedente negato
    NB: non so se qui si può introdurre la semplificazione per creare meno elementi (verifica che satisfied implications venga comnque correttamente aggiornato)
    '''

    imply_formula = node[index]
    lhs = imply_formula.operands[0]  # antecedente
    rhs = imply_formula.operands[1]  # conseguente

    assert index >= 0 and node is not None
    if len(node.operands) > 1:
        if node.implications is None:  # non so perché a volte sia None, in attesa di trovare il problema uso questa soluzione
            node = count_implications(node)
        new_node2 = node.shallow_copy()
        new_node2.replace_operand(index, lhs, rhs)
        new_node2.satisfied_implications.append(node.operands[index].identifier)
        new_node1 = node.shallow_copy()
        if node.implications > 1:  # quando sono a 1 significa che quello che sto negando ora è l'ultimo e quindi li ho negati tutti
            new_node1.replace_operand(index, push_negation(Node('!', lhs)))
            new_node1.implications -= 1  # decremento di 1 ogni volta che passo dal ramo che nega l'antecedente per poter sapere quando li ho negati tutti
            new_node1 = push_negation(new_node1)
        else:
            new_node1 = 'Rejected'
    else:  # se l'imply non è in and con nulla posso direttamente rigettare il ramo negato
        new_node1 = 'Rejected'
        new_node2 = Node(',')
        new_node2.operands = imply_formula.operands
    # qui conviene restituire prima il ramo in cui antecedente è vero, perché tanto finché non sono tutti veri almeno
    #una volta non posso interrompere l'esplorazione
    return new_node2, new_node1


def simplify_F(node):
    '''
    Simplify formula according to the rule
    F[a,b] p && F[c,d] p <-> F[c,d] p whenever c >= a && d <= b
    '''
    assert node.operator == ','
    remove_indices = []
    F_formulas = {}
    for i, formula in enumerate(node.operands):
        if formula.operator == 'F':
            operand = formula[0]
            if operand in F_formulas:
                for j, F_formula in F_formulas[operand]:
                    if F_formula.lower >= formula.lower and F_formula.upper <= formula.upper:
                        remove_indices.append(i)
                    elif formula.lower >= F_formula.lower and formula.upper <= F_formula.upper:
                        remove_indices.append(j)
                        # We could also remove (j, F_formula) from the set, but we would have to do it out of the loop
            else:
                F_formulas[operand] = {(i, formula)}
    for i in sorted(remove_indices, reverse=True):
        del node.operands[i]
    return node

def decompose_jump(node):
    '''
    Distingue casi problematici da non problematici

    NB nei casi PROBLEMATICI (flag = True) posso saltare a partire dal minimo tra range dell'operatore esterno
    e a+d (G[a,b]F[c,d]...) e salto fino al minimo successivo della formula completa (senza contare i bound degli op derivati dalla decomposizione dei nested).
    Se il minimo tra i 2 è l'op esterno in realta non devo fare nulla perché avanzo di 1 in 1 finche non sparisce il nesting, a quel punto la
    flag diventa False ed entro nell'altro caso.

    NB: NON CONTARE I BOUND DEGLI OPERATORI DERIVED DAI NESTED
    '''
    assert node.operator == ','
    flag = flagging(node)
    time_instants = extract_time_instants(node, flag)
    if not flag:  # non ci sono operatori probelmatici attivi
        if not time_instants:
            # there are no temporal operators, we just return None
            return None
        if node.jump1:
            new_time = node.current_time + 1
        else:
            # trovo il primo numero maggiore dell'istante corrente di tempo
            indice = bisect.bisect_right(time_instants, node.current_time)
            new_time = time_instants[indice]
        
        new_operands = []
        for and_operand in node.operands:
            if and_operand.operator not in {'P', '!', 'O'}:
                new_operands.append(and_operand)
            elif and_operand.operator == 'O' and and_operand.operands[0].lower < and_operand.operands[0].upper:
                sub_formula = and_operand.operands[0].shallow_copy()
                sub_formula.lower = new_time
                new_operands.append(sub_formula)
        
        if new_operands:
            new_node = node.shallow_copy()
            new_node.jump1 = False
            new_node.operands = new_operands
            new_node.current_time = new_time
            if len(new_node.operands) > 1:
                simplify_F(new_node)
            return [new_node]
        else:
            return None
    else:  # caso con operatori problematici, uso direttamente i nodi per non perdere info su is_derived e initial_time
        # We first compute the time jump
        if node.jump1:
            jump = 1
            node.jump1 = False
        else:
            jump = [] 
            for and_operand in node.operands:
                # Controllo prima gli operatori nested problematici perché il salto dipende da loro:
                # verifico se ho raggiunto la threshold per cui posso saltare, se l'ho raggiunta cacolo il salto,
                # se non l'ho raggiunta il salto è 1
                # una volta calcolato il salto per ogni operatore problematico, faccio il minimo
                # una volta stabilito il salto da effettuare faccio un altro ciclo negli operands e applico il salto ad ognuno
                # controllando se ogni operatore è derivato da un nested o no (perché saltano in modo diverso)
                if and_operand.operator == 'O' and not and_operand.operands[0].is_derived and and_operand.operands[0].operator in {'G', 'U', 'R'}:
                    max_upper = -1
                    o_operand = and_operand.operands[0]
                    # trovo il max tra gli upper bound degli op interni
                    if o_operand.operator in {'G', 'U'}:
                        max_upper = o_operand.operands[0].get_max_upper()
                    elif o_operand.operator == 'R':
                        max_upper = o_operand.operands[1].get_max_upper()

                    if max_upper != -1 and o_operand.lower >= o_operand.initial_time + max_upper:
                        # se operatore interno è esaurito
                        indice = bisect.bisect_right(time_instants, o_operand.lower) # trovo il primo numero maggiore dell'istante corrente di tempo
                        jump.append(time_instants[indice] - o_operand.lower) # il jump che devo fare è l'istante in cui devo arrivare - quello corrente
                    else:  # se sono qui non posso saltare, devo andare avanti di 1 in 1
                        jump.append(1)

            jump = min(jump)
        # Now we build the new node after the jump
        new_node_operands = []
        for and_operand in node.operands:
            if and_operand.operator in {'F', 'G', 'U', 'R'} and (jump == 1 or not and_operand.is_derived):
                new_node_operands.append(and_operand)
            elif and_operand.operator == 'O' and and_operand.operands[0].lower < and_operand.operands[0].upper:
                if jump == 1:
                    sub_formula = and_operand.operands[0].shallow_copy() # argomento di 'O'
                    sub_formula.lower = sub_formula.lower + jump
                    new_node_operands.append(sub_formula)
                else:
                    if and_operand.operands[0].is_derived:  # per questi devo aggiungere jump ad entrambi gli estremi dell'intervallo
                        sub_formula = and_operand.operands[0].shallow_copy()
                        sub_formula.lower = sub_formula.lower + jump
                        sub_formula.upper = sub_formula.upper + jump
                        new_node_operands.append(sub_formula)
                    else:
                        sub_formula = and_operand.operands[0].shallow_copy()
                        sub_formula.lower = sub_formula.lower + jump
                        new_node_operands.append(sub_formula)

        new_node = node.shallow_copy()
        new_node.operands = new_node_operands
        new_node.current_time = node.current_time + jump
        if len(new_node.operands) > 1:
            simplify_F(new_node)
        return [new_node]


def local_consistency_check(local_solver, node):
    '''
    :return: True if node is consistent, False otherwise
    '''
    for operand in node.operands:
        match operand.operator:
            case 'O':
                if operand.operator == 'O' and operand[0].operator in {'F', 'U'} and operand[0].lower == operand[0].upper:
                    return False
            case 'P':
                if operand[0] in {'<', '<=', '>', '>=', '==', '!='}:
                    local_solver.add_real_constraint(False, operand)
                else: # Boolean variable
                    prop = operand[0]
                    if prop == 'B_false':
                        return False # we have false in the upper level of a node
                    elif prop == 'B_true':
                        continue # if we have true in the upper level of a node we can just ignore it
                    local_solver.add_boolean_constraint(False, prop)
            case '!':
                if operand[0][0] in {'<', '<=', '>', '>=', '==', '!='}:
                    local_solver.add_real_constraint(True, operand[0])
                else: # Boolean variable
                    prop = operand[0][0]
                    if prop == 'B_true':
                        return False # we have !true in the upper level of a node
                    elif prop == 'B_false':
                        continue # if we have !false in the upper level of a node we can just ignore it
                    local_solver.add_boolean_constraint(True, prop)

    return local_solver.check()


def set_initial_time(formula):
    '''
    :return: Serve per il jump nei casi nested problematici (devo sapere qual era il lower bound iniziale
    del nested + esterno per sapere se posso saltare)
    '''
    if formula.operator in {'&&', '||', ',', '->'}:
        for operand in formula.operands:
            if operand.operator in {'G', 'U'} and operand.operands[0].operator not in {'P', '!'}:
                operand.initial_time = operand.lower
            elif operand.operator in {'R'} and operand.operands[1].operator not in {'P', '!'}:
                operand.initial_time = operand.lower
            elif operand.operator in {'&&', '||', ',', '->', '<->'}:
                return set_initial_time(operand)
    elif formula.operator in {'G', 'U'} and formula.operands[0].operator not in {'P', '!'}:
        formula.initial_time = formula.lower
    elif formula.operator in {'R'} and formula.operands[1].operator not in {'P', '!'}:
        formula.initial_time = formula.lower
    return formula


def modify_U_R(node):
    """Modifica una formula sostituendo ogni p U[a,b] q e p R[a,b] q in tutta la formula ricorsivamente."""
    """ pU[a,b]q diventa pU[a,b]q && G[0,a]p mentre (p R[a,b] q) → (F[0,a] p) || (p R[a,b] q)"""
    # Se il nodo è atomico ('P'), lo restituiamo senza modifiche
    if node.operator == 'P':
        return node

    # Se il nodo ha operatori figli, li modifichiamo prima
    #new_operands = [modify_U_R(operand) for operand in node.operands]
    for i in range(len(node.operands)):
        node.operands[i] = modify_U_R(node.operands[i])

    # Se il nodo è un Until, lo modifichiamo: (p U[a,b] q) → (p U[a,b] q) ∧ (G[0,a] p)
    if node.operator == 'U' and node.lower > 0:
        p = node[0]
        a = node.lower

        G_part = Node('G', '0', a, p)
        new_node = Node('&&')
        new_node.operands = [node, G_part]
        return new_node # Sostituiamo con il nuovo nodo

    # Se il nodo è un Release, lo modifichiamo: (p R[a,b] q) → (F[0,a] p) ∨ (p R[a,b] q)
    elif node.operator == 'R' and node.lower > 0:
        p = node[0]
        a = node.lower

        F_part = Node('F', '0', a, p)
        new_node = Node('||')
        new_node.operands = [F_part, node]
        return new_node  # Sostituiamo con il nuovo nodo

    # Restituiamo il nodo con gli operandi aggiornati
    return node


def count_implications(formula):
    counter = 1
    if formula.operator in {'&&', ','}:
        # Conta quante implicazioni ('->') ci sono tra gli operandi
        implication_count = sum(1 for operand in formula.operands if operand.operator == '->')
        # Aggiungi l'attributo 'implications' al nodo e assegna il conteggio
        formula.implications = implication_count
        for operand in formula.operands:
            if operand.operator == '->':
                operand.identifier = counter
                counter += 1
    else:
        # Se il nodo non è un '&&', esplora ricorsivamente i suoi operandi
        for operand in formula.operands:
            if isinstance(operand, Node):
                count_implications(operand)
    return formula


def assign_and_or_element(node):
    """
    Assegna l'attributo and_element numerato a ogni operando di un nodo G con operando &&
    """
    if not node.operands:
        return

    if node.operator == 'G' and node.operands[0].operator in {'&&'}:
        # Scorre i figli e assegna and_element
        for index, operand in enumerate(node.operands[0].operands):
            operand.and_element = index
    elif node.operator == 'G' and node.operands[0].operator in {'||'}:
        # Scorre i figli e assegna and_element
        for index, operand in enumerate(node.operands[0].operands):
            operand.or_element = index

    # Ricorsione su tutti gli operandi
    for operand in node.operands:
        if isinstance(operand, Node):
            assign_and_or_element(operand)

def add_tree_child(tableau_data, G, parent_label, child):
    tableau_data.counter += 1
    if isinstance(child, str):
        child_label = child + ' ' + str(tableau_data.counter)
    else:
        child.counter = tableau_data.counter
        child_label = child.to_label()
    G.add_node(child_label)
    G.add_edge(parent_label, child_label)

def add_rejected(tableau_data, node):
    # Note: checking if some other node implies this one seems not to be useful
    node.sort_operands()
    tableau_data.rejected_store.append(node)
    bisect.insort_left(tableau_data.rejected_store, node, key=Node.get_imply_sort_key)

def check_rejected(tableau_data, node):
    node.sort_operands()
    i = bisect.bisect_left(tableau_data.rejected_store, node.get_imply_search_key(), key=Node.get_imply_search_key)
    for rejected in tableau_data.rejected_store[i:]:
        if node.implies_quick(rejected):
            if tableau_data.verbose:
                print('Rejecting', node, ' because it implies rejected node ', rejected)
            return True
        if rejected.operator == node.operator == ',' and node.operands[-1].get_imply_search_key() < rejected.operands[0].get_imply_search_key():
            return False
    return False

def add_children(tableau_data, local_solver, node, depth, last_spawned, max_depth, current_time):
    if local_solver is None:
        local_solver = LocalSolver()
    mode = tableau_data.mode

    if depth >= max_depth:
        print('Max depth reached!')
        return None

    if tableau_data.tree:
        node_label = node.to_label()

    current_time = node.current_time
    local_solver.push()
    children = decompose(tableau_data, local_solver, node, current_time)
    if children is None:
        local_solver.pop()
        if tableau_data.verbose:
            print('No more children in this branch')
        if mode in {'sat', 'complete'}:
            return True
        else: # mode == 'strong_sat':
            tableau_data.true_implications.update(node.satisfied_implications)
            if len(tableau_data.true_implications) == tableau_data.number_of_implications:
                return True
            else:
                return False
    if tableau_data.verbose:
        for child in children:
            print(child)
    child_queue = []
    for child in children:
        if child != 'Rejected':
            if mode != 'sat' or child.current_time == current_time or not check_rejected(tableau_data, child):
                child_queue.append(child)
            elif tableau_data.tree and mode == 'sat':
                add_tree_child(tableau_data, tableau_data.tree, node_label, child)
                node_label = child.to_label()
                child = 'Rejected (memo)'
        if tableau_data.tree:
            add_tree_child(tableau_data, tableau_data.tree, node_label, child)
    
    if mode == 'complete':
        complete_result = False

    if tableau_data.parallel and mode == 'sat' and depth - last_spawned > 30 and len(child_queue) > 1: # add 'strong_sat'
        # print("spawning", node)
        # print("children: ", str([child for child in child_queue]))

        pool = fs.ProcessPoolExecutor(max_workers=2)
        try:
            futures = [pool.submit(
                add_children,
                tableau_data,
                None, # z3 stuff can't be pickled
                child, depth + 1, depth, max_depth, current_time
            ) for child in child_queue]
            for fut in fs.as_completed(futures):
                if fut.result():
                    local_solver.pop()
                    return True
        finally:
            # We wait for running subtask to finish, otherwise they remain hanging.
            # TODO maybe use Event to stop them asap
            pool.shutdown(wait=True, cancel_futures=True)
    else:
        for child in child_queue:
            # If the child comes from a temporal jump, we need a new, empty solver
            child_solver = local_solver if child.current_time == current_time else LocalSolver()
            if add_children(tableau_data, child_solver, child, depth + 1, last_spawned, max_depth, current_time):
                if mode == 'complete':
                    complete_result = True
                else: # mode in {'sat', 'strong_sat'}
                    local_solver.pop()
                    return True
            elif mode == 'sat' and child.current_time > current_time:
                add_rejected(tableau_data, child)

    local_solver.pop()

    if mode in {'sat', 'strong_sat'}:
        return False
    else: # mode == 'complete'
        return complete_result

def build_decomposition_tree(tableau_data, root, max_depth):
    """
    : return:
        if mode in {'sat', 'complete'}:
            True if the tableau has an accepting branch rooted at node,
            False if the tableau has only rejected branches rooted at node,
            None if we reached max_dept without finding an accepting branch
        if mode == 'strong_sat':
            True if the tableau has an accepting branch rooted at node and all implications are satisfied,
            False if the tableau has only rejected branches rooted at node,
            None if we reached max_dept without finding an accepting branch
    """
    root.current_time = 0
    root.jump1 = root.check_boolean_closure(lambda n: n.operator == 'P')

    if tableau_data.build_tree:
        root.counter = tableau_data.counter
        tableau_data.tree.add_node(root.to_label())

    if tableau_data.verbose:
        print(root)

    res = add_children(tableau_data, LocalSolver(), root, 0, 0, max_depth, root.current_time)

    if res and tableau_data.mode in {'sat', 'strong_sat'} and tableau_data.verbose:
        print("The requirement set is consistent")
    elif not res and tableau_data.mode in {'sat', 'strong_sat'}:
        print("The requirement set is not consistent")
    if tableau_data.build_tree:
        return tableau_data.tree, res
    else:
        return res

class TableauData:

    def __init__(self, formula, mode, build_tree, parallel, verbose):
        self.true_implications = set()
        self.number_of_implications = formula.implications
        self.build_tree = build_tree
        self.mode = mode
        self.parallel = parallel
        self.verbose = verbose
        if build_tree:
            self.counter = 0
            self.tree = nx.DiGraph()
        else:
            self.tree = None
        if mode == 'sat':
            self.rejected_store = []


def plot_tree(G):
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=8, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()


def make_tableau(formula, max_depth, mode, build_tree, parallel, verbose, mltl=False):
    if formula.operator != ',':
        formula = Node(',', formula)

    if not mltl:
        formula = modify_U_R(formula)
    formula = decompose_and(formula)[0][0] # perché funzione sopra può aggiungere && di troppo
    assign_and_or_element(formula)
    formula = assign_identifier(formula)
    assign_real_expr_id(formula)
    formula = count_implications(formula)
    set_initial_time(formula)
    formula = push_negation(formula)

    tableau_data = TableauData(formula, mode, build_tree, parallel, verbose)
    return build_decomposition_tree(tableau_data, formula, max_depth)


'''
CASI NON PROBLEMATICI:
FG
FF
FU (non problematico, ma ogni volta che estrai U dovresti aggiungere il G)
U con nesting nel secondo argument
R con nesting nel primo argument

CASI PROBLEMATICI:
GF
GG
GU
GR
U con nesting nel primo argument (F,G)
R con nesting nel secondo argument (F,G)


'''
