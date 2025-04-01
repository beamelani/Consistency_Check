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

def shift_bounds(node):
    def shift_backward(f, shift_amount):
        match f.operator:
            case '&&' | '||' | ',' | '->' | '!':
                for operand in f:
                    shift_backward(operand, shift_amount)
            case 'G' | 'F' | 'U' | 'R':
                f.lower -= shift_amount
                f.upper -= shift_amount
            case _:
                raise RuntimeError('Trying to shift bounds of proposition')

    match node.operator:
        case '&&' | '||' | ',' | '->' | '!':
            for operand in node:
                shift_bounds(operand)
        case 'G' | 'F':
            shift_bounds(node[0])
            shift_amount = node[0].get_min_lower(False)
            # If get_min_lower is -1, we can't shift because there are props at the first level
            if shift_amount > 0:
                shift_backward(node[0], shift_amount)
                node.lower += shift_amount
                node.upper += shift_amount
        case 'U' | 'R':
            shift_bounds(node[0])
            shift_bounds(node[1])
            shift_amount0 = node[0].get_min_lower(False)
            shift_amount1 = node[1].get_min_lower(False)
            shift_amount = min(shift_amount0, shift_amount1)
            # If get_min_lower is -1, we can't shift because there are props at the first level
            if shift_amount > 0:
                shift_backward(node[0], shift_amount)
                shift_backward(node[1], shift_amount)
                node.lower += shift_amount
                node.upper += shift_amount


def assign_and_or_element(node):
    """
    Assegna l'attributo and_element numerato a ogni operando di un nodo G con operando &&
    """
    if not node.operands:
        return

    if node.operator == 'G' and node.operands[0].operator == '&&':
        # Scorre i figli e assegna and_element
        for index, operand in enumerate(node.operands[0].operands):
            operand.and_element = index
    elif node.operator == 'G' and node.operands[0].operator == '||':
        # Scorre i figli e assegna or_element
        for index, operand in enumerate(node.operands[0].operands):
            operand.or_element = index

    # Ricorsione su tutti gli operandi
    for operand in node.operands:
        if isinstance(operand, Node):
            assign_and_or_element(operand)


def count_implications(node, counter=[0]):
    """
    Conta tutte le implicazioni ('->') presenti nel nodo e nei suoi sotto-nodi,
    assegnando a ciascuna un identificatore univoco.

    """
    if not isinstance(node, Node):
        return
    if node.operator == '->':
        node.identifier = counter[0]  # Assegna l'ID univoco all'implicazione
        counter[0] += 1  # Incrementa il contatore
    else:
        for operand in node.operands:  # Ricorsione su tutti gli operandi
            count_implications(operand, counter)

    return counter[0]


def assign_identifier(node):
    '''
    :param node:
    :return: la funzione assegna un identificatore agli operatori nested, in modo che nella decomposizione gli operatori
    derivati dalla decomposizione di un nested siano riconducibili all'operatore originario
    '''
    id_counter = 0

    def do_assign(node):
        nonlocal id_counter
        match node.operator:
            case 'G' | 'F' | 'U' | 'R':
                node.identifier = id_counter
                id_counter += 1
            case '&&' | '||' | ',' | '->':
                for operand in node.operands:
                    do_assign(operand)

    do_assign(node)


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
                    #res = decompose_imply_new(node, j)
                    res = decompose_imply_classic(node, j, 'strong_sat', tableau_data.number_of_implications)
                break

    if res is None:
        for j in range(len(node.operands)):
            match node.operands[j].operator:
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
    return decompose_jump(tableau_data, node)


def decompose_all_G_nodes(outer_node, current_time):
    """
    Decompone tutti i nodi G nella formula con lower bound uguale a current_time.
    """
    # Funzione interna ricorsiva per modificare l'argomento
    def modify_argument(arg, G_node, short, simple):
        if arg.operator in {'P', '!'}:
            return arg
        elif simple and arg.operator == 'F' and G_node.lower + 2 <= G_node.upper:
            # We expand with the equivalence G[a,b]F[c,d] q = (F[a+c+1,a+d] q || (G[a+c,a+c] q && G[a+d+1,a+d+1] q)) && G[a+2,b]F[c,d] q
            a = G_node.lower
            c, d = arg.lower, arg.upper
            q = arg.operands[0]
            G_node.lower += 1 # this implements G[a+2,b]F[c,d] q because decompose_jump adds 1 again
            ret = Node('||', Node('F', a+c+1, a+d, q), Node(',', Node('G', a+c, a+c, q), Node('G', a+d+1, a+d+1, q)))
            ret.set_initial_time()
            return ret
        elif arg.operator in {'U', 'R', 'F'} or (arg.operator == 'G' and (not short or G_node.lower == G_node.initial_time)):
            # Modifica bounds sommando quelli del nodo G
            extract = arg.shallow_copy()
            extract.lower = arg.lower + G_node.lower
            extract.upper = arg.upper + G_node.lower
            extract.parent = G_node.identifier if G_node.lower < G_node.upper else None
            extract.set_initial_time()
            return extract
        elif short and arg.operator == 'G' and G_node.lower > G_node.initial_time: #non aggiungo un altro G, ma allungo intervallo di quello già esistente
            G_counter = 0
            for i, operand in enumerate(outer_node.operands):
                if operand.operator == 'G' and operand.is_derived() and operand.parent == G_node.identifier and operand.and_element == arg.and_element:
                    outer_node.operands[i] = operand.shallow_copy()
                    outer_node.operands[i].upper += 1
                    G_counter += 1
                    if G_node.lower == G_node.upper:
                        outer_node.operands[i].parent = None
                elif operand.operator == 'O' and operand.operands[0].operator == 'G' and operand.operands[0].is_derived() and operand.operands[0].parent == G_node.identifier and operand.operands[0].and_element == arg.and_element:
                    operand.operands[0] = operand.operands[0].shallow_copy()
                    operand.operands[0].upper += 1
                    G_counter += 1
                    if G_node.lower == G_node.upper:
                        operand.operands[0].parent = False
            if G_counter == 0:
                extract = arg.shallow_copy()
                extract.lower = arg.lower + G_node.lower
                extract.upper = arg.upper + G_node.lower
                extract.parent = G_node.identifier
                extract.set_initial_time()
                return extract
            else:
                return None # non ritorno niente perché è bastato modificare il nodo esistente
        elif arg.operator in {'&&', ','}:
            # Applica la modifica ricorsivamente agli operandi
            arg = arg.shallow_copy()
            new_operands = (modify_argument(op, G_node, short, False) for op in arg.operands)
            arg.operands = [x for x in new_operands if x is not None]
            if arg.operands:
                return arg
            else:
                return None
        elif arg.operator in {'||', '->'}:
            arg = arg.shallow_copy()
            new_operands = (modify_argument(op, G_node, False, False) for op in arg.operands)
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
                    any(other.lower_bound() == operand.lower for j, other in enumerate(outer_node.operands) if (j != i and other is not None))):
                    outer_node.jump1 = True
                # Set is_derived to false
                for j, other in enumerate(outer_node.operands):
                    if j != i and other is not None:
                        temp_op = other.operands[0] if other.operator == 'O' else other
                        if temp_op.operator in {'G', 'U', 'R', 'F'} and temp_op.is_derived() and temp_op.parent == operand.identifier:
                            temp_op.parent = None
                # Elimino l'elemento se a == b
                outer_node.operands[i] = None
    outer_node.operands = [x for x in outer_node.operands if x is not None]

    for G_node in G_nodes:
        assert G_node.initial_time != '-1'
        # Decomponi il nodo originale
        new_operands = modify_argument(G_node.operands[0], G_node, True, True)
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
            extract.set_initial_time()
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
    if (F_formula.lower == F_formula.upper and
        F_formula[0].check_boolean_closure(lambda n: n.operator == 'P') and
        any(other.lower_bound() == F_formula.lower for j, other in enumerate(node.operands) if j != index)):
        new_node2.jump1 = True

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
    assert U_formula.initial_time != '-1'
    first_operand = formula[index].operands[0]
    second_operand = formula[index].operands[1]

    def modify_argument(arg, derived):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modifica bounds sommando quelli del nodo
            extract = arg.shallow_copy()
            extract.lower = arg.lower + U_formula.lower
            extract.upper = arg.upper + U_formula.lower
            extract.current_time = U_formula.current_time
            if derived:
                extract.parent = U_formula.identifier
            extract.set_initial_time()
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Applica la modifica ricorsivamente agli operandi
            new_arg = arg.shallow_copy()
            new_arg.operands = [modify_argument(op, derived) for op in arg.operands]
            return new_arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

    # Node in which U is not satisfied (p, OU)
    new_node1 = formula.shallow_copy()
    new_operand = modify_argument(first_operand.shallow_copy(), True) #derived indica se is_derived deve essere True (quindi è vero nel nodo con p, OU quando p è G,F...)
    new_node1.replace_operand(index, Node('O', U_formula))
    new_node1.operands.extend([new_operand])

    # Node where U is satisfied (q)
    new_node2 = formula.shallow_copy()
    new_node2.replace_operand(index, modify_argument(second_operand.shallow_copy(), False))
    if (U_formula.lower == U_formula.upper and
        U_formula[1].check_boolean_closure(lambda n: n.operator == 'P') and
        any(other.lower_bound() == U_formula.lower for j, other in enumerate(formula.operands) if j != index)):
        new_node2.jump1 = True
    if U_formula.lower == U_formula.upper:
        for operand in new_node1.operands:  # quando U va via tolgo is_derived dagli operatori
            temp_op = operand.operands[0] if operand.operator == 'O' else operand
            if temp_op.is_derived() and temp_op.parent == U_formula.identifier:
                temp_op.parent = None
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
    assert R_formula.initial_time != '-1'
    first_operand = formula[index].operands[0]
    second_operand = formula[index].operands[1]

    def modify_argument(arg, derived):
        if arg.operator in {'P', '!'}:
            return arg
        elif arg.operator in {'G', 'F', 'U', 'R'}:
            # Modifica bounds sommando quelli del nodo
            extract = arg.shallow_copy()
            extract.lower = arg.lower + R_formula.lower
            extract.upper = arg.upper + R_formula.lower
            extract.current_time = R_formula.current_time
            if derived:
                extract.parent = R_formula.identifier
            extract.set_initial_time()
            return extract
        elif arg.operator in {'&&', '||', ',', '->'}:
            # Applica la modifica ricorsivamente agli operandi
            new_arg = arg.shallow_copy()
            new_arg.operands = [modify_argument(op, derived) for op in arg.operands]
            return new_arg
        else:
            raise ValueError(f"Operatore non gestito: {arg.operator}")

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
            temp_op = operand.operands[0] if operand.operator == 'O' else operand
            if temp_op.is_derived() and temp_op.parent == R_formula.identifier:
                temp_op.parent = None
        if (second_operand.check_boolean_closure(lambda n: n.operator == 'P') and
            any(op.lower_bound() == R_formula.lower for j, op in enumerate(new_node1.operands) if j != index)):
            new_node1.jump1 = True

    # Node where U is satisfied (p)
    new_node2 = formula.shallow_copy()
    new_node2.replace_operand(index, modify_argument(first_operand.shallow_copy(), False), modify_argument(second_operand.shallow_copy(), False))

    return [new_node2, new_node1]

def decompose_and(node):
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
        if or_operand.is_derived() and or_operand.or_element > -1:
            z = 0
            for element in new_node.operands:
                if element.operator == 'G' and element.parent == or_operand.parent and element.or_element == or_operand.or_element:
                    z += 1
                    element.upper = or_operand.upper
                elif element.operator == 'O' and element.operands[0].operator == 'G' and element.operands[0].is_derived() and element.operands[0].parent == or_operand.parent and element.operands[0].or_element == or_operand.or_element:
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


def decompose_imply_classic(node, index, mode='sat', number_of_implications=None):
    '''
    :return: decompone p->q come not(p) OR (p and q), senza evitare il caso vacuously true
    '''
    assert index >= 0 and node is not None

    imply_formula = node[index]
    lhs = imply_formula.operands[0]
    rhs = imply_formula.operands[1]
    
    if lhs.id_implication == -1:
        lhs.id_implication = 0
    if rhs.id_implication == -1:
        rhs.id_implication = 1

    def merge_derived_g_nodes(imply_op, new_node):
        # Cerca nodi 'G' derivati nel nuovo nodo
        for i, operand in enumerate(new_node.operands):
            if operand.operator == 'G' and operand.parent == imply_op.parent and operand.is_derived() and operand.id_implication == imply_op.id_implication:
                # We are modifying the existing G node, so we need to make a copy
                new_node.operands[i] = operand.shallow_copy()
                new_node.operands[i].upper = operand.upper
                return None
        return imply_op

    # lhs of the implication
    new_node1 = node.shallow_copy()
    new_node1.replace_operand(index, push_negation(Node('!', lhs)))

    # rhs of the implication
    new_node2 = node.shallow_copy()
    new_lhs, new_rhs = lhs, rhs
    if lhs.operator == 'G' and lhs.is_derived():
        new_lhs = merge_derived_g_nodes(lhs, new_node2)
    if rhs.operator == 'G' and rhs.is_derived():
        new_rhs = merge_derived_g_nodes(rhs, new_node2)
    new_node2.replace_operand(index, *(x for x in [new_lhs, new_rhs] if x is not None))

    if imply_formula.identifier is not None and mode == 'strong_sat':
        skip = imply_formula.identifier in new_node2.satisfied_implications
        new_node2.satisfied_implications.add(imply_formula.identifier)
    else:
        # TODO this is needed because sometimes imply_formula.identifier is None (req_cps): find out why and fix it
        skip = True

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

    if mode == 'sat' or new_node2.satisfied_implications == number_of_implications or (mode == 'strong_sat' and skip):
        # in strong_sat, se quella implicazione l'avevo già prec soddisfatta non mi interessa risoddisfarla
        return new_node1, new_node2
    else:
        return new_node2, new_node1



def decompose_imply_new(node, index):
    '''
    ATTENZIONE: possibile problema, posso avere implicazioni che si attivano in istanti temporali successivi, quindi
    il numero di implicazioni calcolato precedentemente risulta errato, pensare di aggiornarlo (ma come???)
    :return: decompone p->q come not(p) OR (p and q). Se ci sono più -> in and, viene rigettato il nodo in cui tutti
    gli antecedenti sono negati. Se c'è un solo -> viene rigettato il nodo con antecedente negato
    NB: non so se qui si può introdurre la semplificazione per creare meno elementi (verifica che satisfied implications venga comnque correttamente aggiornato)
    '''

    imply_formula = node[index]
    lhs = imply_formula.operands[0]  # antecedente
    rhs = imply_formula.operands[1]  # conseguente

    assert index >= 0 and node is not None
    new_node2 = node.shallow_copy()
    new_node2.replace_operand(index, lhs, rhs)
    #NB: alcuni node.operands[index] non hanno identifier, forse si toglie in decompose_all_G_nodes, per ora faccio in modo che se è None non viene aggiunto
    if node.operands[index].identifier is not None:
        new_node2.satisfied_implications.add(node.operands[index].identifier)
    new_node1 = node.shallow_copy()
    new_node1.replace_operand(index, push_negation(Node('!', lhs)))
    new_node1 = push_negation(new_node1)
    # qui conviene restituire prima il ramo in cui antecedente è vero, perché tanto finché non sono tutti veri almeno
    #una volta non posso interrompere l'esplorazione
    return new_node1, new_node2

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

def is_complex_temporal_operator(node):
    match node.operator:
        case 'G' | 'U':
            return has_temporal_operator(node[0])
        case 'R':
            return has_temporal_operator(node[1])
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

def extract_time_instants(node, flag):
    """
    :return: funzione che restituisce gli estremi di tutti gli intervalli della formula in un vettore ordinato
    (non quelli degli op derivati, eccezione se op is_derived è estratto da -> o ||)
    """
    time_instants = []
    if flag:
        for elem in node:
            if elem.operator in {'G', 'F', 'U', 'R'} and not elem.is_derived():
                # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                time_instants.append(elem.lower)
                time_instants.append(elem.upper)
            elif elem.operator == 'O' and not elem.operands[0].is_derived():
                time_instants.append(elem.operands[0].lower)
                time_instants.append(elem.operands[0].upper)
    else:
        for elem in node:
            if elem.operator in {'G', 'F', 'U', 'R'}:  # Controlla operatori temporali G (Globally), F (Finally) e U (Until)
                time_instants.append(elem.lower)
                time_instants.append(elem.upper)
            elif elem.operator == 'O':
                time_instants.append(elem.operands[0].lower)
                time_instants.append(elem.operands[0].upper)

    return sorted(time_instants)

def decompose_jump(tableau_data, node):
    '''
    Distingue casi problematici da non problematici

    NB nei casi PROBLEMATICI (flag = True) posso saltare a partire dal minimo tra range dell'operatore esterno
    e a+d (G[a,b]F[c,d]...) e salto fino al minimo successivo della formula completa (senza contare i bound degli op derivati dalla decomposizione dei nested).
    Se il minimo tra i 2 è l'op esterno in realta non devo fare nulla perché avanzo di 1 in 1 finche non sparisce il nesting, a quel punto la
    flag diventa False ed entro nell'altro caso.

    NB: NON CONTARE I BOUND DEGLI OPERATORI DERIVED DAI NESTED
    '''
    assert node.operator == ','
    trace_stack = tableau_data.trace_stack
    if trace_stack is not None:
        trace_stack.append([])

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
            elif trace_stack is not None and and_operand.operator in {'P', '!'}:
                trace_stack[-1].append(str(and_operand))

        if trace_stack is not None:
            repetitions = new_time - node.current_time - 1 #-1 perché una volta l'ho già aggiunta prima
            trace_stack.extend([trace_stack[-1]] * repetitions)

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
            must_jump_1 = False
            for and_operand in node.operands:
                # Controllo prima gli operatori nested problematici perché il salto dipende da loro:
                # verifico se ho raggiunto la threshold per cui posso saltare, se l'ho raggiunta cacolo il salto,
                # se non l'ho raggiunta il salto è 1
                # una volta calcolato il salto per ogni operatore problematico, faccio il minimo
                # una volta stabilito il salto da effettuare faccio un altro ciclo negli operands e applico il salto ad ognuno
                # controllando se ogni operatore è derivato da un nested o no (perché saltano in modo diverso)
                if and_operand.operator == 'O' and not and_operand.operands[0].is_derived() and and_operand.operands[0].operator in {'G', 'U', 'R'}:
                    max_upper = -1
                    o_operand = and_operand.operands[0]
                    # trovo il max tra gli upper bound degli op interni
                    if o_operand.operator in {'G', 'U'}:
                        max_upper = o_operand.operands[0].get_max_upper()
                    elif o_operand.operator == 'R':
                        max_upper = o_operand.operands[1].get_max_upper()

                    must_jump_1 = must_jump_1 or max_upper == -1 or o_operand.lower < o_operand.initial_time + max_upper

            if must_jump_1:
                jump = 1
            else:
                indice = bisect.bisect_right(time_instants, node.current_time) # trovo il primo numero maggiore dell'istante corrente di tempo
                jump = time_instants[indice] - node.current_time # il jump che devo fare è l'istante in cui devo arrivare - quello corrente
        # Now we build the new node after the jump
        new_node_operands = []
        for and_operand in node.operands:
            if and_operand.operator in {'F', 'G', 'U', 'R'} and (jump == 1 or not and_operand.is_derived()):
                new_node_operands.append(and_operand)
            elif and_operand.operator == 'O' and and_operand.operands[0].lower < and_operand.operands[0].upper:
                if jump == 1:
                    sub_formula = and_operand.operands[0].shallow_copy() # argomento di 'O'
                    sub_formula.lower = sub_formula.lower + jump
                    new_node_operands.append(sub_formula)
                else:
                    if and_operand.operands[0].is_derived():  # per questi devo aggiungere jump ad entrambi gli estremi dell'intervallo
                        sub_formula = and_operand.operands[0].shallow_copy()
                        sub_formula.lower = sub_formula.lower + jump
                        sub_formula.upper = sub_formula.upper + jump
                        new_node_operands.append(sub_formula)
                    else:
                        sub_formula = and_operand.operands[0].shallow_copy()
                        sub_formula.lower = sub_formula.lower + jump
                        new_node_operands.append(sub_formula)
            elif trace_stack is not None and and_operand.operator in {'P', '!'}:
                trace_stack[-1].append(str(and_operand))

        if trace_stack is not None:
            # aggiungo alla traccia gli atomi dell'ultimo nodo tot volte a seconda di quanto salto
            trace_stack.extend([trace_stack[-1]] * (jump - 1))
        
        new_node = node.shallow_copy()
        new_node.operands = new_node_operands
        new_node.current_time = node.current_time + jump
        if len(new_node.operands) > 1:
            simplify_F(new_node)

        # We build a simplified node without complex nested operators that implies new_node
        simple_node_operands = list(filter(lambda n: not is_complex_temporal_operator(n), new_node.operands))
        
        if len(simple_node_operands) == len(new_node.operands) or not simple_node_operands:
            return [new_node]
        else:
            simple_node = new_node.shallow_copy()
            simple_node.operands = simple_node_operands
            simple_node.siblings_imply = True
            return [simple_node, new_node]


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
                    if prop == 'false':
                        return False # we have false in the upper level of a node
                    elif prop == 'true':
                        continue # if we have true in the upper level of a node we can just ignore it
                    local_solver.add_boolean_constraint(False, prop)
            case '!':
                if operand[0][0] in {'<', '<=', '>', '>=', '==', '!='}:
                    local_solver.add_real_constraint(True, operand[0])
                else: # Boolean variable
                    prop = operand[0][0]
                    if prop == 'true':
                        return False # we have !true in the upper level of a node
                    elif prop == 'false':
                        continue # if we have !false in the upper level of a node we can just ignore it
                    local_solver.add_boolean_constraint(True, prop)

    return local_solver.check()


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
    if not check_rejected(tableau_data, node):
        #print(node)
        bisect.insort_left(tableau_data.rejected_store, node, key=Node.get_imply_sort_key)

def check_rejected(tableau_data, node):
    node.sort_operands()
    max_lower = max((op.lower for op in node.operands if op.operator in {'G', 'F', 'U', 'R'}))
    i = bisect.bisect_left(tableau_data.rejected_store, node.get_imply_sort_key(max_lower), key=Node.get_imply_sort_key)
    for rejected in tableau_data.rejected_store[i:]:
        if node.implies_quick(rejected):
            if tableau_data.verbose:
                print('Rejecting', node, ' because it implies rejected node ', rejected)
            return True
        if node.operands[-1].get_imply_search_key() < rejected.operands[0].get_imply_search_key():
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
        if tableau_data.trace_stack is not None:
            # altrimenti l'ultimo elemento non viene aggiunto perché non si passa dal jump
            for element in node.operands:
                if element.operator in {'P', '!'}:
                    tableau_data.trace_stack[-1].append(str(element))
        if mode in {'sat', 'complete'}:
            return True
        elif mode == 'strong_sat':
            return len(node.satisfied_implications) == tableau_data.number_of_implications
    if tableau_data.verbose:
        for child in children:
            print(child)

    child_queue = []
    for child in children:
        if child != 'Rejected':
            if child.siblings_imply:
                if mode == 'sat':
                    if check_rejected(tableau_data, child):
                        # All other children imply this one, so they'll be rejected
                        child_queue = []
                        if tableau_data.tree:
                            add_tree_child(tableau_data, tableau_data.tree, node_label, 'Rejected (memo)')
                        break
                    else:
                        # Children implied by others must be analyzed first
                        child_queue.insert(0, child)
            else:
                if mode != 'sat' or child.current_time == current_time or not check_rejected(tableau_data, child):
                    child_queue.append(child)
                elif tableau_data.tree and mode == 'sat':
                    add_tree_child(tableau_data, tableau_data.tree, node_label, child)
                    node_label = child.to_label()
                    child = 'Rejected (memo)'
        if tableau_data.tree:
            add_tree_child(tableau_data, tableau_data.tree, node_label, child)
    
    if all(c.siblings_imply for c in child_queue):
        child_queue = []

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
        max_depth_reached = False
        for child in child_queue:
            # If the child comes from a temporal jump, we need a new, empty solver
            child_solver = local_solver if child.current_time == current_time else local_solver.get_empty_solver()
            child_res = add_children(tableau_data, child_solver, child, depth + 1, last_spawned, max_depth, current_time)
            if child_res:
                if not child.siblings_imply:
                    if mode == 'complete':
                        complete_result = True
                    else: # mode in {'sat', 'strong_sat'}
                        local_solver.pop()
                        return True
            elif child_res is None:
                max_depth_reached = True
            elif mode == 'sat' and child.current_time > current_time:
                add_rejected(tableau_data, child)
                if child.siblings_imply:
                    # All other siblings will be rejected
                    break

    local_solver.pop()

    if mode in {'sat', 'strong_sat'}:
        if max_depth_reached:
            return None
        return False
    else: # mode == 'complete'
        if not complete_result and max_depth_reached:
            return None
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
        if tableau_data.trace_stack is not None:
            print(f"A trace satisfying the requirements is: " + str([item for sublist in tableau_data.trace_stack for item in sublist]))
    elif not res and tableau_data.mode in {'sat', 'strong_sat'}:
        print("The requirement set is not consistent")
    if tableau_data.build_tree or tableau_data.trace_stack is not None:
        return tableau_data.tree, tableau_data.trace_stack, res
    else:
        return res

class TableauData:

    def __init__(self, number_of_implications, mode, build_tree, return_trace, parallel, verbose):
        self.number_of_implications = number_of_implications
        self.build_tree = build_tree
        self.mode = mode
        self.parallel = parallel
        self.verbose = verbose
        if build_tree:
            self.counter = 0
            self.tree = nx.DiGraph()
        else:
            self.tree = None
        self.trace_stack = [] if return_trace else None
        if mode == 'sat':
            self.rejected_store = []


def plot_tree(G):
    pos = graphviz_layout(G, prog='dot')
    plt.figure(figsize=(12, 8))
    nx.draw(G, pos, with_labels=True, arrows=True, node_size=2000, node_color='lightblue',
            font_size=8, font_color='black', font_weight='bold', edge_color='gray')
    plt.title('Decomposition Tree')
    plt.show()


def make_tableau(formula, max_depth, mode, build_tree, return_trace, parallel, verbose, mltl=False):
    if formula.operator != ',':
        formula = Node(',', formula)

    if not mltl:
        formula = modify_U_R(formula)
        formula = decompose_and(formula)[0][0] # perché funzione sopra può aggiungere && di troppo
    
    formula = push_negation(formula)
    shift_bounds(formula)
    assign_and_or_element(formula)
    assign_real_expr_id(formula)
    number_of_implications = count_implications(formula)
    formula.set_initial_time()
    assign_identifier(formula)

    tableau_data = TableauData(number_of_implications, mode, build_tree, return_trace, parallel, verbose)
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
