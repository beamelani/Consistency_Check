import sys
import os
sys.path.append(os.getcwd())

import time
from itertools import combinations

from stl_consistency.parser import STLParser
from stl_consistency.node import Node, formula_to_string
from stl_consistency.smtchecker import smt_check_consistency

from stl_consistency.tableau import make_tableau, plot_tree

import csv
from tabulate import tabulate

# Benchmark: (avionics requirements)
# 1) stabilire un time horizon (T)
T = str(10)
requirements = [
    ['G', '0', T, ['||', ['&&', ['B_active'], ['!', ['B_inactive']], ['!', ['B_armed']]], ['&&', ['B_inactive'], ['!', ['B_active']], ['!', ['B_armed']]], ['&&', ['B_armed'], ['!', ['B_inactive']], ['!', ['B_active']]]]],
    ['G', '0', T, ['->', ['&&', ['B_inactive'], ['R_n_s == 1'],  ['R_X_c-R_X_b <= 5'], ['R_X_c-R_X_b>= -5'], ['G', '0', '5', ['R_airspeed>= R_Vmin']], ['!', ['B_X_over']], ['B_X_Activation_Request']], ['F', '0', '2', ['&&', ['!', ['B_inactive']], ['B_active']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['||', ['!', ['R_n_s == 1']], ['F', '0', '10', ['B_X_ch']], ['G', '0', '5', ['R_airspeed < R_Vmin']],  ['!', ['B_r_actuation']], ['!', ['B_X_Activation_Request']]]], ['F', '0', '2', ['&&', ['!', ['B_active']], ['B_inactive']]]]],
    ['G', '0', T, ['->', ['&&', ['B_armed'], ['||', ['!', ['R_n_s ==1']], ['F', '0', '5', ['B_X_ch']], ['!', ['B_X_Activation_Request']], ['!', ['B_r_actuation']]]], ['F', '0', '2', ['&&', ['!', ['B_armed']], ['B_inactive']]]]],
    ['G', '0', T, ['->', ['&&', ['B_inactive'], ['R_n_s ==1'], ['||', ['R_X_c - R_X_b >5'], ['R_X_c - R_X_b <-5']], ['B_X_Activation_Request']], ['F', '0', '2', ['&&', ['!', ['B_inactive']], ['B_armed']]]]],
    ['G', '0', T, ['->', ['&&', ['B_armed'], ['!', ['B_X_over']], ['R_X_c - R_X_b <=5'], ['R_X_c - R_X_b >=-5'], ['G', '0', '5', ['R_airspeed >= R_Vmin']]], ['F', '0', '2', ['&&', ['!', ['B_armed']], ['B_active']]]]], #DOPPIONE (dovrebbe essere stato corretto=
    ['G', '0', T, ['||', ['&&', ['B_active'], ['B_A']], ['&&', ['B_active'], ['B_B']], ['&&', ['B_active'], ['B_C']]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['B_A'], ['!', ['B_X_over']], ['R_Delta_T_Error_reference < R_T_Error'], ['R_Delta_T_Error_reference > 0 - R_T_Error']], ['F', '0', '1', ['&&', ['!', ['B_A']], ['B_B']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['B_B'], ['!', ['B_X_over']], ['R_T_Error < 3'], ['R_T_Error  > -3'],  ['R_Roll_attitude < 0.8'], ['R_Roll_attitude > -0.8'],  ['R_X_deviation < 0.5'], ['R_X_deviation > -0.5'], ['R_dalfadt < 0.002'], ['R_dalfadt > -0.002'], ['!', ['B_h_on']], ['!', ['B_f_on']]], ['F', '0', '1', ['&&', ['!', ['B_B']], ['B_C']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['B_C'], ['!', ['B_X_over']], ['||', ['R_T_Error > 5'], ['R_T_Error < -5']], ['||', ['R_Roll_attitude > 2.6'], ['R_Roll_attitude < -2.6']], ['||', ['R_X_deviation > 1.5'], ['R_X_deviation < -1.5']], ['||', ['R_dalfadt > 0.075'], ['R_dalfadt < -0.075']], ['||', ['B_h_on'], ['B_f_on']]], ['F', '0', '1', ['&&', ['!', ['B_C']], ['B_B']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['!', ['B_X_over']]], ['F', '0', '5', ['R_LME_cr == 1']]]],
    ['G', '0', T, ['->', ['B_inactive'], ['F', '0', '5', ['R_LME_cr == 0']]]],
    ['G', '0', T, ['->', ['B_armed'], ['F', '0', '5', ['R_LMA_cr == 1']]]],
    ['G', '0', T, ['->', ['B_active'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['B_inactive'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['B_X_over'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['&&', ['B_X_over'], ['B_active']], ['F', '0', '5', ['B_LME_cr']]]],
    ['G', '0', T, ['->', ['B_active'], ['F', '0', '1', ['R_Y_pushbutton == 1']]]],
    ['G', '0', T, ['->', ['B_armed'], ['F', '0', '1', ['R_Y_pushbutton == 2']]]],
    ['G', '0', T, ['->', ['R_airspeed < R_Vmin'], ['F', '0', '5', ['B_LS_amr']]]],
]

parameter_ranges = [
    ['G', '0', T, ['&&', ['R_X_c >=0'], ['R_X_c <= 360']]],
    ['G', '0', T, ['&&', ['R_X_b >=0'], ['R_X_b <= 360']]],
    ['G', '0', T, ['&&', ['R_airspeed >=0'], ['R_airspeed <= 200']]],
    ['G', '0', T, ['&&', ['R_a >= 0'], ['R_a <= 360']]],
    ['G', '0', T, ['||', ['R_n_s == 0'], ['R_n_s == 1'], ['R_n_s == 2']]],
    ['G', '0', T, ['&&', ['R_T_Error >= -180'], ['R_T_Error <= 180']]],
    ['G', '0', T, ['&&', ['R_Roll_attitude >= -50'], ['R_Roll_attitude <= 50']]],
    ['G', '0', T, ['&&', ['R_X_deviation >= -180'], ['R_X_deviation <= 180']]],
    ['G', '0', T, ['||', ['R_LME_cr == 0'], ['R_LME_cr == 1'], ['R_LME_cr == 2']]],
    ['G', '0', T, ['||', ['R_LMA_cr == 0'], ['R_LMA_cr == 1'], ['R_LMA_cr == 2']]],
    ['G', '0', T, ['||', ['R_Y_pushbutton == 0'], ['R_Y_pushbutton == 1'], ['R_Y_pushbutton == 2']]],
]

requirements_inconsistent = [
    ['G', '0', T, ['||', ['&&', ['B_active'], ['!', ['B_active']], ['!', ['B_armed']]], ['&&', ['B_inactive'], ['!', ['B_active']], ['!', ['B_armed']]], ['&&', ['B_armed'], ['!', ['B_inactive']], ['!', ['B_active']]]]],
    ['G', '0', T, ['->', ['&&', ['B_inactive'], ['R_n_s == 1'],  ['R_X_c-R_X_b <= 5'], ['R_X_c-R_X_b>= -5'], ['G', '0', '5', ['R_airspeed>= R_Vmin']], ['!', ['B_X_over']], ['B_X_Activation_Request']], ['F', '0', '2', ['&&', ['!', ['B_inactive']], ['B_active']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['||', ['!', ['R_n_s == 1']], ['F', '0', '10', ['B_X_ch']], ['G', '0', '5', ['R_airspeed < R_Vmin']],  ['!', ['B_r_actuation']], ['!', ['B_X_Activation_Request']]]], ['F', '0', '2', ['&&', ['!', ['B_active']], ['B_inactive']]]]],
    ['G', '0', T, ['->', ['&&', ['B_armed'], ['||', ['!', ['R_n_s ==1']], ['F', '0', '5', ['B_X_ch']], ['!', ['B_X_Activation_Request']], ['!', ['B_r_actuation']]]], ['F', '0', '2', ['&&', ['!', ['B_armed']], ['B_inactive']]]]],
    ['G', '0', T, ['->', ['&&', ['B_inactive'], ['R_n_s ==1'], ['||', ['R_X_c - R_X_b >5'], ['R_X_c - R_X_b <-5']], ['B_X_Activation_Request']], ['F', '0', '2', ['&&', ['!', ['B_inactive']], ['B_armed']]]]],
    ['G', '0', T, ['->', ['&&', ['B_armed'], ['!', ['B_X_over']], ['R_X_c - R_X_b <=5'], ['R_X_c - R_X_b >=-5'], ['G', '0', '5', ['R_airspeed >= R_Vmin']]], ['F', '0', '2', ['&&', ['!', ['B_armed']], ['B_active']]]]], #DOPPIONE (dovrebbe essere stato corretto=
    ['G', '0', T, ['||', ['&&', ['B_active'], ['B_A']], ['&&', ['B_active'], ['B_B']], ['&&', ['B_active'], ['B_C']]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['B_A'], ['!', ['B_X_over']], ['R_Delta_T_Error_reference < R_T_Error'], ['R_Delta_T_Error_reference > 0 - R_T_Error']], ['F', '0', '1', ['&&', ['!', ['B_A']], ['B_B']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['B_B'], ['!', ['B_X_over']], ['R_T_Error < 3'], ['R_T_Error  > -3'],  ['R_Roll_attitude < 0.8'], ['R_Roll_attitude > -0.8'],  ['R_X_deviation < 0.5'], ['R_X_deviation > -0.5'], ['R_dalfadt < 0.002'], ['R_dalfadt > -0.002'], ['!', ['B_h_on']], ['!', ['B_f_on']]], ['F', '0', '1', ['&&', ['!', ['B_B']], ['B_C']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['B_C'], ['!', ['B_X_over']], ['||', ['R_T_Error > 5'], ['R_T_Error < -5']], ['||', ['R_Roll_attitude > 2.6'], ['R_Roll_attitude < -2.6']], ['||', ['R_X_deviation > 1.5'], ['R_X_deviation < -1.5']], ['||', ['R_dalfadt > 0.075'], ['R_dalfadt < -0.075']], ['||', ['B_h_on'], ['B_f_on']]], ['F', '0', '1', ['&&', ['!', ['B_C']], ['B_B']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['!', ['B_X_over']]], ['F', '0', '5', ['R_LME_cr == 1']]]],
    ['G', '0', T, ['->', ['B_inactive'], ['F', '0', '5', ['R_LME_cr == 0']]]],
    ['G', '0', T, ['->', ['B_armed'], ['F', '0', '5', ['R_LMA_cr == 1']]]],
    ['G', '0', T, ['->', ['B_active'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['B_inactive'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['B_X_over'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['&&', ['B_X_over'], ['B_active']], ['F', '0', '5', ['B_LME_cr']]]],
    ['G', '0', T, ['->', ['B_active'], ['F', '0', '1', ['R_Y_pushbutton == 1']]]],
    ['G', '0', T, ['->', ['B_armed'], ['F', '0', '1', ['R_Y_pushbutton == 2']]]],
    ['G', '0', T, ['->', ['R_airspeed < R_Vmin'], ['F', '0', '5', ['B_LS_amr']]]],
]

cars = [
    ['G', '0', '100', ['R_dist > 0.1']],
    ['G', '0', '20', ['->', ['R_dist < 6'], ['F', '0', '15', ['B_acc2']]]],
    ['F', '12', '20', ['->', ['B_dec2'], ['F', '3', '18', ['B_acc2']]]],
    ['F', '4', '40', ['U', '10', '20', ['B_dec2'], ['&&', ['R_x >= -0.5'], ['R_x <= 0.5'], ['R_y >= -0.5'], ['R_y <= 0.5']]]]
]

thermostat = [
    ['G', '0', '40', ['R_x1 <= 21']],
    ['G', '0', '10', ['U', '0', '5', ['R_x2 > 20'], ['B_on1']]],
    ['G', '0', '20', ['R', '2', '12', ['R_x2 > 20'], ['R_x1 < 10']]],
    ['F', '0', '20', ['->', ['&&', ['B_off1'], ['B_off2']], ['G', '0', '5', ['||', ['B_on1'], ['B_on2']]]]]
]

watertank = [
    ['G', '0', '50', ['&&', ['R_x1 > 0'], ['R_x1 <= 9'], ['R_x2 > 0'], ['R_x2 <= 9']]],
    ['G', '0', '10', ['->', ['R_x1 < 4.9'], ['F', '0', '10', ['R_x1 >= 5.1']]]],
    ['F', '5', '14', ['->', ['B_off1'], ['F', '0', '7', ['&&', ['B_on1'], ['R_x1 > 5.5']]]]],
    ['G', '0', '20', ['->', ['&&', ['B_on1'], ['B_on2']], ['F', '0', '5', ['||', ['B_off1'], ['B_off2']]]]]

]

railroad = [
    ['F', '1', '49', ['R_pos <= 0']],
    ['G', '20', '40', ['->', ['R_angle >= 80'], ['F', '1', '20', ['R_pos <= 0']]]],
    ['G', '3', '50', ['F', '5', '20', ['R_angle >= 80']]],
    ['G', '10', '60', ['->', ['R_angle >= 80'], ['G', '20', '40', ['R_angle < 60']]]]
]

batteries = [
    ['G', '1', '20', ['F', '3', '14', ['R_d1 >= 1.4']]],
    ['F', '6', '30', ['->', ['&&', ['B_live1'], ['B_live2']], ['G', '7', '24', ['&&', ['B_live1'], ['B_live2']]]]],
    ['G', '1', '49', ['&&', ['R_d1 > 0.5'], ['R_d2 > 0.5']]],
    ['G', '11', '50', ['U', '2', '14', ['||', ['R_g1 >= 0'], ['R_g2 >= 0']], ['&&', ['B_dead1'], ['B_dead2']]]]
]


def make_and(formulas):
    if len(formulas) == 1:
        return formulas[0]
    return ['&&'] + formulas


# Funzione per eseguire entrambi i test su un dataset
def check_dataset(dataset_name, dataset, max_depth):
    # Formula
    formula = make_and(dataset)
    parser = STLParser()
    parsed_formula = parser.parse_relational_exprs(formula)

    # Prima prova: SMT
    start_t = time.perf_counter()
    res_smt = smt_check_consistency(parsed_formula, 'sat', False)
    elapsed_smt = time.perf_counter() - start_t

    # Seconda prova: Tableau
    start_t = time.perf_counter()
    res_tableau = make_tableau(Node(*formula), max_depth, 'sat', False, False)
    elapsed_tableau = time.perf_counter() - start_t

    # Dizionario con i risultati
    return {
        'dataset': dataset_name,
        'time_smt': elapsed_smt,
        'result_smt': res_smt,
        'time_tableau': elapsed_tableau,
        'result_tableau': res_tableau
    }

# Funzione per stampare i risultati
def pretty_print(results, ms, csvfile):
    timeh, timef = ("Time (ms)", lambda t: t * 1000) if ms else ("Time (s)", lambda x: x)

    # Tabella
    results_matrix = [
        [r['dataset'], timef(r['time_smt']), r['result_smt'], timef(r['time_tableau']), r['result_tableau']]
        for r in results
    ]

    # Intestazione della tabella
    header = ["Dataset", f"SMT {timeh}", "SMT Result", f"Tableau {timeh}", "Tableau Result"]

    print(tabulate(results_matrix, headers=header))

    if csvfile:
        with open(csvfile, 'w', newline='') as f:
            cw = csv.writer(f)
            cw.writerow(header)
            cw.writerows(results_matrix)

# Esecuzione principale
if __name__ == '__main__':
    datasets = {
        "cars": cars,
        "thermostat": thermostat,
        "watertank": watertank,
        #"railroad": railroad,
        "batteries": batteries
    }
    #datasets = [cars, thermostat, watertank, batteries]
    max_depth = 100000

    #results = [check_dataset(ds, max_depth) for ds in datasets]
    results = [check_dataset(name, data, max_depth) for name, data in datasets.items()]

    print("Benchmark results:")
    pretty_print(results, ms=False, csvfile="results.csv")


'''
def test_combinations_with_smt(formulas):
    """
    Testa tutte le combinazioni a due a due di `formulas` usando `smt_check_consistency`.
    Interrompe il ciclo se una combinazione non è soddisfacibile.

    Args:
        formulas (list): Una lista di formule.
        max_depth (int): La profondità massima del tableau.

    Returns:
        tuple: La combinazione che non è soddisfacibile (se trovata) e il relativo tableau.
               Se tutte le combinazioni sono soddisfacibili, restituisce None.
    """
    parser = STLParser()
    for formula_pair in combinations(formulas, 2):  # Genera tutte le combinazioni a due a due
        combined_formula = make_and(list(formula_pair))
        parsed_formula = parser.parse_relational_exprs(combined_formula)
        satisfiable = smt_check_consistency(parsed_formula, False)
        if not satisfiable:  # Se la formula non è soddisfacibile, interrompi
            print(f"Non soddisfacibile trovato per combinazione: {formula_pair}")
            return formula_pair

    print("Tutte le combinazioni sono soddisfacibili.")
    return None

# formula = requirements[0]
formula = make_and(railroad)
# print(formula)

parser = STLParser()
print(formula_to_string(formula))
parsed_formula = parser.parse_relational_exprs(formula)
print(parsed_formula)

start_t = time.perf_counter()
res = smt_check_consistency(parsed_formula, 'sat', False)
#test_combinations_with_smt(requirements)
elapsed_smt = time.perf_counter() - start_t
print('Result (SMT):', res)
print('Elapsed time (SMT):', elapsed_smt)


sys.setrecursionlimit(1000000)
max_depth = 100000
start_t = time.perf_counter()
#tableau, _ = make_tableau(Node(*formula), max_depth, 'sat', True, False)
res = make_tableau(Node(*formula), max_depth, 'sat', False, False)
elapsed_tableau = time.perf_counter() - start_t
print('Result (tableau):', res)
print('Elapsed time (tableau):', elapsed_tableau)

#plot_tree(tableau)



def test_combinations_with_tableau(formulas, max_depth, build_tree, verbose, mode='complete'):
    """
    Testa tutte le combinazioni a due a due di `formulas` usando `make_tableau`.
    Interrompe il ciclo se una combinazione non è soddisfacibile.

    Args:
        formulas (list): Una lista di formule.
        max_depth (int): La profondità massima del tableau.

    Returns:
        tuple: La combinazione che non è soddisfacibile (se trovata) e il relativo tableau.
               Se tutte le combinazioni sono soddisfacibili, restituisce None.
    """
    for formula_pair in combinations(formulas, 2):  # Genera tutte le combinazioni a due a due
        combined_formula = make_and(list(formula_pair))
        if build_tree:
            tableau, satisfiable = make_tableau(Node(*combined_formula), max_depth, mode, build_tree, verbose)
        else:
            satisfiable = make_tableau(Node(*combined_formula), max_depth, mode, build_tree, verbose)
        if not satisfiable:  # Se la formula non è soddisfacibile, interrompi
            print(f"Non soddisfacibile trovato per combinazione: {formula_pair}")
            if build_tree:
                return formula_pair, tableau
            else:
                return formula_pair

    print("Tutte le combinazioni sono soddisfacibili.")
    return None

#start_t = time.perf_counter()
#result = test_combinations_with_tableau(railroad, max_depth, False, False, 'sat')
#elapsed_tableau = time.perf_counter() - start_t

#print('Elapsed time (SMT):', elapsed_smt)
#print('Elapsed time (tableau):', elapsed_tableau)
'''