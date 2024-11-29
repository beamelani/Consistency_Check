import sys
import os
sys.path.append(os.getcwd())

import time

from stl_consistency.parser import STLParser
from stl_consistency.node import Node, formula_to_string
from stl_consistency.smtchecker import smt_check_consistency

from stl_consistency.tableau import make_tableau, plot_tree

# Benchmark: (avionics requirements)
# 1) stabilire un time horizon (T)
T = str(10)
requirements = [
    ['G', '0', T, ['||', ['&&', ['B_active'], ['!', ['B_inactive']], ['!', ['B_armed']] ], ['&&', ['B_inactive'], ['!', ['B_active']], ['!', ['B_armed']]], ['&&', ['B_armed'], ['!', ['B_inactive']], ['!', ['B_active']]]]],
    ['G', '0', T, ['->', ['&&', ['B_inactive'], ['R_n_s == 1'],  ['R_X_c-R_X_b <= 5'], ['R_X_c-R_X_b>= -5'], ['G', '0', '5', ['R_airspeed>= R_Vmin']], ['!', ['B_X_over']], ['B_X_Activation_Request']], ['F', '0', '2', ['&&', ['!', ['inactive']], ['active']]]]],
    ['G', '0', T, ['->', ['&&', ['active'], ['||', ['!', ['R_n_s == 1']], ['F', '0', '10', ['B_X_ch']], ['G', '0', '5', ['R_airspeed < R_Vmin']],  ['!', ['B_r_actuation']], ['!', ['B_X_Activation_Request']]], ['F', '0', '2', ['&&', ['!', ['B_active']], ['B_inactive']]]]]],
    ['G', '0', T, ['->', ['&&', ['B_armed'], ['||', ['!', ['R_n_s ==1']], ['F', '0', '5', ['B_X_ch']], ['!', ['B_X_Activation_Request']], ['!', ['B_r_actuation']]]], ['F', '0', '2', ['&&', ['!', ['B_armed']], ['B_inactive']]]]],
    ['G', '0', T, ['->', ['&&', ['B_inactive'], ['R_n_s ==1'], ['||', ['R_X_c - R_X_b >5'], ['R_X_c - R_X_b <-5']], ['B_X_Activation_Request'] ], ['F', '0', '2', ['&&', ['!', ['B_inactive']], ['B_armed']]]]],
    ['G', '0', T, ['->', ['&&', ['B_armed'], ['!', ['B_X_over']], ['R_X_c - R_X_b <=5'], ['R_X_c - R_X_b >=-5'], ['G', '0', '5', ['R_airspeed >= R_Vmin']] ], ['F', '0', '2', ['&&', ['!', ['B_armed']], ['B_active']]]]], #DOPPIONE
    ['G', '0', T, ['||', ['&&', ['B_active'], ['B_A'] ], ['&&', ['B_active'], ['B_B']], ['&&', ['B_active'], ['B_C']]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['B_A'], ['!', ['B_X_over']], ['R_Delta_T_Error_reference < |T Error|'], ['R_Delta_T_Error_reference > -|R_T_Error|']], ['F', '0', '1', ['&&', ['!', ['B_A']], ['B_B']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['B_B'], ['!', ['B_X_over']], ['R_T_Error < | 3'], ['R_T_Error  > -3'] ,  ['R_Roll_attitude < 0.8'], ['R_Roll_attitude > -0.8'],  ['R_X_deviation < 0.5'], ['R_X_deviation > -0.5'] , ['R_dalfa/dt < 0.002'], ['R_dalfa/dt > -0.002'], ['!', ['B_h_on']], ['!', ['B_f_on']]], ['F', '0', '1', ['&&', ['!', ['B_B']], ['B_C']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['B_C'], ['!', ['B_X_over']], ['||', ['R_T_Error > 5'], ['R_T_Error < -5']], ['||', ['R_Roll_attitude > 2.6'], ['R_Roll_attitude < -2.6']], ['||', ['R_X_deviation > 1.5'], ['R_X_deviation < -1.5']], ['||', ['R_dalfa/dt > 0.075'], ['R_dalfa/dt < -0.075']], ['||', ['B_h_on'], ['B_f_on']]], ['F', '0', '1', ['&&', ['!', ['B_C']], ['B_B']]]]],
    ['G', '0', T, ['->', ['&&', ['B_active'], ['!', ['B_X_over']]], ['F', '0', '5', ['R_LME_cr == 1']]]],
    ['G', '0', T, ['->', ['B_inactive'], ['F', '0', '5', ['R_LME_cr == 0']]]],
    ['G', '0', T, ['->', ['B_armed'], ['F', '0', '5', ['R_LMA_cr == 1']]]],
    ['G', '0', T, ['->', ['B_active'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['B_inactive'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['B_X_over'] , ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['&&', ['B_X_over'], ['B_active'] ] , ['F', '0', '5', ['B_LME_cr']]]],
    ['G', '0', T, ['->', ['B_active'] , ['F', '0', '1', ['R_Y_pushbutton == 1']]]],
    ['G', '0', T, ['->', ['B_armed'] , ['F', '0', '1', ['R_Y_pushbutton == 2']]]],
    # ['G', '0', T, ['->', ['&&', ['R_airspeed < Vmin'], [????]] , ['F', '0', '5', ['B_LS_amr']]]],
]

parameter_ranges = [
    ['G', '0', T, ['&&', ['R_X_c >=0'], ['R_X_c <= 360']]],
    ['G', '0', T, ['&&', ['R_X_b >=0'], ['R_X_b <= 360']]],
    ['G', '0', T, ['&&', ['R_airspeed >=0'], ['R_airspeed <= 200']]],
    ['G', '0', T, ['&&', ['R_a >= 0'], ['R_a <= 360']]],
    ['G', '0', T, ['||', ['R_n_s == 0'], ['R_n_s == 1'], ['R_n_s == 2']]],
    ['G', '0', T, ['&&', ['R_T_Error >= -180'], ['R_T_Error <= 180']]],
    ['G', '0', T, ['&&', ['R_Roll_attitude >= -50'], ['R_Roll_attitude <= 50']]],
    ['G', '0', T, ['&&', ['R_X_deviation >= -180'], ['R_X_deviation <= 180'] ]],
    ['G', '0', T, ['||', ['R_LME_cr == 0'], ['R_LME_cr == 1'], ['R_LME_cr == 2']]],
    ['G', '0', T, ['||', ['R_LMA_cr == 0'], ['R_LMA_cr == 1'], ['R_LMA_cr == 2']]],
    ['G', '0', T, ['||', ['R_Y_pushbutton == 0'], ['R_Y_pushbutton == 1'], ['R_Y_pushbutton == 2']]],
]

formula = requirements[18]

# TODO: to be removed after making intermediate representation uniform
parser = STLParser()
print(formula_to_string(formula))
parsed_formula = parser.parse_formula_as_list(formula_to_string(formula))

start_t = time.perf_counter()

smt_check_consistency(parsed_formula, True)

elapsed = time.perf_counter() - start_t
print('Elapsed time:', elapsed)


max_depth = 5
tableau = make_tableau(Node(*formula), max_depth)

plot_tree(tableau)
