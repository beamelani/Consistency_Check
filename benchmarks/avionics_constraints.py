import sys
import os
sys.path.append(os.getcwd())

import time
from itertools import combinations
from wrapt_timeout_decorator import *

from stl_consistency.parser import STLParser
from stl_consistency.node import Node, formula_to_string
from stl_consistency.smtchecker import smt_check_consistency

from stl_consistency.tableau import make_tableau, plot_tree

import csv
from tabulate import tabulate

@timeout(dec_timeout='args[0]', dec_allow_eval=True, use_signals=False)
def inner(timeout, f, *args, **kwargs):
    return f(*args, **kwargs)

def run_with_timeout(timeout, f, *args, **kwargs):
    try:
        return inner(timeout, f, *args, **kwargs)
    except TimeoutError as e:
        print(e)
        return "timeout"


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
    ['G', '0', T, ['->', ['&&', ['B_X_over'], ['B_active']], ['F', '0', '5', ['R_LME_cr']]]],
    ['G', '0', T, ['->', ['B_active'], ['F', '0', '1', ['R_Y_pushbutton == 1']]]],
    ['G', '0', T, ['->', ['B_armed'], ['F', '0', '1', ['R_Y_pushbutton == 2']]]],
    ['G', '0', T, ['->', ['R_airspeed < R_Vmin'], ['F', '0', '5', ['B_LS_amr']]]],
]

requirements_riscritti = [
    ['G', '0', T, ['||', ['R_function_status == 0'], ['R_function_status == 1'], ['R_function_status == 2']]], #where 0 == inactive, 1==armed, 2==active
    ['G', '0', T, ['->', ['&&', ['R_function_status == 0'], ['R_n_s == 1'],  ['R_X_c-R_X_b <= 5'], ['R_X_c-R_X_b>= -5'], ['G', '0', '5', ['R_airspeed>= R_Vmin']], ['Not(B_X_over)'], ['B_X_Activation_Request']], ['F', '1', '2', ['R_function_status == 2']]]],
    ['G', '0', T, ['->', ['&&', ['R_function_status == 2'], ['||', ['!', ['R_n_s == 1']], ['F', '0', '10', ['B_X_ch']], ['G', '0', '5', ['R_airspeed < R_Vmin']],  ['Not(B_r_actuation)'], ['Not(B_X_Activation_Request)']]], ['F', '1', '2', ['R_function_status == 0']]]],
    ['G', '0', T, ['->', ['&&', ['R_function_status == 1'], ['||', ['!', ['R_n_s ==1']], ['F', '0', '5', ['B_X_ch']], ['Not(B_X_Activation_Request)'], ['Not(B_r_actuation)']]], ['F', '1', '2', ['R_function_status == 0']]]],
    ['G', '0', T, ['->', ['&&', ['R_function_status == 0'], ['R_n_s ==1'], ['||', ['R_X_c - R_X_b >5'], ['R_X_c - R_X_b <-5']], ['B_X_Activation_Request']], ['F', '1', '2', ['R_function_status == 1']]]],
    ['G', '0', T, ['->', ['&&', ['R_function_status == 1'], ['Not(B_X_over)'], ['R_X_c - R_X_b <=5'], ['R_X_c - R_X_b >=-5'], ['G', '0', '5', ['R_airspeed >= R_Vmin']]], ['F', '1', '2', ['R_function_status == 2']]]],
    ['G', '0', T, ['->', ['R_function_status == 2'], ['||', ['R_function_active_status == 0'], ['R_function_active_status == 1'], ['R_function_active_status == 2']]]],
    ['G', '0', T, ['->', ['&&', ['R_function_active_status == 0'], ['Not(B_X_over)'], ['R_Delta_T_Error_reference < R_T_Error'], ['R_Delta_T_Error_reference > 0 - R_T_Error']], ['F', '0', '1', ['R_function_active_status == 1']]]],
    ['G', '0', T, ['->', ['&&', ['R_function_active_status == 1'], ['Not(B_X_over)'], ['R_T_Error < 3'], ['R_T_Error  > -3'],  ['R_Roll_attitude < 0.8'], ['R_Roll_attitude > -0.8'],  ['R_X_deviation < 0.5'], ['R_X_deviation > -0.5'], ['R_dalfadt < 0.002'], ['R_dalfadt > -0.002'], ['Not(B_h_on)'], ['Not(B_f_on)']], ['F', '0', '1', ['R_function_active_status == 2']]]],
    ['G', '0', T, ['->', ['&&', ['R_function_active_status == 2'], ['Not(B_X_over)'], ['||', ['R_T_Error > 5'], ['R_T_Error < -5']], ['||', ['R_Roll_attitude > 2.6'], ['R_Roll_attitude < -2.6']], ['||', ['R_X_deviation > 1.5'], ['R_X_deviation < -1.5']], ['||', ['R_dalfadt > 0.075'], ['R_dalfadt < -0.075']], ['||', ['B_h_on'], ['B_f_on']]], ['F', '0', '1', ['R_function_active_status == 1']]]],
    ['G', '0', T, ['->', ['&&', ['R_function_status == 2'], ['Not(B_X_over)']], ['F', '0', '5', ['R_LME_cr == 1']]]],
    ['G', '0', T, ['->', ['R_function_status == 0'], ['F', '0', '5', ['R_LME_cr == 0']]]],
    ['G', '0', T, ['->', ['R_function_status == 1'], ['F', '0', '5', ['R_LMA_cr == 1']]]],
    ['G', '0', T, ['->', ['R_function_status == 2'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['R_function_status == 0'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['B_X_over'], ['F', '0', '5', ['&&', ['B_LMT_ar'], ['B_a_tone']]]]],
    ['G', '0', T, ['->', ['&&', ['B_X_over'], ['R_function_status == 2']], ['F', '0', '5', ['R_LME_cr']]]],
    ['G', '0', T, ['->', ['R_function_status == 2'], ['F', '0', '1', ['R_Y_pushbutton == 1']]]],
    ['G', '0', T, ['->', ['R_function_status == 1'], ['F', '0', '1', ['R_Y_pushbutton == 2']]]],
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

'''
#Requisiti da: Benchmarks for Temporal Logic Requirements for Automotive Systems
t = '10' #alcuni requisiti sono da 0 a un tempo t
T = '100' #quando il requisito ha unboundend operators
mtl_requirements = [
    ['G', '0', T, ['&&', ['R_omega < R_omega_hat'], ['R_v < R_v_hat']]],
    ['G', '0', T, ['->', ['&&', ['B_g2'], ['G', '1', '1', ['B_g1']]], ['G', '0.5', '2.5', ['!', ['B_g2']]]]],
    ['G', '0', T, ['->', ['&&', ['!', ['B_g1']], ['G', '1', '1', ['B_g1']]], ['G', '0.5', '2.5', ['B_g1']]]],
    ['G', '0', T, ['->', ['&&', ['!', ['B_g2']], ['G', '1', '1', ['B_g2']]], ['G', '0.5', '2.5', ['B_g2']]]],
    ['G', '0', T, ['->', ['&&', ['!', ['B_g3']], ['G', '1', '1', ['B_g3']]], ['G', '0.5', '2.5', ['B_g3']]]],
    ['G', '0', T, ['->', ['&&', ['!', ['B_g4']], ['G', '1', '1', ['B_g4']]], ['G', '0.5', '2.5', ['B_g4']]]],
    ['!', ['&&', ['F', '0', t, ['R_v > R_v_hat']], ['G', '0', T, ['R_omega < R_omega_hat']]]],
    ['F', '0', t, ['&&', ['R_v >= R_v_hat'], ['G', '0', T, ['R_omega < R_omega_hat']]]],
    ['F', '0', '100', ['G', '0', '1', ['Not(R_Fuel_Flow_Rate == 0)']]],
    ['G', '0', T, ['->', ['B_lambda_OOB'], ['F', '0', '1', ['G', '0', '1', ['Not(B_lambda_OOB)']]]]]

]

#Requisiti da: Powertrain Control Verification Benchmark
T = '100' #questo valore scelto a caso, gli altri presi dal paper
epsilon = '0.02' #short interval
t_s = '11'
eta = '1'
zeta_mezzi = '10'#zeta è il periodo del pulse train signal
pcv = [
    # rise(a) = ['&&', ['R_theta == 8.8'], ['F', '0', epsilon, ['R_theta == R_a']]] sono usati in altri req
    # fall (a) = ['&&', ['R_theta == R_a'], ['F', '0', epsilon, ['R_theta == 8.8']]]
    # normal mode
    ['G', '0', T, ['->', ['B_normal_mode'], ['&&', ['R_a > 8.8'], ['R_a < 70']]]],
    ['G', t_s, T, ['->', ['B_normal_mode'], ['&&', ['R_mu > -0.05'], ['R_mu < 0.05']]]],
    ['G', t_s, T, ['->', ['||', [['&&', ['R_theta == 8.8'], ['F', '0', epsilon, ['R_theta == R_a']]]], [['&&', ['R_theta == R_a'], ['F', '0', epsilon, ['R_theta == 8.8']]]]], ['G', eta, zeta_mezzi, ['&&', ['R_mu > - 0.02'], ['R_mu < 0.02']]]]],
    ['F', T, T, ['->', ['B_normal_mode'], ['R_xrms < 0.05']]],
    ['G', t_s, T, ['->', ['B_normal_mode'], ['R_mu > -0.1']]],
    ['G', t_s, T, ['->', ['B_normal_mode'], ['R_mu < 0.1']]],
    #power mode
    ['G', '0', T, ['->', ['B_power_mode'], ['&&', ['R_a >= 8.8'], ['R_a <= 90']]]],
    ['G', t_s, T, ['->', ['&&', ['B_power_mode'], ['F', '0', epsilon, ['B_normal_mode']]], ['G', eta, zeta_mezzi, [['&&', ['R_mu > -0.02'], ['R_mu < 0.02']]]]]],
    ['G', t_s, T, ['->', ['B_power_mode'], ['&&', ['R_mu_p > -0.2'], ['R_mu_p < 0.2']]]],
    # startup and sensor fail mode
    ['G', '0', T, ['->', ['&&', ['||', ['B_startup_mode'], ['B_sensor_fail_mode']], ['||', [['&&', ['R_theta == 8.8'], ['F', '0', epsilon, ['R_theta == R_a']]]], [['&&', ['R_theta == R_a'], ['F', '0', epsilon, ['R_theta == 8.8']]]]]], ['G', eta, zeta_mezzi, [['&&', ['R_mu > - 0.1'], ['R_mu < 0.1']]]]]]
]

#requisiti da Signal-Based Properties of Cyber-Physical Systems: Taxonomy and Logic-based Characterization
T = '3000'
req_cps =[
    ['G', '0', T, ['||', ['R_currentADCSMode == 0'], ['R_currentADCSMode == 1'], ['R_currentADCSMode == 2']]], # P1 where 0 == NMC, 1== NMF, 2== SM
    # P2: non serve, basta definire il segnale come bool
    # P3: non serve, basta definire il segnale come bool
    ['G', '0', T, ['R_RWs_angular_velocity == 816.814']], # P4
    ['G', '2000', T, ['R_pointing_error < 2']], # P5
    ['G', '1500', '2000', ['R_RWs_angular_momentum < 0.35']], # P6
    ['G', '2000', '2000', ['&&', ['R_pointing_error > 0'], ['R_pointing_error < R_delta']]], # P7 delta???
    ['F', '2000', '7400', ['&&', ['R_pointing_error < R_k'], ['U', '2', '22', ['R_pointing_error >= R_k'], ['R_pointing_error < R_k']]]], # P8 SPIKE
    #[], # P9 OSCILLATION
    ['G', '0', T, ['&&', ['R_sat_init_angular_velocity_degree <= 3'], ['R_sat_init_angular_velocity_degree >= -3']]], # P10
    ['G', '2000', T, ['&&', ['R_sat_real_angular_velocity <= 1.5'], ['R_sat_real_angular_velocity >= -1.5']]], # P11
    ['G', '0', T, ['||', ['R_sat_target_attitude == 1'], ['R_sat_target_attitude == -1']]], # P12
    ['G', '2000', T, ['&&', ['R_sat_target_angular_velocity <= 1.5'], ['R_sat_target_angular_velocity >= -1.5']]], # P13
    ['G', '0', T, ['||', ['R_sat_estimated_attitude == 1'], ['R_sat_estimated_attitude == -1']]], # P14
    ['G', '2000', T, ['&&', ['R_sat_estimated_angular_velocity <= 1.5'], ['R_sat_estimated_angular_velocity >= -1.5']]], # P15
    ['G', '2000', T, ['&&', ['R_sat_angular_velocity_measured <= 1.5'], ['R_sat_angular_velocity_measured >= -1.5']]], # P16
    ['G', '0', T, ['&&', ['R_earth_mag_field_in_body_measured <= 60000'], ['R_earth_mag_field_in_body_measured >= -60000']]], # P17
    ['G', '0', T, ['||', ['R_sun_direction_ECI == 1'], ['R_sun_direction_ECI == -1']]], # P18
    ['G', '2000', T, ['&&', ['R_sat_target_angular_velocity_safe_spin_mode <= 1.5'], ['R_sat_target_angular_velocity_safe_spin_mode >= -1.5']]], # P19
    ['G', '0', T, ['&&', ['R_RWs_torque <= 0.015'], ['R_RWs_torque >= -0.015']]], # P20
    ['G', '0', T, ['R_sun_sensor_availability <= 3']], # P21 traduzioe non perfetta, ma good enough
    ['G', '2000', '2000', ['&&', ['R_q_real - R_q_estimate_attitude > 0'], ['R_q_real - R_q_estimate_attitude < R_delta']]], # P22
    ['G', '2000', '2000', ['&&', ['R_q_target_attitude - R_q_estimate > 0'], ['R_q_target_attitude - R_q_estimate < R_delta']]], # P23
    ['G', '0', T, ['&&', ['R_sat_estimated_angular_velocity - R_sat_real_angular_velocity > 0'], ['R_sat_estimated_angular_velocity - R_sat_real_angular_velocity < R_delta']]], # P24
    ['G', '0', T, ['&&', ['R_sat_angular_velocity_measured - R_sat_real_angular_velocity > 0'], ['R_sat_angular_velocity_measured - R_sat_real_angular_velocity < R_delta']]], # P25
    #[], # P26 derivative?
    ['G', '0', T, ['->', ['Not(B_not_Eclipse)'], ['Not(B_sun_currents)']]], # P27
    ['G', '0', T, ['->', ['B_pointing_error_under_15'], ['Not(B_pointing_error_above_20)']]], # P28
    ['G', '0', T, ['->', ['B_pointing_error_above_20'], ['Not(B_pointing_error_under_15']]], # P29
    ['G', '0', T, ['->', ['R_RWs_command == 0'], ['F', '0', '60', ['RWs_angular_velocity == 0']]]], # P30 monotonically decreasing come lo esprimo??
    ['G', '0', T, ['->', ['R_RWs_angular_momentum > 0.35'], ['R_RWs_torque == 0']]], # P31
    ['G', '0', T, ['->', ['R_currentADCSMode == 0'], ['R_control_error >= 10']]], # P32
    ['G', '0', T, ['->', ['R_control_error < 10'], ['R_currentADCSMode == 1']]], # P33
    ['G', '0', T, ['->', ['R_currentADCSMode == 1'], ['R_control_error <= 15']]], # P34
    ['G', '0', T, ['->', ['R_currentADCSMode == 1'], ['->', ['R_RWs_command > 0'], ['F', '0', '180', ['R_pointing_error < 2']]]]], # P35
    ['G', '0', T, ['->', ['R_currentADCSMode == 1'], ['->', ['R_RWs_command > 0'], ['F', '0', '180', ['R_control_error < 0.5']]]]], # P36
    ['G', '0', T, ['->', ['R_currentADCSMode == 1'], ['->', ['B_not_Eclipse'], ['F', '0', '900', ['R_knowledge_error < 1']]]]], # P37
    ['G', '0', T, ['->', ['R_currentADCSMode == 2'], ['->', ['R_RWs_command > 0'], ['F', '0', '900', ['R_RWs_angular_momentum < 0.25']]]]], # P38
    ['G', '0', T, ['->', ['R_currentADCSMode == 2'], ['F', '0', '10799', ['R_real_Omega - R_signal_target_Omega == 0']]]], # P39
    ['G', '0', T, ['->', ['B_not_Eclipse'], ['R_sun_angle < 45']]], # P40
    ['G', '16200', T, ['->', ['R_pointing_error < 2'], ['F', '0', '5400', ['&&', ['R_pointing_error < R_k2'], ['U', '0', '600', ['R_pointing_error >= R_k'], ['R_pointing_error < R_k2']]]]]] # P41

]
'''
#Requisiti da Bounded Model Checking of STL Properties using Syntactic Separation
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
def check_dataset(dataset_name, dataset, max_depth, timeout):
    # Formula
    formula = make_and(dataset)
    parser = STLParser()
    parsed_formula = parser.parse_relational_exprs(formula)

    # Prima prova: SMT
    start_t = time.perf_counter()
    res_smt = run_with_timeout(timeout, smt_check_consistency, parsed_formula, 'sat', False)
    elapsed_smt = time.perf_counter() - start_t

    # Seconda prova: Tableau
    start_t = time.perf_counter()
    res_tableau = run_with_timeout(timeout, make_tableau, Node(*formula), max_depth, 'sat', False, False, False)
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
        #"avionics": requirements_riscritti,
        #"cars": cars,
        #"thermostat": thermostat,
        #"watertank": watertank,
        "railroad": railroad,
        #"batteries": batteries
    }
    #datasets = [cars, thermostat, watertank, batteries]
    max_depth = 100000
    timeout = 100 # in seconds

    #results = [check_dataset(ds, max_depth) for ds in datasets]
    results = [check_dataset(name, data, max_depth, timeout) for name, data in datasets.items()]

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
formula = make_and(requirements_riscritti)
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
res = make_tableau(Node(*formula), max_depth, 'sat', False, True, False)
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