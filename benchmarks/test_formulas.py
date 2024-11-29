import sys
import os
sys.path.append(os.getcwd())

from stl_consistency.parser import STLParser
from stl_consistency.node import formula_to_string
from stl_consistency.smtchecker import smt_check_consistency

# formula = [['&&', ['G', '1/3', '9', ['B_p']], ['F', '4', '7', ['B_q']]]]
# formula = [['&&', ['G', '0.5', '9', ['B_p']], ['F', '4', '7', ['B_q']]]]
# formula = [['&&', ['G', '0.0', '9.0', ['B_p']], ['F', '4.0', '7.0', ['B_q']]]] #ok
# formula = [['&&', ['G', '0', '2', ['B_p']], ['F', '1', '3', ['!', ['B_p']]]]] #ok
# formula = [['G', '0', '2', ['&&', ['p'], ['q']]]] #come gestirlo? vedi sotto
# formula = [['G', '0', '2', ['And(B_p, B_q)']]]
# formula = [['F', '0', '5', ['B_q']]]
# formula = [['||', ['G', '0', '2', ['B_p']], ['F', '1', '3', ['B_q']]]] #ok
# formula = [['&&', ['F', '0', '2', ['B_p']], ['F', '1', '3', ['B_q']]]] #ok
# formula = [['G', '0', '3', ['F', '0', '2', ['B_p']]]]
# formula = [['F', '0', '3', ['G', '1', '4', ['B_p']]]]
# formula = [['G', '0', '5', ['G', '1', '3', ['B_p']]]]
# formula = [['F', '0', '5', ['F', '1', '4', ['B_p']]]]
# formula = [['&&', ['F', '0', '3', ['G', '1', '4', ['B_p']]], ['G', '0', '3', ['B_y']]]]
# formula = [['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['B_p']]]]]
# formula = [['G', '0', '3', ['F', '1', '4', ['G', '0', '2', ['F', '1', '3', ['B_p']]]]]] #problemi con la funz che plotta se depth >5
# formula = [['&&', ['F', '0', '3', ['G', '1', '4', ['B_p']]], ['G', '1', '6', ['!', ['B_p']]]]] #ok
# formula = [['&&', ['G', '0', '3', ['F', '1', '4', ['B_p']]], ['F', '1.0', '3.0', ['B_q']]]] #ok
# formula = [['&&', ['G', '0', '4', ['R_x>5']], ['F', '2', '4', ['R_x<2']]]] #consistency check ok
# formula = [['&&', ['G', '0', '4', ['R_x>5']], ['F', '2', '4', ['R_y<2']]]] #consistency check ok
# formula = [['&&', ['G', '0', '4', ['R_x>5']], ['F', '2', '4', ['R_y<2']], ['F', '1', '5', ['R_x == 4']]]] #ok
# formula = [['&&', ['G', '0', '4', ['Implies(B_q, R_x>2)']], ['F', '0', '4', ['Implies(B_q, R_x<1)']]]] #il ris mi confonde
# formula = [['&&', ['G', '0', '4', ['Implies(B_q, Not(B_p))']], ['F', '0', '4', ['Implies(B_q, B_p)']]]]
# formula = [['G', '0', '4', ['And(Implies(B_q, Not(B_p)), Implies(B_q, B_p))']]]
# formula = [['G', '0', '4', ['And(B_q, Not(B_q))']]]
# formula = [['&&', ['G', '0', '4', ['And(B_p, Not(B_p))']], ['F', '0', '4', ['R_x>9']]]]
# formula = [['&&', ['G', '0', '4', ['And(B_p, Not(B_p))']], ['F', '0', '4', ['R_x>9']]]]
# formula = [['U', '0', '5', ['B_p'], ['B_q']]]
# formula = [['&&', ['U', '0', '5', ['B_p'], ['B_q']], ['G', '0', '4', ['B_p']]]]
# formula = [['U', '1', '3', ['G', '1', '4', ['B_p']], ['B_q']]]
# formula = [['U', '1', '3', ['B_q'], ['G', '1', '4', ['B_p']]]]
# formula = [['U', '1', '3', ['G', '1', '4', ['B_p']], ['G', '2', '5', ['B_q']]]]
# formula = [['&&', ['G', '0', '7', ['F', '1', '3', ['B_p']]], ['G', '2', '9', ['B_y']]]]
# formula = [['G', '0', '7', ['F', '1', '3', ['B_p']]]]

#formula = ['&&', ['G', '0', '9', ['R_x>5']], ['F', '4', '7', ['R_x<4']]]
#formula = ['&&', ['G', '0', '9', ['B_p']], ['F', '4', '7', ['!', ['B_p']]]]
#formula = ['||', ['G', '0', '9', ['B_p']], ['F', '4', '7', ['B_q']], ['G', '1', '6', ['B_z']]]
#formula = ['F', '4', '7', ['B_q']]
#formula = [',', ['G', '1', '9', ['F', '2', '5', ['B_q']]], ['G', '0', '10', ['B_p']]]
#formula = ['&&', ['G', '0', '10', ['F', '1', '2', ['B_p']]], ['G', '6', '9', ['B_q']]] #sembra ok
#formula = ['&&', ['G', '0', '10', ['F', '1', '2', ['B_p']]], ['F', '3', '10', ['F', '1', '2', ['B_p']]]]
#formula = ['&&', ['G', '0', '2', ['F', '1', '10', ['B_p']]], ['G', '6', '9', ['B_q']]]
#formula = ['U', '5', '8', ['B_q'], ['B_p']]
#formula = ['U', '1', '5', ['G', '1', '2', ['B_p']], ['B_q']]
#formula = ['U', '1', '3', ['B_p'], ['B_q']]
#formula = ['&&', ['G', '3', '5', ['B_p']], ['U', '0', '7', ['B_q'], ['G', '0', '3', ['B_z']]]]
#formula = ['R', '2', '9', ['B_p'], ['B_q']]
#formula = ['R', '0', '9', ['U', '2', '9', ['B_p'], ['B_z']], ['B_q']] #no problemi
#formula = ['R', '0', '9', ['B_q'], ['R', '2', '9', ['B_p'], ['B_z']]]
#formula = ['R', '2', '9', ['B_q'], ['B_p']]
#formula = ['&&', ['G', '0', '5', ['B_z']], ['R', '0', '9', ['B_q'], ['G', '0', '9', ['B_p']]]]
#formula = ['U', '0', '9', ['G', '0', '2', ['B_p']], ['B_q']] #problematico il salto
#formula = ['U', '0', '9', ['B_q'], ['F', '0', '3', ['B_p']]] #no problemi
#formula = ['&&', ['G', '0', '9', ['B_p']], ['R', '2', '4', ['B_q'], ['B_z']]]
#formula = ['&&', ['G', '0', '9', ['B_p']], ['G', '1', '7', ['||', ['B_q'], ['B_z']]]]
#formula = ['G', '0', '6', ['U', '2', '4', ['B_p'], ['B_q']]]
#formula = ['F', '1', '6', ['G', '1', '3', ['B_p']]]
#formula = ['G', '0', '2', ['G', '1', '4', ['B_p']]]
#formula = ['U', '0', '2', ['G', '1', '4', ['B_p']], ['B_q']]
#formula = ['->', ['G', '1', '4', ['B_p']], ['B_q']]
#formula = ['&&', ['->', ['G', '1', '4', ['B_p']], ['B_q']], ['G', '1', '7', ['||', ['B_x'], ['B_z']]]]
#formula = ['&&', ['->', ['G', '1', '4', ['B_p']], ['B_q']], ['->', ['G', '1', '7', ['B_p']], ['B_z']]]
#formula = ['->', ['B_p'], ['B_q']]
#formula = ['&&', ['->', ['G', '1', '4', ['B_p']], ['B_q']], ['->', ['F', '2', '3', ['!', ['B_p']]], ['B_z']]]

# TODO: to be removed after making intermediate representation uniform
parser = STLParser()
print(formula_to_string(formula))
parsed_formula = parser.parse_formula_as_list(formula_to_string(formula))

smt_check_consistency(parsed_formula, True)
