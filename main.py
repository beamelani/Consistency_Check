# MIT License
#
# Copyright (c) 2024 Ezio Bartocci, Beatrice Melani
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


# STL Requirements Consistency Checking (ver 0.41)
# Date: 28-04-2024
#
#

from z3 import *
from pyparsing import (Optional, Combine, Literal, Word, alphas, nums, alphanums, Group, Forward, infixNotation, opAssoc, oneOf)

class SyntaxError(Exception):
    """Base class for other exceptions"""
    pass


class STLConsistencyChecker:

    def __init__(self):
        self._variables          = {}  # Protected variable
        self._real_constraints   = {}  # Protected variable
        self._binary_constraints = {}  # Protected variable
        self._sub_formulas       = {}  # Protected variable
        self._prop_count         = 0   # Protected variable

    def _addSubFormula (self, sub_formula):
        key_formula = f"_phi{self._prop_count}"
        self._sub_formulas[key_formula] = sub_formula
        self._prop_count = self._prop_count + 1
        return key_formula

    def getVariableList (self):
        return self._variables

    def getRealConstraintsList (self):
        return self._real_constraints

    def getBinaryConstraintsList (self):
        return self._binary_constraints

    def getBasicPropositionsList (self):
        return self._sub_formulas

    def getNumProp (self):
        return self._prop_count

    def printSubFormulas (self):
        # Print the list of the subformulas
        print("")
        print("List of subformulas")
        print("===================")
        print("")
        for key in self._sub_formulas.keys():
            # Key is the name of the formula
            # Now we check the type of the formula
            if len(self._sub_formulas[key]) == 1:
            # The subformula is a binary variable
                print(f"{key} = {self._sub_formulas[key][0]} (Binary variable)")
            elif len(self._sub_formulas[key]) == 3 and self._sub_formulas[key][1] in {'<', '<=', '>', '>=', '==', '!='}:
            # The subformula is a predicate over the real variable
                print(f"{key} = {self._sub_formulas[key][0]} {self._sub_formulas[key][1]} {self._sub_formulas[key][2]} (Real constraint)")
            elif len(self._sub_formulas[key]) == 4 and self._sub_formulas[key][0] == "G":
            # The subformula is always
                print(f"{key} = {self._sub_formulas[key][0]} [{self._sub_formulas[key][1]}, {self._sub_formulas[key][2]}] {self._sub_formulas[key][3]} (Always)")
            elif len(self._sub_formulas[key]) == 4 and self._sub_formulas[key][0] == "F":
            # The subformula is eventually
                print(f"{key} = {self._sub_formulas[key][0]} [{self._sub_formulas[key][1]}, {self._sub_formulas[key][2]}] {self._sub_formulas[key][3]} (Eventually)")
            elif len(self._sub_formulas[key]) == 5 and self._sub_formulas[key][0] == "U":
            # The subformula is until
                print(f"{key} = {self._sub_formulas[key][3]} {self._sub_formulas[key][0]} [{self._sub_formulas[key][1]}, {self._sub_formulas[key][2]}] {self._sub_formulas[key][4]} (Until)")
            elif len(self._sub_formulas[key]) == 3 and self._sub_formulas[key][0] == "&&":
            #The subformula is an &&
                print(f"{key} = {self._sub_formulas[key][1]} {self._sub_formulas[key][0]}  {self._sub_formulas[key][2]}   (And)")
            elif len(self._sub_formulas[key]) == 3 and self._sub_formulas[key][0] == "||":
            #The subformula is an Or
                print(f"{key} = {self._sub_formulas[key][1]} {self._sub_formulas[key][0]}  {self._sub_formulas[key][2]}   (Or)")
            elif len(self._sub_formulas[key]) == 2 and self._sub_formulas[key][0] == "!":
            #The subformula is a Not
                print(f"{key} = {self._sub_formulas[key][0]} {self._sub_formulas[key][1]}   (Not)")
        print("")



    def print_vars(self):
        print(self._variables)
        print(self._real_constraints)
        print(self._binary_constraints)
        print(self._sub_formulas)

    def _create_stl_parser(self):
        # Basic elements
        identifier = Word(alphas, alphanums + "_")

        # Expression for integer
        non_zero_digit = "123456789"
        zero = "0"
        integer_number = Word(non_zero_digit, nums) | zero

        # Expression for real
        point = "."
        e = Word("eE", exact=1)
        plus_or_minus = Word("+-", exact=1)
        real_number = Combine(Optional(plus_or_minus) + Word(nums) + Optional(point + Optional(Word(nums))) + Optional(
            e + Optional(plus_or_minus) + Word(nums)))

        # Define relational operators
        relational_op = oneOf("< <= > >= == !=")

        # Logical operators
        unary_logical_op = Literal('!')
        binary_logical_op = oneOf("&& || -> <->")

        interval = Literal('[') + integer_number + Literal(',') + integer_number + Literal(']')

        # Temporal operators
        unary_temporal_op = oneOf("G F")
        unary_temporal_prefix = unary_temporal_op + interval

        binary_temporal_op = Literal('U')
        binary_temporal_prefix = binary_temporal_op + interval

        # Define expressions
        expr = Forward()

        # Parentheses for grouping
        parens = Group(Literal("(") + expr + Literal(")"))

        # Building the expressions
        binary_relation = Group(identifier + relational_op + real_number) | Group(
            identifier + relational_op + identifier)
        binary_variable = Group(identifier)
        unary_relation = Group(Optional(binary_temporal_prefix) + unary_logical_op + expr)

        # Expression with all options
        expr <<= infixNotation(binary_relation | unary_relation | binary_variable | parens,
                               [(unary_temporal_prefix, 1, opAssoc.RIGHT),
                                (unary_logical_op, 1, opAssoc.RIGHT),
                                (binary_temporal_prefix, 2, opAssoc.LEFT),
                                (binary_logical_op, 2, opAssoc.LEFT)
                                ])

        return expr

    # Example parser usage
    def parseSTL(self, expression):
        stl_parser = self._create_stl_parser()
        parsed_expression = stl_parser.parseString(expression, parseAll=True)
        return parsed_expression.asList()

    def visit(self, node):
        # Determine the type of the node and call the appropriate visit method
        if isinstance(node, list):
            if len(node) == 1:
                # Single element (either a terminal or a unary expression)
                if isinstance(node[0], str) and len(node[0]) == 1:
                    print(node[0])
                    return self.visit_binary_variable(node[0])
                return self.visit(node[0])
            elif len(node) == 3 and isinstance(node[0], str) and isinstance(node[1], str) and isinstance(node[2], str):
                if node[1] in {'<', '<=', '>', '>=', '==', '!='}:
                    return self.visit_binary_relational(node[1], node[0], node[2])
            elif not isinstance(node[0], list):
                if node[0] in {'!'}:
                    return self.visit_unary_logical(node[0], node[1])
                elif node[0] in {'('} and node[len(node)-1] in {')'}:
                    return self.visit_parenthesis(node[0], node[len(node)-1], node[1])
                elif node[0] in {'G', 'F'}:  # Temporal operators with a single argument
                    if (int(node[2]) > int(node[4])):
                        raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                    return self.visit_unary_temporal_operator(node[0], node[2], node[4], node[6])
            elif isinstance(node[1], str):
                #print(node[0])
                if node[1] in {'U'}:  # Temporal operators with two arguments
                    if (int(node[3]) > int(node[5])):
                        raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                    return self.visit_binary_temporal_operator(node[1], node[3], node[5], node[0], node[7])
                elif node[1] in {'&&', '||', '->', '<->'}:  # Binary logical operators
                    return self.visit_binary_logical(node[1], node[0], node[2:])
        elif isinstance(node, str):
            return self.visit_identifier(node)

    def visit_parenthesis(self, openPar, closePar, expr):
        # Visit the expression within the temporal operator
        #print(f"Visiting parenthesis: {openPar}{closePar}")
        return self.visit(expr)

    def visit_unary_temporal_operator(self, operator, time_interval_low, time_interval_high, expr):
        # Visit the expression within the temporal operator
        #print(f"Visiting Unary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        ret = self.visit(expr)
        prop = self._addSubFormula([operator, time_interval_low, time_interval_high, ret[0]])
        return prop, str(int(time_interval_high) + int(ret[1]))

    def visit_binary_temporal_operator(self, operator, time_interval_low, time_interval_high, left, right):
        # Visit the expression within the temporal operator
        #print(f"Visiting Binary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        ret_left  = self.visit(left)
        ret_right = self.visit(right)

        prop = self._addSubFormula([operator, time_interval_low, time_interval_high, ret_left[0], ret_right[0]])
        return prop, str(int(time_interval_high) + max(int(ret_left[1]),int(ret_right[1])))

    def visit_unary_logical(self, operator, expr):
        # Visit both sides of the logical expression
        #print(f"Visiting Unary Logical Operator: {operator}")
        ret = self.visit(expr)
        return self._addSubFormula([operator, ret[0]]), ret[1]

    def visit_binary_logical(self, operator, left, right):
        # Visit both sides of the logical expression
        # print(f"Visiting Logical Operator: {operator}, {left}, {right}")
        ret_left = self.visit(left)
        ret_right = self.visit(right)

        if operator in {'&&', '||'}:
            prop = self._addSubFormula([operator, ret_left[0], ret_right[0]])
        elif operator in {'->'}:
            prop = self._addSubFormula(['!', ret_left[0]])
            prop1 = self._addSubFormula(['||', prop, ret_right[0]])
        elif operator in {'<->'}:
            formula1 = self._addSubFormula(['&&', ret_left[0], ret_right[0]])
            formula2 = self._addSubFormula(['&&', self._addSubFormula(['!', ret_left[0]]), self._addSubFormula(['!', ret_right[0]])])
            prop     = self._addSubFormula(['||', formula1, formula2])
        return prop, str(max(int(ret_left[1]), int(ret_right[1])))

    def visit_binary_relational(self, operator, left, right):
        # Visit both sides of the relational expression
        #print(f"Visiting Relational Operator: {operator}")
        prop = ""

        if left in self._variables:
            #print(f"Key '{left}' is in the dictionary.")

            if (self._variables[left] == 'binary'):
                raise SyntaxError(f"Variable '{left}' cannot be real and binary")

            #print(self._real_constraints[left].keys())
            if operator in self._real_constraints[left].keys():
                #print(f"'{operator}' is in {self._real_constraints[left].keys()}")
                if right in self._real_constraints[left][operator].keys():
                    prop = self._real_constraints[left][operator][right]
                     #print(prop)
                else:
                    prop = self._addSubFormula([left, operator, right])
                    self._real_constraints[left][operator] = {right: prop}
            else:
                #print(f"'{operator}' is not in {self._real_constraints[left].keys()}")
                prop = self._addSubFormula([left, operator, right])
                self._real_constraints[left][operator]={right:prop}
        else:
            #print(f"Key '{left}' is not in the dictionary.")
            self._variables[left] = 'real'
            #print(f"Key '{left}' added in the dictionary.")
            prop = self._addSubFormula([self.visit(left), operator, self.visit(right)])
            self._real_constraints[left] = {operator:{right:prop}}
        return prop, '1'



    def visit_binary_variable(self, binary_var):
        # Simply return the identifier, in more complex cases you might want to look up values
        #print(f"Visiting Binary Variable: {binary_var}")
        prop = ""
        if binary_var in self._variables:
            #print(f"Key '{binary_var}' is in the dictionary.")
            if (self._variables[binary_var] == 'real'):
                raise SyntaxError(f"Variable '{binary_var}' cannot be real and binary")
            prop = self._binary_constraints[binary_var]
        else:
            #print(f"Key '{binary_var}' is not in the dictionary.")
            self._variables[binary_var] = 'binary'
            #print(f"Key '{binary_var}' added in the dictionary.")
            prop = self._addSubFormula(binary_var)
            self._binary_constraints[binary_var] = prop

        return prop, '1'

    def visit_identifier(self, identifier):
        # Simply return the identifier, in more complex cases you might want to look up values
        # print(f"Visiting Identifier: {identifier}")
        return identifier

    def _encode_variables (self,time_horizon,smt_variables,verbose):
        if verbose:
            print("")
            print("# Encode the Real/Binary variables ")
            print("")
        for key in self._variables:
            for t in range(time_horizon):
                prop = f"{key}_t{t}"
                if variables[key] == 'real':
                    if verbose:
                        print(f"{prop} = Real('{prop}')")
                    smt_variables[prop] = Real(prop)
                elif variables[key] == 'binary':
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    smt_variables[prop] = Bool(prop)
            print("")

    def _filter_witness(self, model):
        filter_model1 = []
        filter_model2 = {}
        sorted_model =  {}
        for var in model:
            var_name = str(var)
            if len(var_name) >= 4:
                if var_name[0:4] != "_phi":
                    filter_model1.append(var_name)
                    filter_model2[var_name] = model[var]

        filter_model1.sort()
        for var in filter_model1:
            sorted_model[var] = filter_model2[var]

        return sorted_model

    def solve(self, time_horizon, root_formula, verbose):
        #This hashtable will contains the variables for the SMT Solver
        smt_variables = {}

        if verbose:
            print("# SMT Encoding in Python")
            print("")
            print("#===========================")
            print("from z3 import *")
            print("")

        self._encode_variables(time_horizon,smt_variables,verbose)

        if verbose:
            print("")
            print("# Instantiate the SMT Solver")
            print("s = Solver()")

        s = Solver()
        root_prop = f"{root_formula}_t{0}"

        for key in self._sub_formulas:
            # If the sub-formula to consider is the root formula then
            # we compute only the for time tO
            # we introduce another variable
            time_limit = 1
            if key != root_formula:
                time_limit = time_horizon
            for t in range(time_limit):
                prop = f"{key}_t{t}"
                #print(f"{prop}")
                if len(self._sub_formulas[key]) == 1:
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    smt_variables[prop] = Bool(prop)
                    if (root_prop != prop):
                        if verbose:
                            print(f"s.add({prop} == {self._sub_formulas[key][0]}_t{t})")
                        s.add(smt_variables[prop] == smt_variables[f"{self._sub_formulas[key][0]}_t{t}"])
                    else:
                        if verbose:
                            print(f"s.add({self._sub_formulas[key][0]}_t{t})")
                        s.add(smt_variables[f"{self._sub_formulas[key][0]}_t{t}"])
                elif len(self._sub_formulas[key]) == 3 and self._sub_formulas[key][1] in {'<', '<=', '>', '>=', '==', '!='}:
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    smt_variables[prop] = Bool(prop)
                    if self._sub_formulas[key][1] == '<':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] < float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{t} < {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] < float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add({self._sub_formulas[key][0]}_t{t} < {self._sub_formulas[key][2]})")
                    elif self._sub_formulas[key][1] == '<=':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] <= float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{t} <= {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] <= float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add({self._sub_formulas[key][0]}_t{t} <= {self._sub_formulas[key][2]})")
                    elif self._sub_formulas[key][1] == '>':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] > float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{t} > {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] > float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add(({self._sub_formulas[key][0]}_t{t} > {self._sub_formulas[key][2]}))")
                    elif self._sub_formulas[key][1] == '>=':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] >= float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{t} >= {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] >= float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add(({self._sub_formulas[key][0]}_t{t} >= {self._sub_formulas[key][2]}))")
                    elif self._sub_formulas[key][1] == '==':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] == float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{t} == {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] == float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add(({self._sub_formulas[key][0]}_t{t} == {self._sub_formulas[key][2]}))")
                    elif self._sub_formulas[key][1] == '!=':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] != float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{t} != {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[f"{self._sub_formulas[key][0]}_t{t}"] != float(self._sub_formulas[key][2])))
                            if verbose:
                                print(f"s.add(({self._sub_formulas[key][0]}_t{t} != {self._sub_formulas[key][2]}))")
                elif len(self._sub_formulas[key]) == 4 and self._sub_formulas[key][0] in {'G','F'}: #Ezio in the case of nested operation it is necessary to do all the t

                    int_a = int(self._sub_formulas[key][1])
                    int_b = int(self._sub_formulas[key][2])
                    if t + int_b < time_horizon:

                        prop1 = self._sub_formulas[key][3]
                        flag = 1
                        for i in range(int_a, int_b + 1):
                            if not f"{prop1}_t{t + i}" in smt_variables:
                                flag = 0
                                break
                        if flag:
                            if verbose:
                                print(f"{prop} = Bool('{prop}')")
                            smt_variables[prop] = Bool(prop)

                            prop1_list = [smt_variables[f"{prop1}_t{t + i}"] for i in range(int_a, int_b + 1)]
                            if self._sub_formulas[key][0] == 'G':
                                if (root_prop != prop):
                                    s.add(smt_variables[prop] == And(prop1_list))
                                    if verbose:
                                        print(f"s.add({prop} == And({prop1_list}))")
                                else:
                                    s.add(And(prop1_list))
                                    if verbose:
                                        print(f"s.add(And({prop1_list}))")
                            elif self._sub_formulas[key][0] == 'F':
                                if (root_prop != prop):
                                    s.add(smt_variables[prop] == Or(prop1_list))
                                    if verbose:
                                        print(f"s.add({prop} == Or({prop1_list}))")
                                else:
                                    s.add(Or(prop1_list))
                                    if verbose:
                                        print(f"s.add(Or({prop1_list}))")

                elif len(self._sub_formulas[key]) == 3 and self._sub_formulas[key][0] in {'&&', '||'}:
                    prop1 = f"{self._sub_formulas[key][1]}_t{t}"
                    prop2 = f"{self._sub_formulas[key][2]}_t{t}"
                    if prop1 in smt_variables.keys() and prop2 in smt_variables.keys():
                        if verbose:
                            print(f"{prop} = Bool('{prop}')")
                        smt_variables[prop] = Bool(prop)
                        if self._sub_formulas[key][0] == '&&':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == And(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add({prop} == And({prop1},{prop2}))")
                            else:
                                s.add(And(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add(And({prop1},{prop2}))")
                        elif self._sub_formulas[key][0] == '||':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == Or(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add({prop} == Or({prop1},{prop2}))")
                            else:
                                s.add(Or(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add(Or({prop1},{prop2}))")
                elif len(self._sub_formulas[key]) == 2 and self._sub_formulas[key][0] in {'!'}:
                    prop1 = f"{self._sub_formulas[key][1]}_t{t}"
                    if prop1 in smt_variables.keys():
                        if verbose:
                            print(f"{prop} = Bool('{prop}')")
                        smt_variables[prop] = Bool(prop)
                        if self._sub_formulas[key][0] == '!':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == Not(smt_variables[prop1]))
                                if verbose:
                                    print(f"s.add({prop} == Not({prop1}))")
                            else:
                                s.add(Not(smt_variables[prop1]))
                                if verbose:
                                    print(f"s.add(Not({prop1}))")
                elif len(self._sub_formulas[key]) == 5 and self._sub_formulas[key][0] in {'U'}:
                    int_a = int(self._sub_formulas[key][1])
                    int_b = int(self._sub_formulas[key][2])
                    # phi1 U_[a,b] phi2 = G [0,a] phi1 && F [a,b] phi2 && F [a,a] (phi1 U phi2)
                    # A   = G [0,a] phi1
                    # B   = F [a,b] phi2
                    # C   = phi1 U phi2
                    # C_t = phi2_t or (phi1_t and C_t+1) with C_N = phi2_N
                    # C_a = F [a,a] (phi1 U phi2)
                    # Example
                    # a = 2 and N = 7
                    # C_t7 = phi2_t7
                    # C_t6 = phi2_t6 or (phi1_t6 and C_t7)
                    # C_t5 = phi2_t5 or (phi1_t5 and C_t6)

                    prop1 = self._sub_formulas[key][3]
                    prop2 = self._sub_formulas[key][4]

                    if t + int_b < time_horizon:
                        if verbose:
                            print(f"{prop}_A = Bool('{prop}_A')")
                        smt_variables[f"{prop}_A"] = Bool(f"{prop}_A")
                        prop_a_list = [smt_variables[f"{prop1}_t{t + i}"] for i in range(0, int_a + 1)]
                        s.add(smt_variables[f"{prop}_A"] == And(prop_a_list))
                        if verbose:
                            print(f"s.add({prop}_A == And({prop_a_list}))")
                            print(f"{prop}_B = Bool('{prop}_B')")
                        smt_variables[f"{prop}_B"] = Bool(f"{prop}_B")
                        prop_b_list = [smt_variables[f"{prop2}_t{t + i}"] for i in range(int_a, int_b + 1)]
                        if verbose:
                            print(f"s.add({prop2}_B == Or({prop_b_list}))")

                        if not f"{key}_t{t + int_a}_C" in smt_variables.keys():
                            if verbose:
                                print(f"The variables {key}_t{t + int_a}_C is not in smt_variables")

                            if not f"{key}_t{time_horizon - 1}_C" in smt_variables.keys():
                                if verbose:
                                    print(f"{key}_t{time_horizon - 1}_C = Bool('{key}_t{time_horizon - 1}_C')")
                                smt_variables[f"{key}_t{time_horizon - 1}_C"] = Bool(f"{key}_t{time_horizon - 1}_C")
                                s.add(smt_variables[f"{key}_t{time_horizon - 1}_C"] == smt_variables[
                                    f"{prop2}_t{time_horizon - 1}"])
                                if verbose:
                                    print(f"s.add({key}_t{time_horizon - 1}_C == {prop2}_t{time_horizon - 1})")
                            for i in range(t + int_a, time_horizon - 1):
                                k = time_horizon - i
                                if not f"{key}_t{k}_C" in smt_variables.keys():
                                    if verbose:
                                        print(f"{key}_t{k}_C = Bool('{key}_t{k}_C')")
                                    smt_variables[f"{key}_t{k}_C"] = Bool(f"{key}_t{k}_C")
                                    if verbose:
                                        print(f"s.add({key}_t{k}_C == Or({prop2}_t{k},And({prop1}_t{k},{key}_t{k + 1}_C))")
                                    s.add(smt_variables[f"{key}_t{k}_C"] == Or(smt_variables[f"{prop2}_t{k}"],
                                                                               And(smt_variables[f"{prop1}_t{k}"],
                                                                                   smt_variables[f"{key}_t{k + 1}_C"])))
                        if verbose:
                            print("")
                        smt_variables[f"{prop}"] = Bool(f"{prop}")
                        if verbose:
                            print(f"{prop} = Bool('{prop}')")

                        if (root_prop != prop):
                            s.add(
                                smt_variables[f"{prop}"] == And(smt_variables[f"{prop}_A"], smt_variables[f"{prop}_B"],
                                                                smt_variables[f"{key}_t{int_a}_C"]))
                            if verbose:
                                print(f"s.add({prop} == And({prop}_A,{prop}_B,{key}_t{int_a}_C))")
                        else:
                            s.add(And(smt_variables[f"{prop}_A"], smt_variables[f"{prop}_B"],
                                      smt_variables[f"{key}_t{int_a}_C"]))
                            if verbose:
                                print(f"s.add(And({prop}_A,{prop}_B,{key}_t{int_a}_C))")
        if verbose:
            print("")
            print("================================")
            print(f"Num of variables in SMT solver = {len(smt_variables.keys())}")
            print("")
            print("Solver statistics")
            print(s.statistics())

        if s.check() == unsat:
            print("")
            print("The STL requirements are inconsistent.")
        else:
            print("")
            print("The STL requirements are consistent. This is a signal witness:")
            print(self._filter_witness(s.model()))

#End class STLConsistencyChecker









# Example STL expression
#stl_expression = " F [10,10000] (! (a > 0) &&  b > 0)" #controlla not davanti ad a -> ora è ok
#stl_expression = " F [0,5] (a > 0 && a < 0)"
# Example STL expression
#stl_expression = "! F [0,5] G [2,5] a > 0"
#stl_expression = "!(a > 0)"
#stl_expression = "(! x<0 && y>0) U[1,5] ( y > 6.07)"
#stl_expression = "G[0,5] ((x > 3) && (F[2,7] (y < 2)))"
#stl_expression = "G[0,5] ((x > 3) && (y < 2))"
#stl_expression = " (x > 4) && ! (y > 3)"
#stl_expression = "G[0,5] ((F[2,7] (y < 2)))"
#stl_expression = "G[0,5] (x > 5)"
#stl_expression = "G[0,5] (F[7,9] (x > 3))"
#stl_expression = "G[0,10](x U[2,5] y)" #Until è sistemato
#stl_expression = "x>0 U[2,7] y < 0"
#stl_expression = "G[2,5] x > 5 || G[1,3] x < 0"  #Giustamente dice che è sat, ma poi la witness che produce non ha senso
#stl_expression = "G[2,5] (x > 5 || x < 0)"
#stl_expression = "! a && a"
#stl_expression =  "!a && !b && ((a && b) <-> (a || b)) "
#stl_expression = "a && !b && (a <-> b)"
#stl_expression = "F [2,3] a < 0 && G [0,5] a > 0"
stl_expression = "(a && (a -> (a || b)))"

# Create a checker and visit the parsed expression
checker = STLConsistencyChecker()
parsed_expr = checker.parseSTL(stl_expression)
print("Input STL expression: ", stl_expression)
print("Parsed STL Expression:", parsed_expr)
result = checker.visit(parsed_expr)

print(f"Formula_horizon =  {result[1]}")
print(f"Root sub_formula = {result[0]} ")
checker.printSubFormulas()
formula_horizon = int(result[1])
variables = checker.getVariableList()
propositions = checker.getBasicPropositionsList()
expression = list(propositions.values())

checker.solve(int(result[1]), result[0], True)



