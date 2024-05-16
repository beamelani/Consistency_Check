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


# STL Requirements Consistency Checking (ver 0.43)
# Date: 06-05-2024
#
#

from z3 import *
from pyparsing import (Optional, Combine, Literal, Word, alphas, nums, alphanums, Group, Forward, infixNotation,
                       opAssoc, oneOf)


class SyntaxError(Exception):
    """Base class for other exceptions"""
    pass


class STLConsistencyChecker:

    def __init__(self):
        self._variables = {}  # Protected variable
        self._real_constraints = {}  # Protected variable
        self._binary_constraints = {}  # Protected variable
        self._sub_formulas = {}  # Protected variable
        self._prop_count = 0  # Protected variable

    def _checkFormulaType(self, sub_formula):
        if len(sub_formula) == 1:
            return "Literal"
        elif len(sub_formula) == 2:
            if sub_formula[0] in {'!'}:
                return "Not"
            elif sub_formula[0] in {'True'}:
                return "True"
            elif sub_formula[0] in {'False'}:
                return "False"
        elif len(sub_formula) == 3:
            if sub_formula[1] in {'<', '<=', '>', '>=', '==', '!='}:
                return "RConstraint"
            elif sub_formula[0] == "&&":
                return "And"
            elif sub_formula[0] == "||":
                return "Or"
            elif sub_formula[0] == "->":
                return "Implies"
            elif sub_formula[0] == "<->":
                return "Equivalence"
        elif len(sub_formula) == 4:
            if sub_formula[0] == "G":
                return "Always"
            elif sub_formula[0] == "F":
                return "Eventually"
        elif len(sub_formula) == 5:
            if sub_formula[0] == "U":
                return "Until"
        return "Not defined"

    def _invertRConstraint(self, sub_formula):
        if self._checkSubformulaType(sub_formula) == "RConstraint":
            if sub_formula[1] == "<":
                sub_formula[1] = ">="
            elif sub_formula[1] == ">":
                sub_formula[1] = "<="
            elif sub_formula[1] == ">=":
                sub_formula[1] = "<"
            elif sub_formula[1] == "<=":
                sub_formula[1] = ">"
            elif sub_formula[1] == "==":
                sub_formula[1] = "!="
            elif sub_formula[1] == "!=":
                sub_formula[1] = "=="
        return sub_formula

    # Ezio: These are some rules to simplify the formulas and to push the negation always on top
    #
    # Not case
    #
    # Not Not phi == phi
    # Not True    == False
    # Not False   == True
    #
    # And case
    #
    # phi and phi   == phi
    # phi and True  == phi
    # phi and False == False
    #
    # (G [a1,b2] phi) and (G [a2,b2] phi) == G[min(a1,a2),max(b1,b2)] phi  (if [a1,b1] intersect [a2,b2])
    #
    # (Not phi1 and Not phi2) == Not (phi1 or phi2)
    # (Not phi1 and phi2) == Not (phi1 or Not phi2) == Not (phi2 implies phi1)
    # (phi1 and Not phi2) == Not (Not phi1 or phi2) == Not (phi1 implies phi2)
    #
    # Or case
    #
    # phi   or phi   == phi
    # phi   or True  == True
    # True  or phi   == True
    # False or phi  == phi
    # phi   or False == phi
    #
    # (F [a1,b2] phi) and (F [a2,b2] phi) == F[min(a1,a2),max(b1,b2)] phi  (if [a1,b1] intersect [a2,b2])
    #
    # (Not phi1 or Not phi2) == Not (phi1 and phi2)
    # (Not phi1 or phi2)     == (phi1 implies phi2)
    # (phi1 or Not phi2)     == (phi2 implies phi1)
    #
    # Implies case
    #
    # True implies phi    == phi
    # phi  implies True   == True
    # False implies phi   == True
    # phi   implies False == Not phi
    #
    # (Not phi1 implies Not phi2) == (Not Not phi1 or Not phi2) == (phi2 implies phi1)
    # (Not phi1 implies phi2)     == (phi1 or phi2)
    # (phi1 implies Not phi2)     == (Not phi1 or Not phi2) == Not (phi1 and phi2)
    #
    # (phi1 -> (phi1 -> phi2))    == (phi1 -> phi2)
    # (phi1 -> phi1)              == True (Tautology)
    # (phi1 -> (phi2 -> phi1))    == True (Tautology)
    #
    #
    # Equivalence case
    #
    # (True <-> phi)  == (True -> phi) and (phi -> True)    == phi and True == phi
    # (False <-> phi) == (False -> phi) and (phi -> False) == True and Not phi == Not phi
    #
    # (Not phi1 <-> Not phi2)     ==  (phi1 <-> phi2)
    # (Not phi1 <-> phi2)         ==  (phi1 <-> Not phi2) == Not (phi1 <-> phi2)
    #
    # Globally case
    #
    # G [a,b] True  == True
    # G [a,b] False == False
    #
    # G [a,b] Not phi             == Not F [a,b] phi
    # F [a,b] Not phi             == Not G [a,b] phi
    #
    # Until case
    #
    # phi1  U_[a,b] True  = True
    # phi1  U_[a,b] False = False
    # True  U_[a,b] phi2  = F [a,b] phi2
    # False U_[a,b] phi2  = False
    #
    # phi1 U_[a,b] phi2 = G [0,a] phi1 && F [a,b] phi2 && F [a,a] (phi1 U phi2)
    #
    # Not phi1 Until Not phi2    == Not (phi1 Release phi2)
    #
    # C_t7 = phi2_t7
    # C_t6 = phi2_t6 or (phi1_t6 and C_t7)
    # a or (!b and c) = ((b_7->a_6)->b_6)
    # a or (a and !b) = a or !(a ->b) = (6(a -> b) -> a)
    # C(n-1) = Not phi2 (n-1) or (phi1 (n-1) and C (n))
    # C(n-1) = (phi2 (n-1) -> (phi1 (n-1) and C (n)))
    # C(n-2) = (phi2 (n-2) -> (phi1 (n-2) and ((phi2 (n-1) -> (phi1 (n-1) and C (n)))))))
    #
    # C_t7 = phi2_t7
    # C_t6 = phi2_t6 or (False and phi2_t7) = phi2_t6
    # C_t5 = phi2_t5 or (False and phi2_t6) = phi2_t5
    #
    # False U_[a,b] phi2 = G [0,a] False && F [a,b] phi2 && F [a,a] (phi1 U phi2)
    #
    #
    # G[a,b] phi1 && G [c,d] phi1 = G[min(a,c),max(b,d)] phi1 if [a,b] intersect [c,d]
    #
    #
    #
    #

    def _findKeyOpTree(self, key, key_root, type):
        if self._cmpForTypeByKey(key_root, type):
            if self._sub_formulas[key_root][1] == key or self._sub_formulas[key_root][2] == key:
                return True
            else:
                return self._findKeyOpTree(key, self._sub_formulas[key_root][1], type) or self._findKeyOpTree(key,
                                                                                                              self._sub_formulas[
                                                                                                                  key_root][
                                                                                                                  2],
                                                                                                              type)
        return False

    def _findKeyImpliesTree(self, key, key_root):
        if self._cmpForTypeByKey(key_root, "Implies"):
            if self._sub_formulas[key_root][1] == key:
                return True
            else:
                return self._findKeyImpliesTree(key, self._sub_formulas[key_root][1]) or self._findKeyImpliesTree(key,
                                                                                                                  self._sub_formulas[
                                                                                                                      key_root][
                                                                                                                      2])
        return False

    def _findFormulaKey(self, sub_formula):
        for key in self._sub_formulas.keys():
            if self._sub_formulas[key] == sub_formula:
                return key
        return None

    def _insSubFormula(self, subformula):
        print(f"Insert {subformula}")
        key = f"_phi{self._prop_count}"
        self._sub_formulas[key] = subformula
        self._prop_count = self._prop_count + 1
        self.printSubFormulas()
        return key

    def _cmpForTypeByKey(self, key, type):
        if self._checkFormulaType(self._sub_formulas[key]) == type:
            return True
        return False

    def _addSubFormula(self, sub_formula):
        # First search if the sub_formula is already present
        # in the list of subformulas
        print(f"Add {sub_formula}")
        key = self._findFormulaKey(sub_formula)
        if key is not None:
            return key

        simplify_flag = False

        if simplify_flag:
            match self._checkFormulaType(sub_formula):
                case "Not":
                    key = sub_formula[1]
                    if self._cmpForTypeByKey(key, "Not"):
                        sub_sub_formula = self._sub_formulas[key]
                        return sub_sub_formula[1]
                    elif self._cmpForTypeByKey(key, "True"):
                        return self._addSubFormula(['False', '*'])
                    elif self._cmpForTypeByKey(key, "False"):
                        return self._addSubFormula(['True', '*'])
                    # sub_sub_formula = self._sub_formulas[key]
                    # if self._checkFormulaType(sub_sub_formula) == "Not":
                    #    key = sub_sub_formula[1]
                    #    return key
                case "And":
                    key1 = sub_formula[1]
                    key2 = sub_formula[2]
                    # a && a == a
                    if key1 == key2:
                        return key1

                    if self._findKeyOpTree(key1, key2, "And"):
                        return key2

                    if self._findKeyOpTree(key2, key1, "And"):
                        return key1

                    if self._cmpForTypeByKey(key1, "True"):
                        return key2
                    elif self._cmpForTypeByKey(key2, "True"):
                        return key1

                    if self._cmpForTypeByKey(key1, "False"):
                        return key1
                    elif self._cmpForTypeByKey(key2, "False"):
                        return key2

                    # (Not phi1 and Not phi2) == Not (phi1 or phi2)
                    if self._cmpForTypeByKey(key1, "Not") and \
                            self._cmpForTypeByKey(key2, "Not"):
                        phi1_key = self._sub_formulas[key1][1]
                        phi2_key = self._sub_formulas[key2][1]
                        return self._addSubFormula(['||', phi1_key, phi2_key])
                    elif self._cmpForTypeByKey(key1, "Not") and \
                            not self._cmpForTypeByKey(key2, "Not"):
                        # (Not phi1 and phi2) == Not (phi1 or Not phi2) == Not (phi2 implies phi1)

                        phi1_key = self._sub_formulas[key1][1]
                        key = self._addSubFormula(['->', key2, phi1_key])
                        return self._addSubFormula(['!', key])
                    elif not self._cmpForTypeByKey(key1, "Not") and \
                            self._cmpForTypeByKey(key2, "Not"):
                        # (phi1 and Not phi2) == Not (Not phi1 or phi2) == Not (phi1 implies phi2)
                        phi2_key = self._sub_formulas[key2][1]
                        key = self._addSubFormula(['->', key1, phi2_key])
                        return self._addSubFormula(['!', key])
                case "Or":
                    key1 = sub_formula[1]
                    key2 = sub_formula[2]
                    # a || a == a
                    if key1 == key2:
                        return key1

                    if self._findKeyOpTree(key1, key2, "Or"):
                        return key2

                    if self._findKeyOpTree(key2, key1, "Or"):
                        return key1

                    if self._cmpForTypeByKey(key1, "True"):
                        return key1
                    elif self._cmpForTypeByKey(key2, "True"):
                        return key2

                    if self._cmpForTypeByKey(key1, "False"):
                        return key2
                    elif self._cmpForTypeByKey(key2, "False"):
                        return key1

                    # (Not phi1 or Not phi2) == Not (phi1 and phi2)
                    if self._cmpForTypeByKey(key1, "Not") and self._cmpForTypeByKey(key2, "Not"):
                        phi1_key = self._sub_formulas[key1][1]
                        phi2_key = self._sub_formulas[key2][1]
                        return self._addSubFormula(['&&', phi1_key, phi2_key])
                    elif self._cmpForTypeByKey(key1, "Not") and not self._cmpForTypeByKey(key2, "Not"):
                        # (Not phi1 or phi2)     == (phi1 implies phi2)
                        phi1_key = self._sub_formulas[key1][1]
                        return self._addSubFormula(['->', phi1_key, key2])
                    elif not self._cmpForTypeByKey(key1, "Not") and self._cmpForTypeByKey(key2, "Not"):
                        # (phi1 or Not phi2)     == (phi2 implies phi1)
                        phi2_key = self._sub_formulas[key2][1]
                        return self._addSubFormula(['->', phi2_key, key1])
                case "Implies":
                    key1 = sub_formula[1]
                    key2 = sub_formula[2]
                    if key1 == key2:
                        return self._addSubFormula(['True', '*'])

                    if self._findKeyImpliesTree(key1, key2):
                        return key2

                    # (Not phi1 implies Not phi2) == (Not Not phi1 or Not phi2) == (phi2 implies phi1)
                    if self._cmpForTypeByKey(key1, "Not") and self._cmpForTypeByKey(key2, "Not"):
                        phi1_key = self._sub_formulas[key1][1]
                        phi2_key = self._sub_formulas[key2][1]
                        return self._addSubFormula(['->', phi2_key, phi1_key])
                    elif self._cmpForTypeByKey(key1, "Not") and not self._cmpForTypeByKey(key2, "Not"):
                        # (Not phi1 implies phi2)     == (phi1 or phi2)
                        phi1_key = self._sub_formulas[key1][1]
                        return self._addSubFormula(['||', phi1_key, key2])
                    elif not self._cmpForTypeByKey(key1, "Not") and self._cmpForTypeByKey(key2, "Not"):
                        # (phi1 implies Not phi2)     == (Not phi1 or Not phi2) == Not (phi1 and phi2)
                        phi2_key = self._sub_formulas[key2][1]
                        key = self._addSubFormula(['&&', key1, phi2_key])
                        return self._addSubFormula(['!', key])
                case "Equivalence":
                    key1 = sub_formula[1]
                    key2 = sub_formula[2]
                    if key1 == key2:
                        return self._addSubFormula(['True', '*'])
                    if self._cmpForTypeByKey(key1, "Not") and self._cmpForTypeByKey(key2, "Not"):
                        # (Not phi1 <-> Not phi2)     ==  (phi1 <-> phi2)
                        phi1_key = self._sub_formulas[key1][1]
                        phi2_key = self._sub_formulas[key2][1]
                        return self._addSubFormula(['<->', phi1_key, phi2_key])
                    elif self._cmpForTypeByKey(key1, "Not") and not self._cmpForTypeByKey(key2, "Not"):
                        # (Not phi1 <-> phi2)         ==  (phi1 <-> Not phi2) == Not (phi1 <-> phi2)
                        phi1_key = self._sub_formulas[key1][1]
                        return self._addSubFormula(['<->', phi1_key, key2])
                    elif not self._cmpForTypeByKey(key1, "Not") and self._cmpForTypeByKey(key2, "Not"):
                        # (Not phi1 <-> phi2)         ==  (phi1 <-> Not phi2) == Not (phi1 <-> phi2)
                        phi2_key = self._sub_formulas[key2][1]
                        key = self._addSubFormula(['<->', key1, phi2_key])
                case "Always":
                    key = sub_formula[3]
                    a = int(sub_formula[1])
                    b = int(sub_formula[2])
                    sub_sub_formula = self._sub_formulas[key]
                    if self._checkFormulaType(sub_sub_formula) == "Not":
                        key1 = sub_sub_formula[1]
                        key = self._addSubFormula(['F', sub_formula[1], sub_formula[2], key1])
                        return self._addSubFormula(['!', key])
                case "Eventually":
                    key = sub_formula[3]
                    sub_sub_formula = self._sub_formulas[key]
                    if self._checkFormulaType(sub_sub_formula) == "Not":
                        key1 = sub_sub_formula[1]
                        key = self._addSubFormula(['G', sub_formula[1], sub_formula[2], key1])
                        return self._addSubFormula(['!', key])

        # If the subformula is not found then add it

        return self._insSubFormula(sub_formula)

    def _encode_time(self, t, time_horizon):
        # Convert the number in a string
        t_str = str(t)
        # Add 0 to complete the string
        return t_str.zfill(len(str(time_horizon)))

    def getVariableList(self):
        return self._variables

    def getRealConstraintsList(self):
        return self._real_constraints

    def getBinaryConstraintsList(self):
        return self._binary_constraints

    def getBasicPropositionsList(self):
        return self._sub_formulas

    def getNumProp(self):
        return self._prop_count

    def _reachSubFormula(self, root, key):
        if self._cmpForTypeByKey(root, "Literal"):
            return False
        elif self._cmpForTypeByKey(root, "True"):
            return False
        elif self._cmpForTypeByKey(root, "False"):
            return False
        elif self._cmpForTypeByKey(root, "RConstraint"):
            return False
        elif self._cmpForTypeByKey(root, "Not"):
            if self._sub_formulas[root][1] == key:
                return True
            else:
                return self._reachSubFormula(self._sub_formulas[root][1], key)
        elif self._cmpForTypeByKey(root, "And") or self._cmpForTypeByKey(root, "Or") or self._cmpForTypeByKey(root,
                                                                                                              "Implies") or self._cmpForTypeByKey(
                root, "Equivalence"):
            if self._sub_formulas[root][1] == key or self._sub_formulas[root][2] == key:
                return True
            else:
                return self._reachSubFormula(self._sub_formulas[root][1], key) or self._reachSubFormula(
                    self._sub_formulas[root][2], key)
        elif self._cmpForTypeByKey(root, "Always") or self._cmpForTypeByKey(root, "Eventually"):
            if self._sub_formulas[root][3] == key:
                return True
            else:
                return self._reachSubFormula(self._sub_formulas[root][1], key)
        elif self._cmpForTypeByKey(root, "Until"):
            if self._sub_formulas[root][3] == key or self._sub_formulas[root][4] == key:
                return True
            else:
                return self._reachSubFormula(self._sub_formulas[root][3], key) or self._reachSubFormula(
                    self._sub_formulas[root][4], key)

    def cleanUnreachableSubFormulas(self, key_root):
        temp = self._sub_formulas.keys()
        for key in temp:
            if key != key_root and not self._reachSubFormula(key_root, key):  # credo che questo crei problemi
                self._sub_formulas[key] = []

    def printSubFormulas(self):
        # Print the list of the subformulas
        print("")
        print("List of subformulas")
        print("===================")
        print("")
        for key in self._sub_formulas.keys():
            # Key is the name of the formula
            # Now we check the type of the formula
            if self._checkFormulaType(self._sub_formulas[key]) == "Literal":
                # The subformula is a binary variable
                print(f"{key} = {self._sub_formulas[key][0]} (Binary variable)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "True":
                print(f"{key} = {self._sub_formulas[key][0]} (Tautology)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "False":
                print(f"{key} = {self._sub_formulas[key][0]} (Contradiction)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "RConstraint":
                # The subformula is a predicate over the real variable
                print(
                    f"{key} = {self._sub_formulas[key][0]} {self._sub_formulas[key][1]} {self._sub_formulas[key][2]} (Real constraint)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "Always":
                # The subformula is always
                print(
                    f"{key} = {self._sub_formulas[key][0]} [{self._sub_formulas[key][1]}, {self._sub_formulas[key][2]}] {self._sub_formulas[key][3]} (Always)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "Eventually":
                # The subformula is eventually
                print(
                    f"{key} = {self._sub_formulas[key][0]} [{self._sub_formulas[key][1]}, {self._sub_formulas[key][2]}] {self._sub_formulas[key][3]} (Eventually)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "Until":
                # The subformula is until
                print(
                    f"{key} = {self._sub_formulas[key][3]} {self._sub_formulas[key][0]} [{self._sub_formulas[key][1]}, {self._sub_formulas[key][2]}] {self._sub_formulas[key][4]} (Until)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "And":
                # The subformula is an &&
                print(
                    f"{key} = {self._sub_formulas[key][1]} {self._sub_formulas[key][0]}  {self._sub_formulas[key][2]}   (And)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "Or":
                # The subformula is an Or
                print(
                    f"{key} = {self._sub_formulas[key][1]} {self._sub_formulas[key][0]}  {self._sub_formulas[key][2]}   (Or)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "Implies":
                # The subformula is an Implies
                print(
                    f"{key} = {self._sub_formulas[key][1]} {self._sub_formulas[key][0]}  {self._sub_formulas[key][2]}   (Implies)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "Equivalence":
                # The subformula is an Equivalent
                print(
                    f"{key} = {self._sub_formulas[key][1]} {self._sub_formulas[key][0]}  {self._sub_formulas[key][2]}   (Equivalent)")
            elif self._checkFormulaType(self._sub_formulas[key]) == "Not":
                # The subformula is a Not
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
                elif node[0] in {'('} and node[len(node) - 1] in {')'}:
                    return self.visit_parenthesis(node[0], node[len(node) - 1], node[1])
                elif node[0] in {'G', 'F'}:  # Temporal operators with a single argument
                    if (int(node[2]) > int(node[4])):
                        raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                    return self.visit_unary_temporal_operator(node[0], node[2], node[4], node[6])
            elif isinstance(node[1], str):
                # print(node[0])
                if node[1] in {'U'}:  # Temporal operators with two argument
                    if (int(node[3]) > int(node[5])):
                        raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                    return self.visit_binary_temporal_operator(node[1], node[3], node[5], node[0], node[7])
                elif node[1] in {'&&', '||', '->', '<->'}:  # Binary logical operators
                    return self.visit_binary_logical(node[1], node[0], node[2:])
        elif isinstance(node, str):
            return self.visit_identifier(node)

    def visit_parenthesis(self, openPar, closePar, expr):
        # Visit the expression within the temporal operator
        # print(f"Visiting parenthesis: {openPar}{closePar}")
        return self.visit(expr)

    def visit_unary_temporal_operator(self, operator, time_interval_low, time_interval_high, expr):
        # Visit the expression within the temporal operator
        # print(f"Visiting Unary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        ret = self.visit(expr)
        prop = self._addSubFormula([operator, time_interval_low, time_interval_high, ret[0]])
        return prop, str(int(time_interval_high) + int(ret[1]))

    def visit_binary_temporal_operator(self, operator, time_interval_low, time_interval_high, left, right):
        # Visit the expression within the temporal operator
        # print(f"Visiting Binary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        ret_left = self.visit(left)
        ret_right = self.visit(right)

        prop = self._addSubFormula([operator, time_interval_low, time_interval_high, ret_left[0], ret_right[0]])
        return prop, str(int(time_interval_high) + max(int(ret_left[1]), int(ret_right[1])))

    def visit_unary_logical(self, operator, expr):
        # Visit both sides of the logical expression
        # print(f"Visiting Unary Logical Operator: {operator}")
        ret = self.visit(expr)
        return self._addSubFormula([operator, ret[0]]), ret[1]

    def visit_binary_logical(self, operator, left, right):
        # Visit both sides of the logical expression
        # print(f"Visiting Logical Operator: {operator}, {left}, {right}")
        ret_left = self.visit(left)
        ret_right = self.visit(right)

        if operator in {'&&', '||', '->', '<->'}:
            prop = self._addSubFormula([operator, ret_left[0], ret_right[0]])
        return prop, str(max(int(ret_left[1]), int(ret_right[1])))

    def visit_binary_relational(self, operator, left, right):
        # Visit both sides of the relational expression
        # print(f"Visiting Relational Operator: {operator}")
        prop = ""

        if left in self._variables:
            # print(f"Key '{left}' is in the dictionary.")

            if (self._variables[left] == 'binary'):
                raise SyntaxError(f"Variable '{left}' cannot be real and binary")

            # print(self._real_constraints[left].keys())
            if operator in self._real_constraints[left].keys():
                # print(f"'{operator}' is in {self._real_constraints[left].keys()}")
                if right in self._real_constraints[left][operator].keys():
                    prop = self._real_constraints[left][operator][right]
                    # print(prop)
                else:
                    prop = self._addSubFormula([left, operator, right])
                    self._real_constraints[left][operator] = {right: prop}
            else:
                # print(f"'{operator}' is not in {self._real_constraints[left].keys()}")
                prop = self._addSubFormula([left, operator, right])
                self._real_constraints[left][operator] = {right: prop}
        else:
            # print(f"Key '{left}' is not in the dictionary.")
            self._variables[left] = 'real'
            # print(f"Key '{left}' added in the dictionary.")
            prop = self._addSubFormula([self.visit(left), operator, self.visit(right)])
            self._real_constraints[left] = {operator: {right: prop}}
        return prop, '1'

    def visit_binary_variable(self, binary_var):
        # Simply return the identifier, in more complex cases you might want to look up values
        # print(f"Visiting Binary Variable: {binary_var}")
        prop = ""
        if binary_var in self._variables:
            # print(f"Key '{binary_var}' is in the dictionary.")
            if (self._variables[binary_var] == 'real'):
                raise SyntaxError(f"Variable '{binary_var}' cannot be real and binary")
            prop = self._binary_constraints[binary_var]
        else:
            # print(f"Key '{binary_var}' is not in the dictionary.")
            self._variables[binary_var] = 'binary'
            # print(f"Key '{binary_var}' added in the dictionary.")
            prop = self._addSubFormula(binary_var)
            self._binary_constraints[binary_var] = prop

        return prop, '1'

    def visit_identifier(self, identifier):
        # Simply return the identifier, in more complex cases you might want to look up values
        # print(f"Visiting Identifier: {identifier}")
        return identifier

    def _encode_variables(self, time_horizon, smt_variables, verbose):
        if verbose:
            print("")
            print("# Encode the Real/Binary variables ")
            print("")
        for key in self._variables:
            for t in range(time_horizon):
                prop = f"{key}_t{self._encode_time(t, time_horizon)}"
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
        sorted_model = {}
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
        # This hashtable will contains the variables for the SMT Solver
        smt_variables = {}

        if verbose:
            print("# SMT Encoding in Python")
            print("")
            print("#===========================")
            print("from z3 import *")
            print("")

        self._encode_variables(time_horizon, smt_variables, verbose)

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
                prop = f"{key}_t{self._encode_time(t, time_horizon)}"
                # print(f"{prop}")
                if len(self._sub_formulas[key]) == 1:
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    smt_variables[prop] = Bool(prop)
                    if (root_prop != prop):
                        if verbose:
                            print(
                                f"s.add({prop} == {self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)})")
                        s.add(smt_variables[prop] == smt_variables[
                            f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"])
                    else:
                        if verbose:
                            print(f"s.add({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)})")
                        s.add(smt_variables[f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"])
                elif len(self._sub_formulas[key]) == 3 and self._sub_formulas[key][1] in {'<', '<=', '>', '>=', '==',
                                                                                          '!='}:
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    smt_variables[prop] = Bool(prop)
                    if self._sub_formulas[key][1] == '<':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] < float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} < {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] < float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} < {self._sub_formulas[key][2]})")
                    elif self._sub_formulas[key][1] == '<=':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] <= float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} <= {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] <= float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} <= {self._sub_formulas[key][2]})")
                    elif self._sub_formulas[key][1] == '>':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] > float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} > {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] > float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add(({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} > {self._sub_formulas[key][2]}))")
                    elif self._sub_formulas[key][1] == '>=':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] >= float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} >= {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] >= float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add(({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} >= {self._sub_formulas[key][2]}))")
                    elif self._sub_formulas[key][1] == '==':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] == float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} == {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] == float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add(({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} == {self._sub_formulas[key][2]}))")
                    elif self._sub_formulas[key][1] == '!=':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] != float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} != {self._sub_formulas[key][2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)}"] != float(
                                self._sub_formulas[key][2])))
                            if verbose:
                                print(
                                    f"s.add(({self._sub_formulas[key][0]}_t{self._encode_time(t, time_horizon)} != {self._sub_formulas[key][2]}))")
                elif len(self._sub_formulas[key]) == 4 and self._sub_formulas[key][0] in {'G',
                                                                                          'F'}:  # Ezio in the case of nested operation it is necessary to do all the t

                    int_a = int(self._sub_formulas[key][1])
                    int_b = int(self._sub_formulas[key][2])
                    if t + int_b < time_horizon:

                        prop1 = self._sub_formulas[key][3]
                        flag = 1
                        for i in range(int_a, int_b + 1):
                            if not f"{prop1}_t{self._encode_time(t + i, time_horizon)}" in smt_variables:
                                flag = 0
                                break
                        if flag:
                            if verbose:
                                print(f"{prop} = Bool('{prop}')")
                            smt_variables[prop] = Bool(prop)

                            prop1_list = [smt_variables[f"{prop1}_t{self._encode_time(t + i, time_horizon)}"] for i in
                                          range(int_a, int_b + 1)]
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

                elif len(self._sub_formulas[key]) == 3 and self._sub_formulas[key][0] in {'&&', '||', '->', '<->'}:
                    prop1 = f"{self._sub_formulas[key][1]}_t{self._encode_time(t, time_horizon)}"
                    prop2 = f"{self._sub_formulas[key][2]}_t{self._encode_time(t, time_horizon)}"
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
                        elif self._sub_formulas[key][0] == '->':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == Implies(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add({prop} == Implies({prop1},{prop2}))")
                            else:
                                s.add(Implies(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add(Implies({prop1},{prop2}))")
                        elif self._sub_formulas[key][0] == '<->':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == (smt_variables[prop1] == smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add({prop} == ({prop1} == {prop2}))")
                            else:
                                s.add((smt_variables[prop1] == smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add(({prop1} == {prop2}))")
                elif len(self._sub_formulas[key]) == 2 and self._sub_formulas[key][0] in {'!'}:
                    prop1 = f"{self._sub_formulas[key][1]}_t{self._encode_time(t, time_horizon)}"
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

                        # We create
                        if verbose:
                            print("")
                            print(f"{prop}_A = Bool('{prop}_A')")
                        smt_variables[f"{prop}_A"] = Bool(f"{prop}_A")
                        prop_a_list = [smt_variables[f"{prop1}_t{self._encode_time(t + i, time_horizon)}"] for i in
                                       range(0, int_a + 1)]
                        s.add(smt_variables[f"{prop}_A"] == And(prop_a_list))
                        if verbose:
                            print(f"s.add({prop}_A == And({prop_a_list}))")

                        smt_variables[f"{prop}_B"] = Bool(f"{prop}_B")
                        if verbose:
                            print("")
                            print(f"{prop}_B = Bool('{prop}_B')")
                        prop_b_list = [smt_variables[f"{prop2}_t{self._encode_time(t + i, time_horizon)}"] for i in
                                       range(int_a, int_b + 1)]
                        s.add(smt_variables[f"{prop}_B"] == Or(prop_b_list))
                        if verbose:
                            print(f"s.add({prop}_B == Or({prop_b_list}))")
                            print("")
                        if not f"{key}_t{self._encode_time(t + int_a, time_horizon)}_C" in smt_variables.keys():
                            if verbose:
                                print(
                                    f"The variables {key}_t{self._encode_time(t + int_a, time_horizon)}_C is not in smt_variables")

                            if not f"{key}_t{self._encode_time(time_horizon, time_horizon)}_C" in smt_variables.keys():
                                if verbose:
                                    print(
                                        f"{key}_t{self._encode_time(time_horizon - 1, time_horizon)}_C = Bool('{key}_t{self._encode_time(time_horizon - 1, time_horizon)}_C')")
                                smt_variables[f"{key}_t{self._encode_time(time_horizon - 1, time_horizon)}_C"] = Bool(
                                    f"{key}_t{self._encode_time(time_horizon - 1, time_horizon)}_C")
                                s.add(smt_variables[f"{key}_t{self._encode_time(time_horizon - 1, time_horizon)}_C"] ==
                                      smt_variables[f"{prop2}_t{self._encode_time(time_horizon - 1, time_horizon)}"])
                                if verbose:
                                    print(
                                        f"s.add({key}_t{self._encode_time(time_horizon - 1, time_horizon)}_C == {prop2}_t{self._encode_time(time_horizon - 1, time_horizon)})")
                            print("")
                            for i in range(t + int_a, time_horizon - 1):

                                k = time_horizon - i - 2 + int_a
                                # print(f"i = {i}, k = {k}")
                                if not f"{key}_t{self._encode_time(k, time_horizon)}_C" in smt_variables.keys():
                                    if verbose:
                                        print(
                                            f"{key}_t{self._encode_time(k, time_horizon)}_C = Bool('{key}_t{self._encode_time(k, time_horizon)}_C')")
                                    smt_variables[f"{key}_t{self._encode_time(k, time_horizon)}_C"] = Bool(
                                        f"{key}_t{self._encode_time(k, time_horizon)}_C")
                                    if verbose:
                                        print(
                                            f"s.add({key}_t{self._encode_time(k, time_horizon)}_C == Or({prop2}_t{self._encode_time(k, time_horizon)},And({prop1}_t{self._encode_time(k + 1, time_horizon)},{key}_t{self._encode_time(k + 1, time_horizon)}_C))")
                                    s.add(smt_variables[f"{key}_t{self._encode_time(k, time_horizon)}_C"] == Or(
                                        smt_variables[f"{prop2}_t{self._encode_time(k, time_horizon)}"],
                                        And(smt_variables[f"{prop1}_t{self._encode_time(k, time_horizon)}"],
                                            smt_variables[f"{key}_t{self._encode_time(k + 1, time_horizon)}_C"])))
                        if verbose:
                            print("")
                        smt_variables[f"{prop}"] = Bool(f"{prop}")
                        if verbose:
                            print(f"{prop} = Bool('{prop}')")

                        if (root_prop != prop):
                            s.add(
                                smt_variables[f"{prop}"] == And(smt_variables[f"{prop}_A"], smt_variables[f"{prop}_B"],
                                                                smt_variables[
                                                                    f"{key}_t{self._encode_time(int_a, time_horizon)}_C"]))
                            if verbose:
                                print(
                                    f"s.add({prop} == And({prop}_A,{prop}_B,{key}_t{self._encode_time(int_a, time_horizon)}_C))")
                        else:
                            s.add(And(smt_variables[f"{prop}_A"], smt_variables[f"{prop}_B"],
                                      smt_variables[f"{key}_t{self._encode_time(int_a, time_horizon)}_C"]))
                            if verbose:
                                print(
                                    f"s.add(And({prop}_A,{prop}_B,{key}_t{self._encode_time(int_a, time_horizon)}_C))")
        if verbose:
            print("")
            print("================================")
            print(f"Num of variables in SMT solver = {len(smt_variables.keys())}")
            print("")
            print("Solver statistics")
            print(s.statistics())
            print(s)

        if s.check() == unsat:
            print("")
            print("The STL requirements are inconsistent.")
            print(f"The unsat core is {s.unsat_core()}")
        else:
            print("")
            print("The STL requirements are consistent. This is a signal witness:")
            print(self._filter_witness(s.model()))


# End class STLConsistencyChecker


# Example STL expression
# stl_expression = " F [10,100000] (! (a > 0) &&  ! (b >= 0))"
# stl_expression = "!((a <-> ! b) <-> ! (a <-> b))"
# stl_expression = "a && a"
# stl_expression = " F [0,5] (a > 0)"
# stl_expression = " F [0,5] (a > 0 && b>3)"
# stl_expression = "F [0,5] G [2,5] ! a"
# stl_expression = "(! ! a && a) && (! ! ! a)"
# stl_expression = "!(a > 0)"
# stl_expression = "(! x<0 && y>0) U[1,5] ( y > 6.07)"
# stl_expression = "G[0,5] ((x > 3) && (F[2,7] (y < 2)))"
# stl_expression = "G[0,5] ((x > 3) && (y < 2))"
# stl_expression = " (x > 4) && ! (y > 3)" #ok
# stl_expression = "G[0,5] ((F[2,7] (y < 2)))"
# stl_expression = "G[0,5] (x > 5)"
# stl_expression = "G[0,5] (F[7,9] (x > 3))"
# stl_expression = "G[0,10](x U[2,5] y)" #witness non ok
# stl_expression = "x>0 U[2,7] y < 0"
# stl_expression = "G[2,5] x > 5 || G[1,3] x < 0"
# stl_expression = "G[2,5] (x > 5 || x < 0)"
# stl_expression = "! a && a" #ok
# stl_expression = "((a && (! b)) && a)"
# !(a -> b) && a
# stl_expression = "(a && (a -> b)) && !b"
# stl_expression = "(a && b && !b)"
# stl_expression = "(G[0,10]a && (F[2,5](a && (a -> b)))) <-> (G[0,10] a && (F[2,5](a && b)))"
# stl_expression = "a->(b->a) <-> (a->b)"
# !(a -> a -> b)
# stl_expression = "c && d && b && a && (! b) && c"
# "c && a && b && a && d && (! b) && c"
# "d && !(c -> b)"
# "!(d -> (c -> b))"
# "!(b -> (a -> (d -> (c -> b))))"
# stl_expression = "a U [2,5] b"
# stl_expression = "(y>6) U[3,7] (y < 3)"
# stl_expression = "F[0,5](x>3 || x<5)"
# stl_expression = "G[0,5]((a && b) || (a && !b && c))"
# stl_expression = "G[0,5](a || (b && c))" #49,118
#stl_expression = "G[0,5]((a || b) && (a || c))" #55, 148


# We can use the consistency checking to verify the equivalence of the formulas
# For example De Morgan Laws
# stl_expression =  "!(!(a && b) <-> (!a || !b)) " #This formula should be unsat
# stl_expression =  "!(!(a || b) <-> (!a && !b)) " #This formula should be unsat
# stl_expression =  "!(a <-> a)"                   #This formula should be unsat
# stl_expression =  "!(G[0,1] a <-> F[0,1] a)"

# stl_expression = "!(G[0,5] G[2,4] a <-> G[2,9] a)" #This formula should be unsat

# stl_expression = "F [2,3] a < 0 && G [0,5] a > 0"
# stl_expression = "(a && (a -> (a || b)))"
# stl_expression = "(G[0,2] a && (G[0,2] a -> F[0,2] a))"

stl_expression = "!(G[0,2] (!a <-> ! F[0,2] a))" #like this it works, you need the parentheses after the globally
# stl_expression = "!(G[0,2] ((!a) <-> (! F[0,2] a)))"
# stl_expression = "!(! G[0,2] a <-> F[0,2] ! a)"
# stl_expression = "G[0,100] (x > 0.5 -> F [0,10] (y < 10)) && G[0,100] (x > 0.5 && y > 10)"

# stl_expression = "(G[0,2] !b) && (G [0,4] (a -> F[0,2] b)) && (!b -> a)"

# stl_expression = "!(G[0,2] a -> G[0,2] a)"

# Create a checker and visit the parsed expression
checker = STLConsistencyChecker()
parsed_expr = checker.parseSTL(stl_expression)
print("Input STL expression: ", stl_expression)
print("Parsed STL Expression:", parsed_expr)
result = checker.visit(parsed_expr)

print(f"Formula_horizon =  {result[1]}")
print(f"Root sub_formula = {result[0]} ")
checker.printSubFormulas()
# checker.cleanUnreachableSubFormulas (result[0])
checker.printSubFormulas()
formula_horizon = int(result[1])
variables = checker.getVariableList()
propositions = checker.getBasicPropositionsList()
expression = list(propositions.values())

checker.solve(int(result[1]), result[0], True)
