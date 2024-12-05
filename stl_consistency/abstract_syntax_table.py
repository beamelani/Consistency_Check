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

import collections

from stl_consistency.parser import STLParser

class STLAbstractSyntaxTable:

    def __init__(self, formula):
        self._variables = {}  # Protected variable
        self._real_constraints = {}  # Protected variable
        self._binary_constraints = {}  # Protected variable
        self._sub_formulas = collections.OrderedDict()  # Protected variable
        self._prop_count = 0  # Protected variable
        self._root_formula, self._time_horizon = self._visit(formula)

    def setRootFormula(self, root_formula):
        self._root_formula = root_formula

    def getFormulaKeyValuePairs(self):
        return self._sub_formulas.items()

    def getFormula(self, key):
        return self._sub_formulas[key]

    def getRootFormula(self):
        return self._root_formula

    def setTimeHorizon (self, time_horizon):
        self._time_horizon = time_horizon

    def getTimeHorizon (self):
        return self._time_horizon

    def containsVariable(self, variable):
        return variable in self._variables

    def getVariableType (self, variable):
        return self._variables[variable]

    def addRealVariable(self, variable):
        self._variables[variable] = 'real'

    def addBinaryVariable(self, variable):
        self._variables[variable] = 'binary'

    def addBinaryConstraint(self, binary_var, prop):
        self._binary_constraints[binary_var] = prop

    def getSubFormulaKeyFromBinaryConstraints (self, binary_var):
        return self._binary_constraints[binary_var]

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

    def _insSubFormula(self, subformula):
        #print(f"Insert {subformula}")
        key = f"_phi{self._prop_count}"
        self._sub_formulas[key] = subformula
        self._prop_count = self._prop_count + 1
        #self.printSubFormulas()
        return key

    def addSubFormula(self, sub_formula):
        # First search if the sub_formula is already present
        # in the list of subformulas
        #print(f"Add {sub_formula}")
        key = self._findFormulaKey(sub_formula)
        if key is not None:
            return key

        # If the subformula is not found then add it
        return self._insSubFormula(sub_formula)

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

    def genExpSubFormula(self, key_root):
        match self._checkFormulaType(self._sub_formulas[key_root]):
            case "Literal":
                return f"{self._sub_formulas[key_root][0]}"
            case "Not":
                return f"! ({self.genExpSubFormula(self._sub_formulas[key_root][1])})"
            case "True":
                return f"True"
            case "False":
                return f"False"
            case "RConstraint":
                return f"({self._sub_formulas[key_root][0]} {self._sub_formulas[key_root][1]} {self._sub_formulas[key_root][2]})"
            case "And":
                return f"({self.genExpSubFormula(self._sub_formulas[key_root][1])} && {self.genExpSubFormula(self._sub_formulas[key_root][2])})"
            case "Or":
                return f"({self.genExpSubFormula(self._sub_formulas[key_root][1])} || {self.genExpSubFormula(self._sub_formulas[key_root][2])})"
            case "Implies":
                return f"({self.genExpSubFormula(self._sub_formulas[key_root][1])} -> {self.genExpSubFormula(self._sub_formulas[key_root][2])})"
            case "Equivalence":
                return f"({self.genExpSubFormula(self._sub_formulas[key_root][1])} <-> {self.genExpSubFormula(self._sub_formulas[key_root][2])})"
            case "Always":
                return f"G [{self._sub_formulas[key_root][1]},{self._sub_formulas[key_root][2]}] ({self.genExpSubFormula(self._sub_formulas[key_root][3])})"
            case "Eventually":
                return f"F [{self._sub_formulas[key_root][1]},{self._sub_formulas[key_root][2]}] ({self.genExpSubFormula(self._sub_formulas[key_root][3])})"
            case "Until":
                return f"({self.genExpSubFormula(self._sub_formulas[key_root][3])}) U [{self._sub_formulas[key_root][1]},{self._sub_formulas[key_root][2]}] ({self.genExpSubFormula(self._sub_formulas[key_root][4])})"

    def _findFormulaKey(self, sub_formula):
        for key in self._sub_formulas.keys():
            if self._sub_formulas[key] == sub_formula:
                return key
        return None

    def _cmpForTypeByKey(self, key, type):
        if self._checkFormulaType(self._sub_formulas[key]) == type:
            return True
        return False

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


    def _visit(self, node):
        # Determine the type of the node and call the appropriate visit method

        if isinstance(node, list):

            if len(node) == 1:
                # Single element (either a terminal or a unary expression)
                if isinstance(node[0], str):
                    return self._visit_binary_variable(node[0])
                return self._visit(node[0])
            elif len(node) == 3 and isinstance(node[1], str) and node[1] in {'<', '<=', '>', '>=', '==', '!='}:
                return self._visit_binary_relational(node[1], node[0], node[2])
            elif not isinstance(node[0], list):
                if node[0] == '!':
                    return self._visit_unary_logical(node[0], node[1])
                elif node[0] in {'G', 'F'}:  # Temporal operators with a single argument
                    if (int(node[1]) > int(node[2])):
                        raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                    return self._visit_unary_temporal_operator(node[0], node[1], node[2], node[3])
            elif isinstance(node[1], str):
                if node[1] in {'U'}:  # Temporal operators with two arguments
                    if (int(node[2]) > int(node[3])):
                        raise SyntaxError("The lower bound of the time interval is greater than the upper bound")
                    return self._visit_binary_temporal_operator(node[1], node[2], node[3], node[0], node[4])
                elif node[1] in {'&&', '||', '->', '<->'}:  # Binary logical operators
                    return self._visit_binary_logical(node[1], node[0], node[2:])
        elif isinstance(node, str):
            return self._visit_binary_variable(node)

    def _visit_unary_temporal_operator(self, operator, time_interval_low, time_interval_high, expr):
        # Visit the expression within the temporal operator
        #print(f"Visiting Unary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        ret = self._visit(expr)
        prop = self.addSubFormula([operator, time_interval_low, time_interval_high, ret[0]])
        return prop, str(int(time_interval_high) + int(ret[1]))

    def _visit_binary_temporal_operator(self, operator, time_interval_low, time_interval_high, left, right):
        # Visit the expression within the temporal operator
        # print(f"Visiting Binary Temporal Operator: {operator}" + " with time Interval [" + time_interval_low + "," + time_interval_high + "]")
        ret_left = self._visit(left)
        ret_right = self._visit(right)

        prop = self.addSubFormula([operator, time_interval_low, time_interval_high, ret_left[0], ret_right[0]])
        return prop, str(int(time_interval_high) + max(int(ret_left[1]), int(ret_right[1])))

    def _visit_unary_logical(self, operator, expr):
        # Visit both sides of the logical expression
        # print(f"Visiting Unary Logical Operator: {operator}")
        ret = self._visit(expr)
        return self.addSubFormula([operator, ret[0]]), ret[1]

    def _visit_binary_logical(self, operator, left, right):
        # Visit both sides of the logical expression
        # print(f"Visiting Logical Operator: {operator}, {left}, {right}")
        ret_left = self._visit(left)
        ret_right = self._visit(right)

        if operator in {'&&', '||', '->', '<->'}:
            prop = self.addSubFormula([operator, ret_left[0], ret_right[0]])
        return prop, str(max(int(ret_left[1]), int(ret_right[1])))

    def _visit_binary_relational(self, operator, left, right):
        # Visit both sides of the relational expression
        # print(f"Visiting Relational Operator: {operator}")
        lhs = self._visit_real_expr(left)
        rhs = self._visit_real_expr(right)
        if (operator, lhs, rhs) in self._real_constraints:
            return self._real_constraints[(operator, lhs, rhs)]

        prop = self.addSubFormula([operator, lhs, rhs])
        self._real_constraints[(operator, lhs, rhs)] = prop

        return prop, '1'

    def _visit_real_expr(self, expr):
        if isinstance(expr, str):
            if STLParser.is_float(expr):
                return expr
            else:
                # expr is a real variable
                if self.containsVariable(expr) and self.getVariableType(expr) != 'real':
                    raise ValueError(f"Variable '{left}' cannot be real and binary")
                self.addRealVariable(expr)
                return expr
        else:
            assert isinstance(expr, list)
            if len(expr) == 1:
                return self._visit_real_expr(expr[0])
            assert len(expr) == 3
            return (expr[1], self._visit_real_expr(expr[0]), self._visit_real_expr(expr[2]))

    def _visit_binary_variable(self, binary_var):
        # Simply return the identifier, in more complex cases you might want to look up values
        # print(f"Visiting Binary Variable: {binary_var}")
        prop = ""
        if self.containsVariable(binary_var):
            # print(f"Key '{binary_var}' is in the dictionary.")
            if self.getVariableType(binary_var) == 'real':
                raise SyntaxError(f"Variable '{binary_var}' cannot be real and binary")
            prop = self.getSubFormulaKeyFromBinaryConstraints(binary_var)
        else:
            # print(f"Key '{binary_var}' is not in the dictionary.")
            self.addBinaryVariable(binary_var)
            # print(f"Key '{binary_var}' added in the dictionary.")
            prop = self.addSubFormula([binary_var])
            self.addBinaryConstraint(binary_var, prop)

        return prop, '1'

    def print(self):
        # Print the list of the subformulas
        print("")
        print("===============================")
        print("STL Abstract Syntax Table")
        print("===============================")
        print("")
        print(f"Root = {self._root_formula}")
        print(f"Time horizon = {self._time_horizon}")
        print(f"Num of formulas = {self._prop_count}")


        print("")
        print("Table of STL Formulas")
        print("===============================")
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
        print("===============================")

    def print_vars(self):
        print(self._variables)
        print(self._real_constraints)
        print(self._binary_constraints)
        print(self._sub_formulas)
