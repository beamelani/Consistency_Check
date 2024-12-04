from stl_consistency.abstract_syntax_table import STLAbstractSyntaxTable

from z3 import *

class SMTSTLConsistencyChecker:

    def __init__(self):
        pass

    def _encode_time(self, t, time_horizon):
        # Convert the number in a string
        t_str = str(t)
        # Add 0 to complete the string
        return t_str.zfill(len(str(time_horizon)))

    def _encode_variables(self, table, time_horizon, smt_variables, verbose):
        if verbose:
            print("")
            print("# Encode the Real/Binary variables ")
            print("")
        for key in table.getVariableList():
            for t in range(time_horizon):
                prop = f"{key}_t{self._encode_time(t, time_horizon)}"
                if table.getVariableType(key) == 'real':
                    if verbose:
                        print(f"{prop} = Real('{prop}')")
                    smt_variables[prop] = Real(prop)
                elif table.getVariableType(key) == 'binary':
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

    def solve(self, table, verbose):

        # This hashtable will contains the variables for the SMT Solver
        smt_variables = {}

        time_horizon = int(table.getTimeHorizon())
        root_formula = table.getRootFormula()

        if verbose:
            print("# SMT Encoding in Python")
            print("")
            print("#===========================")
            print("from z3 import *")
            print("")

        self._encode_variables(table, time_horizon, smt_variables, verbose)

        if verbose:
            print("")
            print("# Instantiate the SMT Solver")
            print("s = Solver()")

        s = Solver()
        root_prop = f"{root_formula}_t{self._encode_time(0, time_horizon)}"

        for key in table.getFormulasKeys():
            # If the sub-formula to consider is the root formula then
            # we compute only the for time t00
            # we introduce another variable
            time_limit = 1
            if key != root_formula:
                time_limit = time_horizon
            for t in range(time_limit):
                prop = f"{key}_t{self._encode_time(t, time_horizon)}"

                if len(table.getFormula(key)) == 1:
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    smt_variables[prop] = Bool(prop)
                    if (root_prop != prop):
                        if verbose:
                            print(
                                f"s.add({prop} == {table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)})")
                        s.add(smt_variables[prop] == smt_variables[
                            f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"])
                    else:
                        if verbose:
                            print(f"s.add({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)})")
                        s.add(smt_variables[f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"])
                elif len(table.getFormula(key)) == 3 and table.getFormula(key)[1] in {'<', '<=', '>', '>=', '==','!='}:
                    if verbose:
                        print(f"{prop} = Bool('{prop}')")
                    smt_variables[prop] = Bool(prop)
                    if table.getFormula(key)[1] == '<':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] < float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} < {table.getFormula(key)[2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] < float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} < {table.getFormula(key)[2]})")
                    elif table.getFormula(key)[1] == '<=':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] <= float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} <= {table.getFormula(key)[2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] <= float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} <= {table.getFormula(key)[2]})")
                    elif table.getFormula(key)[1] == '>':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] > float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} > {table.getFormula(key)[2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] > float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add(({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} > {table.getFormula(key)[2]}))")
                    elif table.getFormula(key)[1] == '>=':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] >= float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} >= {table.getFormula(key)[2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] >= float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add(({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} >= {table.getFormula(key)[2]}))")
                    elif table.getFormula(key)[1] == '==':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] == float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} == {table.getFormula(key)[2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] == float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add(({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} == {table.getFormula(key)[2]}))")
                    elif table.getFormula(key)[1] == '!=':
                        if (root_prop != prop):
                            s.add(smt_variables[prop] == (smt_variables[
                                                              f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] != float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add({smt_variables[prop]} == ({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} != {table.getFormula(key)[2]}))")
                        else:
                            s.add((smt_variables[
                                       f"{table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)}"] != float(
                                table.getFormula(key)[2])))
                            if verbose:
                                print(
                                    f"s.add(({table.getFormula(key)[0]}_t{self._encode_time(t, time_horizon)} != {table.getFormula(key)[2]}))")
                elif len(table.getFormula(key)) == 4 and table.getFormula(key)[0] in {'G','F'}:  # Ezio in the case of nested operation it is necessary to do all the t

                    int_a = int(table.getFormula(key)[1])
                    int_b = int(table.getFormula(key)[2])
                    if t + int_b < time_horizon:

                        prop1 = table.getFormula(key)[3]
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
                            if table.getFormula(key)[0] == 'G':
                                if (root_prop != prop):
                                    s.add(smt_variables[prop] == And(prop1_list))
                                    if verbose:
                                        print(f"s.add({prop} == And({prop1_list}))")
                                else:
                                    s.add(And(prop1_list))
                                    if verbose:
                                        print(f"s.add(And({prop1_list}))")
                            elif table.getFormula(key)[0] == 'F':
                                if (root_prop != prop):
                                    s.add(smt_variables[prop] == Or(prop1_list))
                                    if verbose:
                                        print(f"s.add({prop} == Or({prop1_list}))")
                                else:
                                    s.add(Or(prop1_list))
                                    if verbose:
                                        print(f"s.add(Or({prop1_list}))")

                elif len(table.getFormula(key)) == 3 and table.getFormula(key)[0] in {'&&', '||', '->', '<->'}:
                    prop1 = f"{table.getFormula(key)[1]}_t{self._encode_time(t, time_horizon)}"
                    prop2 = f"{table.getFormula(key)[2]}_t{self._encode_time(t, time_horizon)}"
                    if prop1 in smt_variables.keys() and prop2 in smt_variables.keys():
                        if verbose:
                            print(f"{prop} = Bool('{prop}')")
                        smt_variables[prop] = Bool(prop)
                        if table.getFormula(key)[0] == '&&':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == And(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add({prop} == And({prop1},{prop2}))")
                            else:
                                s.add(And(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add(And({prop1},{prop2}))")
                        elif table.getFormula(key)[0] == '||':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == Or(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add({prop} == Or({prop1},{prop2}))")
                            else:
                                s.add(Or(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add(Or({prop1},{prop2}))")
                        elif table.getFormula(key)[0] == '->':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == Implies(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add({prop} == Implies({prop1},{prop2}))")
                            else:
                                s.add(Implies(smt_variables[prop1], smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add(Implies({prop1},{prop2}))")
                        elif table.getFormula(key)[0] == '<->':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == (smt_variables[prop1] == smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add({prop} == ({prop1} == {prop2}))")
                            else:
                                s.add((smt_variables[prop1] == smt_variables[prop2]))
                                if verbose:
                                    print(f"s.add(({prop1} == {prop2}))")
                elif len(table.getFormula(key)) == 2 and table.getFormula(key)[0] in {'!'}:
                    prop1 = f"{table.getFormula(key)[1]}_t{self._encode_time(t, time_horizon)}"
                    if prop1 in smt_variables.keys():
                        if verbose:
                            print(f"{prop} = Bool('{prop}')")
                        smt_variables[prop] = Bool(prop)
                        if table.getFormula(key)[0] == '!':
                            if (root_prop != prop):
                                s.add(smt_variables[prop] == Not(smt_variables[prop1]))
                                if verbose:
                                    print(f"s.add({prop} == Not({prop1}))")
                            else:
                                s.add(Not(smt_variables[prop1]))
                                if verbose:
                                    print(f"s.add(Not({prop1}))")
                elif len(table.getFormula(key)) == 5 and table.getFormula(key)[0] in {'U'}:
                    int_a = int(table.getFormula(key)[1])
                    int_b = int(table.getFormula(key)[2])
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

                    prop1 = table.getFormula(key)[3]
                    prop2 = table.getFormula(key)[4]

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

        check_res = s.check()

        if check_res == unsat:
            print("The STL requirements are inconsistent.")
            print(f"The unsat core is {s.unsat_core()}")
            return False
        elif check_res == sat:
            print("The STL requirements are consistent. This is a signal witness:")
            print(self._filter_witness(s.model()))
            return True
        else:
            print("Unable to check consistency.")
            return False


def smt_check_consistency(parsed_formula, verbose=False):
    table = STLAbstractSyntaxTable(parsed_formula)

    if verbose:
        print("Parsed STL Expression:", parsed_formula)
        table.print()

    checker = SMTSTLConsistencyChecker()
    return checker.solve(table, verbose)
