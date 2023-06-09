import copy
import random
import subprocess
from typing import List

from src.translate.pddl import Atom
from src.translate.pddl.effects import *
from pddl.conditions import *
import invariant_candidate
from invariant_candidate import *
def weaken(inv_cand : InvariantCandidate, action : PropositionalAction):
    print("inv_cand: ")
    print(type(inv_cand))
    inv_cand.dump()
    inv_cand_set = set()
    curr_inv_list = set(inv_cand.parts)
    for cond, eff in action.add_effects:
        if eff not in curr_inv_list:
            curr_inv_list.add(eff)
            inv_cand_set.add(InvariantCandidate(part=curr_inv_list))
            curr_inv_list.remove(eff)
    for cond, eff in action.del_effects:
        if eff.negate() not in curr_inv_list:
            curr_inv_list.add(eff.negate())
            inv_cand_set.add(InvariantCandidate(part=curr_inv_list))
            curr_inv_list.remove(eff.negate())
    return inv_cand_set
    # weaken of form X -> l_1 to X -> l_1 v l_2


def regression(formula : Condition, operator : PropositionalAction):
    # eff_list = eff(o)
    eff_list = get_effects_from_action(operator)
    # start recursive call
    for pre in operator.precondition:
        handempty_conversion(pre)
    return Conjunction([Conjunction(operator.precondition), regression_rec(formula, Conjunction(eff_list))]).simplified()

def regression_rec(formula : Condition, effect : Condition):
    if isinstance(formula, Truth):
        return Truth()
    if isinstance(formula, Falsity):
        return Falsity()
    if isinstance(formula, NegatedAtom):
        return regression_rec(formula.negate(), effect).negate()
    if isinstance(formula, Disjunction) or isinstance(formula, Conjunction):
        regr_list = []
        for part in formula.parts:
            regr_list.append(regression_rec(part, effect))
        if isinstance(formula, Conjunction):
            return Conjunction(regr_list)
        else:
            return Disjunction(regr_list)
    return Disjunction([eff_con(formula, effect), Conjunction([formula, eff_con(formula.negate(), effect).negate()])])


def eff_con(atomic_effect : Condition, effect : Condition):
    if isinstance(effect, Truth):
        return Falsity()
    if isinstance(effect, Conjunction):
        eff_con_list = []
        for part in effect.parts:
            eff_con_list.append(eff_con(atomic_effect, part))
        return Disjunction(eff_con_list)
    if isinstance(effect, ConditionalEffect):
        return Conjunction([effect.condition, eff_con(atomic_effect, effect.effect)])
    if atomic_effect == effect:
        return Truth()
    return Falsity()


def get_effects_from_action(operator : Condition):
    eff_list = []
    # add all add_effects
    for cond, eff in operator.add_effects:
        if len(cond) == 0:
            eff_list.append(handempty_conversion(eff))
        else:
            eff_list.append(ConditionalEffect(condition=cond, effect=handempty_conversion(eff)))
    # add all del_effects as negated effect
    for cond, eff in operator.del_effects:
        if len(cond) == 0:
            eff_list.append(handempty_conversion(eff.negate()))
        else:
            eff_list.append(ConditionalEffect(condition=cond, effect=handempty_conversion(eff.negate())))
    return eff_list


def formula_to_list(formula : Condition):

    l = []
    x_found = False
    y_found = False
    # iterate through all parts in formulas and all arguments from each part
    for part in formula.parts:
        part_args = ""
        for arg in part.args:
            if isinstance(arg, TypedObject):
                arg = arg.name
            # handempty: fof file don't recognize empty brackets
            if arg == " ":
                arg = "noargs"
            elif arg == "?x":
                arg = "X"
                x_found = True
            elif arg == "?y":
                arg = "Y"
                y_found = True
            if part_args == "":
                part_args = arg
            else:
                part_args = part_args + "," + arg
        # add entry to list for each part we have one line
        l.append(f"{part.predicate}({part_args})")
    # return list of formulas as well as if generic variables were found (e.g. not objects a,b,c but vars x,y)
    return l, x_found, y_found

def write_formula_to_fof(formula : Condition, type : str, file, counter : int):
    # write one line to tptp-formulas.p
    file.write("fof(formula{}, ".format(counter) + type + ",")
    if isinstance(formula, Conjunction):
        # conjunction joins with &
        # get strings from formulas
        list_formula, x_found, y_found = formula_to_list(formula)
        # needed for generic variables
        if x_found and y_found:
            file.write("![X]: ![Y]:")
        elif x_found:
            file.write("![X]:")
        elif y_found:
            file.write("![Y]:")
        file.write(" & ".join(list_formula) + ").\n")
    elif isinstance(formula, Disjunction):
        # disjunction needs | to join
        list_formula, x_found, y_found = formula_to_list(formula)
        if x_found and y_found:
            file.write("![X]: ![Y]:")
        elif x_found:
            file.write("![X]:")
        elif y_found:
            file.write("![Y]:")
        file.write(" | ".join(list_formula) + ").\n")
    elif isinstance(formula, Atom) or isinstance(formula, NegatedAtom):
        # atom does not need formula conversion
        part_args = ""
        x_found = False
        y_found = False
        if len(formula.args) == 0:
            part_args = "noargs"
        else:
            for arg in formula.args:
                if isinstance(arg, TypedObject):
                    arg = arg.name
                if arg == "?x":
                    arg = "X"
                    x_found = True
                elif arg == "?y":
                    arg = "Y"
                    y_found = True
                if part_args == "":
                    part_args = arg
                else:
                    part_args = part_args + "," + arg
        if x_found and y_found:
            file.write("![X]: ![Y]:")
        elif x_found:
            file.write("![X]:")
        elif y_found:
            file.write("![Y]:")
        if isinstance(formula, Atom):
            # check again if negated or not
            s = f"{formula.predicate}({part_args})).\n"
        else:
            s = f"~{formula.predicate}({part_args})).\n"
        # finally write string/line to file
        file.write(s)


def is_sat(negated_conjecture : Condition, axiom_list : list[Condition]):
    with open("src/translate/tptp-formulas.p", "w") as file:
        counter = 1
        # create for all axioms the tptp file
        for inv_cand in axiom_list:
            if len(inv_cand.parts) == 1:
                write_formula_to_fof(inv_cand.parts[0], "axiom", file, counter)
            else:
                write_formula_to_fof(Disjunction(parts=[inv_cand.parts]))
            counter += 1
        # add formula we want to check to tptp file
        write_formula_to_fof(negated_conjecture, "negated_conjecture", file, 0)
    # run vampire
    result = subprocess.run(['vampire', 'src/translate/tptp-formulas.p'], capture_output=True)
    # return 0 for Satisfiable, else Refutation
    return result.returncode == 0

def handempty_conversion(condition : Condition):
    # since vampire doesn't recognize empty claues, use "noargs" for handempty()
    if isinstance(condition, Conjunction) or isinstance(condition, Disjunction):
        for part in condition.parts:
            if isinstance(part, Conjunction) or isinstance(part, Disjunction):
                return handempty_conversion(part)
            if isinstance(part, Atom) or isinstance(part, NegatedAtom):
                if len(part.args) == 0:
                    part.args = ["noargs"]
    if isinstance(condition, Atom) or isinstance(condition, NegatedAtom):
        if len(condition.args) == 0:
            condition.args = ["noargs"]
    return condition


def parse_objects_with_current_pred(task: Task, task_objects : list[TypedObject], task_pred : Predicate):
    p_should_have_length = 0

    if len(task_pred.arguments) == 2:
        p_should_have_length = len(task_objects) * len(task_objects)
    elif len(task_pred.arguments) == 1:
        p_should_have_length = len(task_objects)
    elif len(task_pred.arguments) == 0:
        p_should_have_length = 1
    count_pred_in_init = 0
    for atom in task.init:
        if atom.predicate == task_pred.name:
            count_pred_in_init += 1
    if count_pred_in_init == p_should_have_length:
        return InvariantCandidate(part=[Atom(predicate=task_pred.name, args=task_pred.arguments)])
    elif count_pred_in_init == 0:
        return InvariantCandidate(part=[NegatedAtom(predicate=task_pred.name, args=task_pred.arguments)])
    else:
        return None



def create_invariant_candidates(task : Task):
    # create simple invariants: all atoms in init are used as invariant candidates
    inv_list = set()
    task_objects = list(task.objects)
    for task_pred in task.predicates:
        inv_cand = parse_objects_with_current_pred(task, task_objects, task_pred)
        if inv_cand is not None:
            inv_list.add(inv_cand)
    return set(inv_list)


def remove_inv_cand(inv_cand_temp_set : set[InvariantCandidate], inv_cand : InvariantCandidate):
    for curr_cand in inv_cand_temp_set:
        if len(inv_cand.parts) == 1 and len(curr_cand.parts) == 1:
            if curr_cand.parts[0].predicate == inv_cand.parts[0].predicate:
                if len(curr_cand.parts[0].args) == 0:
                    if (isinstance(curr_cand.parts[0], Atom) and isinstance(inv_cand.parts[0], Atom)) or (
                            isinstance(curr_cand.parts[0], NegatedAtom) and isinstance(inv_cand.parts[0], Atom)):
                        inv_cand_temp_set.remove(curr_cand)
                        return set(inv_cand_temp_set)
                elif len(curr_cand.parts[0].args) == 1:
                    if curr_cand.parts[0].args[0] == inv_cand.parts[0].args[0]:
                        if (isinstance(curr_cand.parts[0], Atom) and isinstance(inv_cand.parts[0], Atom)) or (
                                isinstance(curr_cand.parts[0], NegatedAtom) and isinstance(inv_cand.parts[0],
                                                                                           Atom)):
                            inv_cand_temp_set.remove(curr_cand)
                            return set(inv_cand_temp_set)
                elif len(curr_cand.parts[0].args) == 2:
                    if (curr_cand.parts[0].args[0] == inv_cand.parts[0].args[0]) and (
                            curr_cand.parts[0].args[1] == inv_cand.parts[0].args[1]):
                        if (isinstance(curr_cand.parts[0], Atom) and isinstance(inv_cand.parts[0], Atom)) or (
                                isinstance(curr_cand.parts[0], NegatedAtom) and isinstance(inv_cand.parts[0],
                                                                                           Atom)):
                            inv_cand_temp_set.remove(curr_cand)
                            return set(inv_cand_temp_set)
        elif len(inv_cand.parts) == 2 and len(curr_cand.parts) == 2:
            print("inv cand is disjunction")
    return set(inv_cand_temp_set)

def remove_and_weaken(inv_cand_temp : InvariantCandidate, task : Task, inv_cand_temp_set : set[InvariantCandidate], action : PropositionalAction):
    print("no invariant")
    print("inv list in where we remove")
    for inv in inv_cand_temp_set:
        inv.dump()
    print("to remove: ")
    inv_cand = invariant_candidate.InvariantCandidate(inv_cand_temp.parts)
    inv_cand.dump()
    # inv candidates X_1 or X_2 == X_2 or X_1 --> im moment wird das nicht als gleich erkannt und daher key error
    # --> wurde behoben --> remove_inv_cand überprüft ob invariant candidate is in set falls ja entferne diesen (sollte zu diesem zeitpunkt im set sein)
    inv_cand_temp_set = remove_inv_cand(set(inv_cand_temp_set), inv_cand)
    # aktion übergeben zu sat test
    # schwächt schematische invarianten ab
    # hier muss geprüft werden ob C wächst, falls nicht --> emptyObject oder so übergeben (da C sonst grösse ändert innerhalb iteration)

    weakened_inv_cand_set = weaken(inv_cand, action)
    print("weaken result: ")
    for weakend_inv_cand in weakened_inv_cand_set:
        if weakend_inv_cand is not None:
            weakend_inv_cand.dump()
            inv_cand_temp_set.add(weakend_inv_cand)
    check_set = set()
    for check_for_none in inv_cand_temp_set:
        if check_for_none is not None:
            check_set.add(check_for_none)
    return set(check_set)




def create_c_sigma(inv_cand:InvariantCandidate, task_objects:list[TypedObject]):
    c_sigma = []
    if len(inv_cand.parts) == 1:
        negated = False
        if isinstance(inv_cand.parts[0], Atom):
            negated = True
        if len(inv_cand.parts[0].args) == 0:
            if negated:
                c_sigma.append(InvariantCandidate(part=[NegatedAtom(predicate=inv_cand.parts[0].predicate, args=[])]))
            else:
                c_sigma.append(InvariantCandidate(part=[Atom(predicate=inv_cand.parts[0].predicate, args=[])]))
        elif len(inv_cand.parts[0].args) == 1:
            for obj in task_objects:
                if negated:
                    c_sigma.append(InvariantCandidate(part=[NegatedAtom(predicate=inv_cand.parts[0].predicate, args=[obj.name])]))
                else:
                    c_sigma.append(InvariantCandidate(part=[Atom(predicate=inv_cand.parts[0].predicate, args=[obj.name])]))
        elif len(inv_cand.parts[0].args) == 2:
            for obj in task_objects:
                for obj2 in task_objects:
                    if negated:
                        c_sigma.append(InvariantCandidate(part=[NegatedAtom(predicate=inv_cand.parts[0].predicate, args=[obj.name, obj2.name])]))
                    else:
                        c_sigma.append(InvariantCandidate(part=[Atom(predicate=inv_cand.parts[0].predicate, args=[obj.name, obj2.name])]))
        return set(c_sigma)
        # TODO: return c sigma: each item in list test in regression and sat test, if any is sat --> then weaken inv cand
    else:
        print("inv cand is disjunction")
        l = set()
        l.add(inv_cand)
        return l

def regr_and_sat(action : PropositionalAction, inv_cand_temp : InvariantCandidate, inv_cand_set_C_0 : set[InvariantCandidate]):
    print("action:")
    action.dump()
    # TODO:
    # hier alle möglichen c instanziierungen (mit unterschiedlichen objekten testen) --> nur wenn mit action ungültig gemacht werden
    #
    print("inv_cand_temp")
    inv_cand_temp.dump()
    input_for_regression = None
    if len(inv_cand_temp.parts) == 1:
        input_for_regression = inv_cand_temp.parts[0]
    else:
        input_for_regression = Disjunction(inv_cand_temp.parts)

    after_reg = regression(input_for_regression.negate(), action).simplified()
    print("after reg:")
    after_reg.dump()
    after_reg_and_conv = handempty_conversion(after_reg)

    return is_sat(after_reg_and_conv, inv_cand_set_C_0)


def get_schematic_invariants(task : Task, actions : list[PropositionalAction]):
    # use deepcopy, so we can modify actions and task freely
    task = copy.deepcopy(task)
    available_objects = []
    for obj in task.objects:
        available_objects.append(obj.name)
    actions = copy.deepcopy(actions)
    inv_cand_set_C = set(create_invariant_candidates(task))
    list_of_possible_actions = []
    # create all possible actions which can be done in the game
    for a in actions:
        x = a.name.split()
        if len(x) > 2:
            y = x[2].split(")")
            if x[1] != y[0]:
                list_of_possible_actions.append(a)

        else:
            list_of_possible_actions.append(a)
    # start algorithm from Rintannen
    while True:
        inv_cand_set_C_0 = set(inv_cand_set_C)
        print("inv_cand_set_C_0")
        for inv_cand in inv_cand_set_C_0:
            inv_cand.dump()
        print("end inv_cand_set_C0 ")
        for action in list_of_possible_actions:
            # kommt in der aktion ein negiertes literal vor welches in c enthalten ist --> kann action überhaupt effekt auf candidates haben
            # if else check
            inv_cand_temp_set = set(inv_cand_set_C)
            for inv_cand in inv_cand_set_C:
                if inv_cand.contains(action):
                    print("c in while loop: ")
                    inv_cand.dump()
                    # return c sigma: each item in list test in regression and sat test, if any is sat --> then weaken inv cand
                    inv_cand_temp_set = create_c_sigma(inv_cand, task.objects)
                    print("created c_temp: ")
                    is_inv_cand_sat = False
                    for inv_cand_temp in inv_cand_temp_set:
                        inv_cand_temp.dump()
                        if regr_and_sat(action, inv_cand_temp, inv_cand_set_C_0):
                            is_inv_cand_sat = True
                            break
                    if is_inv_cand_sat:
                        inv_cand_temp_set = remove_and_weaken(inv_cand_temp, task, set(inv_cand_temp_set), action)
                    else:
                        print("invariant")
                else:
                    print("action has no influence")
            inv_cand_set_C = set(inv_cand_temp_set)
        if inv_cand_set_C == inv_cand_set_C_0:
            # solution found, return
            return inv_cand_set_C
