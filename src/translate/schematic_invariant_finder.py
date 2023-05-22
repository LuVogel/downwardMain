import random
import subprocess
from src.translate.pddl.effects import *
from pddl.conditions import *

def weaken(formula, objects):
    # weaken of form X -> l_1 to X -> l_1 v l_2
    if isinstance(formula, Atom) or isinstance(formula, NegatedAtom):
        if formula.predicate != "handempty" and formula.predicate != "on":
            for obj in objects:
                if formula.args[0] != obj.name:
                    return Disjunction(parts=[formula, Atom(predicate=formula.predicate, args=[obj.name])])
        elif formula.predicate == "handempty":
            return Disjunction(parts=[formula, formula.negate()])
        elif formula.predicate == "on":
            cond_obj1 = formula.args[0]
            while cond_obj1 == formula.args[0]:
                cond_obj1 = random.choice(objects).name
            cond_obj2 = random.choice(objects).name
            while cond_obj2 == cond_obj1:
                cond_obj2 = random.choice(objects).name
            return Disjunction(parts=[formula, Atom(predicate="on", args=[cond_obj1, cond_obj2])])
    # weaken of form X -> l_1 v ... v l_n to X -> l_1 v .. v l_n v l_n+1
    elif isinstance(formula, Disjunction):
        list = []
        for part in formula.parts:
            list.append(part)
        cond = list[0]
        while cond in list:
            cond_pred = random.choice(["on", "handempty", "ontable", "clear", "holding"])
            if cond_pred == "on":
                cond_obj1 = random.choice(objects).name
                cond_obj2 = random.choice(objects).name
                while cond_obj2 == cond_obj1:
                    cond_obj2 = random.choice(objects).name
                cond = Atom(predicate=cond_pred, args=[cond_obj1, cond_obj2])
            elif cond_pred == "handempty":
                cond = Atom(predicate=cond_pred, args=["z"])
            else:
                cond_obj = random.choice(objects).name
                cond = Atom(predicate=cond_pred, args=[cond_obj])
        list.append(cond)
        return Disjunction(list)

def regression(formula, operator):
    eff_list = get_effects_from_action(operator)
    return Conjunction([Conjunction(operator.precondition), regression_rec(formula, Conjunction(eff_list))]).simplified()

def regression_rec(formula, effect):
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


def eff_con(atomic_effect, effect):
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

def get_effects_from_action(operator):
    eff_list = []
    for cond, eff in operator.add_effects:
        if len(cond) == 0:
            eff_list.append(eff)
        else:
            eff_list.append(ConditionalEffect(condition=cond, effect=eff))
    for cond, eff in operator.del_effects:
        if len(cond) == 0:
            eff_list.append(eff.negate())
        else:
            eff_list.append(ConditionalEffect(condition=cond, effect=eff.negate()))
    return eff_list

def formula_to_list(formula):
    l = []
    x_found = False
    y_found = False
    for part in formula.parts:
        part_args = ""
        for arg in part.args:
            # handempty: fof file don't recognize empty brackets
            if arg == " ":
                arg = "z"
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
        l.append(f"{part.predicate}({part_args})")
    return l, x_found, y_found

def write_formula_to_fof(formula, type, file, counter):
    file.write("fof(formula{}, ".format(counter) + type + ",")
    if isinstance(formula, Conjunction):
        list_formula, x_found, y_found = formula_to_list(formula)
        if x_found and y_found:
            file.write("![X]: ![Y]:")
        elif x_found:
            file.write("![X]:")
        elif y_found:
            file.write("![Y]:")
        file.write(" & ".join(list_formula) + ").\n")
    elif isinstance(formula, Disjunction):
        list_formula, x_found, y_found = formula_to_list(formula)
        if x_found and y_found:
            file.write("![X]: ![Y]:")
        elif x_found:
            file.write("![X]:")
        elif y_found:
            file.write("![Y]:")
        file.write(" | ".join(list_formula) + ").\n")
    elif isinstance(formula, Atom) or isinstance(formula, NegatedAtom):
        part_args = ""
        x_found = False
        y_found = False
        for arg in formula.args:
            if arg == " ":
                arg = "z"
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
        if x_found and y_found:
            file.write("![X]: ![Y]:")
        elif x_found:
            file.write("![X]:")
        elif y_found:
            file.write("![Y]:")
        if isinstance(formula, Atom):
            s = f"{formula.predicate}({part_args})).\n"
        else:
            s = f"~{formula.predicate}({part_args})).\n"
        file.write(s)

def is_sat(negated_conjecture, axiom_list):
    with open("src/translate/tptp-formulas.p", "w") as file:
        counter = 1
        for formula in axiom_list:
            write_formula_to_fof(formula, "axiom", file, counter)
            counter += 1
        write_formula_to_fof(negated_conjecture, "negated_conjecture", file, 0)
    result = subprocess.run(['vampire', 'src/translate/tptp-formulas.p'], capture_output=True)
    return result.returncode

def handempty_conversion(x):
    if isinstance(x, Conjunction) or isinstance(x, Disjunction):
        for part in x.parts:
            if isinstance(part, Conjunction) or isinstance(part, Conjunction):
                return handempty_conversion(part)
            if isinstance(part, Atom) or isinstance(part, NegatedAtom):
                if part.predicate == "handempty":
                    part.args = ["z"]
    if isinstance(x, Atom) or isinstance(x, NegatedAtom):
        if x.predicate == "handempty":
            x.args = ["z"]
    return x


def create_invariant_candidates(task):
    inv_list = []
    for a in task.init:
        if a.predicate != "=":
            if a.predicate == "handempty":
                a.args = ["z"]
            inv_list.append(a)
    return inv_list


def get_schematic_invariants(task, actions):
    C = set(create_invariant_candidates(task))
    list_of_possible_actions = []
    for a in actions:
        x = a.name.split()
        if len(x) > 2:
            y = x[2].split(")")
            if x[1] != y[0]:
                list_of_possible_actions.append(a)
        else:
            list_of_possible_actions.append(a)
    while True:
        C_0 = C
        for action in list_of_possible_actions:
            for c in C:
                after_reg = regression(c.negate(), action).simplified()
                after_reg_and_conv = handempty_conversion(after_reg)
                satTest = is_sat(after_reg_and_conv, C_0)
                if satTest == 0:
                    C.remove(c)
                    C.add(weaken(c, task.objects))
        if C == C_0:
            return C
