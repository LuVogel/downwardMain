import copy
import random
import subprocess

from src.translate.pddl.effects import *
from pddl.conditions import *
import invariant_candidate
from invariant_candidate import *
def weaken(formula, objects):
    # weaken of form X -> l_1 to X -> l_1 v l_2
    print("inside weaken, formula: type: ")
    print(type(formula))
    if isinstance(formula, Atom) or isinstance(formula, NegatedAtom):
        # handempty has no argument and on has two arguments --> the rest has exactly one argument
        if formula.predicate != "handempty" and formula.predicate != "on":
            for obj in objects:
                if formula.args[0] != obj.name:
                    # if object found which is not arg of formula e.g. ontable(d) and c found, return ontable(d) v ontable(c)
                    return Disjunction(parts=[formula, Atom(predicate=formula.predicate, args=[obj.name])])
        elif formula.predicate == "handempty":
            # if handempty, just negate
            return Disjunction(parts=[formula, formula.negate()])
        elif formula.predicate == "on":
            # if on: e.g. on(x,y) search z where x != z, and then search u where u != z and return on(u,z)
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
        # start with a condition (Atom) which is in formula
        cond = list[0]
        # as long as condition is in list
        while cond in list:
            # choose random predicate
            cond_pred = random.choice(["on", "handempty", "ontable", "clear", "holding"])
            # if on was choosen, chose two random objects (on(x,y)) with x != y and set this to cond
            if cond_pred == "on":
                cond_obj1 = random.choice(objects).name
                cond_obj2 = random.choice(objects).name
                while cond_obj2 == cond_obj1:
                    cond_obj2 = random.choice(objects).name
                cond = Atom(predicate=cond_pred, args=[cond_obj1, cond_obj2])
            # if handempty, create new atom handempty
            elif cond_pred == "handempty":
                cond = Atom(predicate=cond_pred, args=["noargs"])
            else:
                # in other cases, create cond with random object
                cond_obj = random.choice(objects).name
                cond = Atom(predicate=cond_pred, args=[cond_obj])
        # if we land here, that means we created an new Atom which wasn't already in the formula.
        # therefore add it to list and return a disjunction (formula = x1 v...v xn) return x1 v...v xn v cond
        list.append(cond)
        return Disjunction(list)

def regression(formula, operator):
    # eff_list = eff(o)
    eff_list = get_effects_from_action(operator)
    # start recursive call
    for pre in operator.precondition:
        handempty_conversion(pre)
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


def formula_to_list(formula):

    l = []
    x_found = False
    y_found = False
    # iterate through all parts in formulas and all arguments from each part
    for part in formula.parts:
        part_args = ""
        for arg in part.args:
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

def write_formula_to_fof(formula, type, file, counter):
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
        for arg in formula.args:
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

def is_sat(negated_conjecture, axiom_list):
    with open("src/translate/tptp-formulas.p", "w") as file:
        counter = 1
        # create for all axioms the tptp file
        for formula in axiom_list:
            write_formula_to_fof(formula.part, "axiom", file, counter)
            counter += 1
        # add formula we want to check to tptp file
        write_formula_to_fof(negated_conjecture, "negated_conjecture", file, 0)
    # run vampire
    result = subprocess.run(['vampire', 'src/translate/tptp-formulas.p'], capture_output=True)
    # return 0 for Satisfiable, else Refutation
    return result.returncode == 0

def handempty_conversion(x):
    # since vampire doesn't recognize empty claues, use "noargs" for handempty()
    if isinstance(x, Conjunction) or isinstance(x, Disjunction):
        for part in x.parts:
            if isinstance(part, Conjunction) or isinstance(part, Disjunction):
                return handempty_conversion(part)
            if isinstance(part, Atom) or isinstance(part, NegatedAtom):
                if part.predicate == "handempty":
                    part.args = ["noargs"]
    if isinstance(x, Atom) or isinstance(x, NegatedAtom):
        if x.predicate == "handempty":
            x.args = ["noargs"]
    return x


def create_invariant_candidates(task):
    # create simple invariants: all atoms in init are used as invariant candidates
    inv_list = set()
    for a in task.init:
        if a.predicate != "=":
            # TODO ersetzen hier drin machen (vari und objekte)
            inv_list.add(invariant_candidate.InvariantCandidate([a]))
            # if a.predicate == "handempty":
            #     a.args = ["noargs"]
            #     inv_list.append(a)
    return set(inv_list)


def runAlgorithm(action, c, C_0, C, task, temp_c_list):
    print("action:")
    action.dump()
    # TODO:
    # hier alle möglichen c instanziierungen (mit unterschiedlichen objekten testen) --> nur wenn mit action ungültig gemacht werden
    #
    print("c")
    c.dump()

    after_reg = regression(c.negate(), action).simplified()
    print("after reg:")
    print("first c, then reg: ")
    c.dump()
    after_reg.dump()
    after_reg_and_conv = handempty_conversion(after_reg)

    sat_test = is_sat(after_reg_and_conv, C_0)
    if sat_test:
        print("no invariant")
        print("inv list in where we remove")
        for inv in temp_c_list:
            inv.dump()
        print("to remove: ")
        invcand = invariant_candidate.InvariantCandidate([c])
        invcand.dump()
        # TODO: inv candidates X_1 or X_2 == X_2 or X_1 --> im moment wird das nicht als gleich erkannt und daher key error
        temp_c_list.remove(invcand)
        # aktion übergeben zu sat test
        # schwächt schematische invarianten ab
        # TODO:
        # hier muss geprüft werden ob C wächst, falls nicht --> emptyObject oder so übergeben (da C sonst grösse ändert innerhalb iteration)
        x = weaken(c, task.objects)
        print("weaken result: ")
        x.dump()

        temp_c_list.add(invariant_candidate.InvariantCandidate([x]))
    else:
        print("invariant")



def create_c_temp(c, available_objects):
    if isinstance(c, InvariantCandidate):
        return create_c_temp(c.parts, available_objects)
    else:
        if isinstance(c, Atom) or isinstance(c, NegatedAtom):
            if len(c.args) == 0:
                return c
            elif len(c.args) == 1:
                for obj1 in available_objects:
                    if c.args[0] == "?x" or c.args[0] == "?y":
                        if isinstance(c, Atom):
                            return Atom(predicate=c.predicate, args=[obj1])
                        else:
                            return NegatedAtom(predicate=c.predicate, args=[obj1])
            elif len(c.args) == 2:
                for obj1 in available_objects:
                    for obj2 in available_objects:
                        if obj1 != obj2:
                            if c.args[0] == "?x" and c.args[1] == "?y":
                                if isinstance(c, Atom):
                                    return Atom(predicate=c.predicate, args=[obj1, obj2])
                                else:
                                    return NegatedAtom(predicate=c.predicate, args=[obj1, obj2])
        elif isinstance(c, Disjunction) or isinstance((c, Conjunction)):
            part_list = set()
            for part in c.parts:
                part_list.add(create_c_temp(part, available_objects))
            if isinstance(c, Disjunction):
                return Disjunction(part_list)
            else:
                return Conjunction(part_list)

def get_schematic_invariants(task, actions):
    # use deepcopy, so we can modify actions and task freely
    task = copy.deepcopy(task)
    available_objects = []
    for obj in task.objects:
        available_objects.append(obj.name)
    actions = copy.deepcopy(actions)
    C = set(create_invariant_candidates(task))
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
        C_0 = set(C)
        print("C")
        for part in C_0:
            part.dump()
        print("end c ")
        for action in list_of_possible_actions:
            # TODO:
            # kommt in der aktion ein negiertes literal vor welches in c enthalten ist --> kann action überhaupt effekt auf candidates haben
            # if else check
            temp_c_list = set(C)
            for c in C:
                if c.contains(action):
                    print("c in while loop: ")
                    c.dump()
                    c_temp = create_c_temp(c, available_objects)
                    print("created c_temp: ")
                    c_temp.dump()
                    runAlgorithm(action, c_temp, C_0, C, task, temp_c_list)
                else:
                    print("action has no influence")
            C = set(temp_c_list)
        if C == C_0:
            # solution found, return
            return C
