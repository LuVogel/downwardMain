import random
import subprocess
from src.translate.pddl.effects import *
from pddl.conditions import *



# weaken: return {c \lor a | a \in A} U {c \lor \lnot a | a \in A}

def weaken(formula, objects):
    # print("try to weaken : ")
    # formula.dump()
    # weaken of form X -> l_1 to X -> l_1 v l_2
    if isinstance(formula, Atom) or isinstance(formula, NegatedAtom):
        if formula.predicate != "handempty" and formula.predicate != "on":
            list = []
            for obj in objects:
                if formula.args[0] != obj.name:
                    list.append(obj.name)
                    x = Disjunction(parts=[formula, Atom(predicate=formula.predicate, args=[obj.name])])
                    # print("after weaken: ")
                    # x.dump()
                    return x
        elif formula.predicate == "handempty":
            x = Disjunction(parts=[formula, formula.negate()])
            # print("after weaken: ")
            # x.dump()
            return x
        elif formula.predicate == "on":
            cond_obj1 = formula.args[0]
            while cond_obj1 == formula.args[0]:
                cond_obj1 = random.choice(objects).name
            cond_obj2 = random.choice(objects).name
            while cond_obj2 == cond_obj1:
                cond_obj2 = random.choice(objects).name
            x = Disjunction(parts=[formula, Atom(predicate="on", args=[cond_obj1, cond_obj2])])
            # print("after weaken: ")
            # x.dump()
            return x
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
        x = Disjunction(list)
        # print("after weaken: ")
        # x.dump()
        return x

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






# add after delete (für <a, (c |> d) and not d) in folie b02 s16
# regr(q,o) ->_o q
# [e]_s consistent effectbedingung
# task anpassen (verkleinern, dann exlplore für grounding)
# for instance in c = c\sigma
# visitor pattern s

# bei grosse Conjunction: for parts in Conjunction.parts --> regr(not parts, action)
# bei Liste: for form in list: --> regr(not form, action)
def formula_to_list(formula):
    l = []
    x_found = False
    y_found = False
    for part in formula.parts:
        part_args = ""
        for arg in part.args:
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
    return (l, x_found, y_found)


# def junctor_to_list(formula):
#     print("junctor needed")
#     l = []
#     x_found = False
#     y_found = False
#     for part in formula.parts:
#         list = []
#         if isinstance(part, Conjunction):
#             part_type = "conj"
#         elif isinstance(part, Disjunction):
#             part_type = "disj"
#         elif isinstance(part, Atom):
#             part_type = "atom"
#             part_args = ""
#             for arg in part.args:
#                 if arg == " ":
#                     arg = "z"
#                 elif arg == "?x":
#                     arg = "X"
#                     x_found = True
#                 elif arg == "?y":
#                     arg = "Y"
#                     y_found = True
#                 if part_args == "":
#                     part_args = arg
#                 else:
#                     part_args = part_args + "," + arg
#             list.append(f"{part.predicate}({part_args})")
#         elif isinstance(part, NegatedAtom):
#             part_type = "negatom"
#             part_args = ""
#             for arg in part.args:
#                 if arg == " ":
#                     arg = "z"
#                 elif arg == "?x":
#                     arg = "X"
#                     x_found = True
#                 elif arg == "?y":
#                     arg = "Y"
#                     y_found = True
#                 if part_args == "":
#                     part_args = arg
#                 else:
#                     part_args = part_args + "," + arg
#             list.append(f"~{part.predicate}({part_args})")
#         if not isinstance(part, Atom) and not isinstance(part, NegatedAtom):
#             for p in part.parts:
#                 neg = False
#                 if isinstance(p, NegatedAtom):
#                     neg = True
#                 part_args = ""
#                 for arg in p.args:
#                     if arg == " ":
#                         arg = "z"
#                     elif arg == "?x":
#                         arg = "X"
#                         x_found = True
#                     elif arg == "?y":
#                         arg = "Y"
#                         y_found = True
#                     if part_args == "":
#                         part_args = arg
#                     else:
#                         part_args = part_args + "," + arg
#                 if neg:
#                     list.append(f"~{p.predicate}({part_args})")
#                 else:
#                     list.append(f"{p.predicate}({part_args})")
#         l.append((list, part_type, x_found, y_found))
#     return l


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
    # elif isinstance(formula, JunctorCondition):
    #     list_formula = junctor_to_list(formula)
    #     part_to_write = ""
    #     counter = 0
    #     tx_found = False
    #     ty_found = False
    #     for list, part_type, x_found, y_found in list_formula:
    #         if part_type == "conj":
    #             part_to_write += " & ".join(list)
    #         elif part_type == "disj":
    #              part_to_write += " | ".join(list)
    #         else:
    #             part_to_write += "".join(list)
    #         if counter == 0:
    #             part_to_write += " => "
    #         else:
    #             part_to_write += ").\n"
    #         counter += 1
    #         if x_found:
    #             tx_found = True
    #         if y_found:
    #             ty_found = True
    #     if tx_found and ty_found:
    #         file.write("![X]: ![Y]:")
    #     elif tx_found:
    #         file.write("![X]:")
    #     elif ty_found:
    #         file.write("![Y]:")
    #     file.write(part_to_write)
    elif isinstance(formula, Atom):
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
        s = f"{formula.predicate}({part_args})).\n"
        file.write(s)
    elif isinstance(formula, NegatedAtom):
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


def create_invariant_candidates1(task):
    inv_list = []
    name_arg_list = []
    for pred in task.predicates:
        if pred.name != "=":
            arg_list = []
            for arg in pred.arguments:
                arg_list.append(arg.name)
            name_arg_list.append((pred.name, arg_list))
    obj_list = []
    for obj in task.objects:
        obj_list.append(obj.name)
    for (name, args) in name_arg_list:
        if len(args) == 0:
            inv_list.append(Atom(predicate=name, args=["z"]))
        elif len(args) == 1:
            inv_list.append(Atom(predicate=name, args=[args[0]]))
            for obj in obj_list:
                inv_list.append(Atom(predicate=name, args=obj))
        else:
            for obj in obj_list:
                for arg in args:
                    inv_list.append(Atom(predicate=name, args=[obj, arg]))
                    inv_list.append(Atom(predicate=name, args=[arg, obj]))
                    for arg1 in args:
                        if arg != arg:
                            inv_list.append(Atom(predicate=name, args=[arg, arg1]))
                            inv_list.append(Atom(predicate=name, args=[arg1, arg]))
                for obj1 in obj_list:
                    if obj != obj1:
                        inv_list.append(Atom(predicate=name, args=[obj1, obj]))
                        inv_list.append(Atom(predicate=name, args=[obj, obj1]))
    # TODO: X -> l_1 \lor l_2 richtig?
    temp_inv_list = []
    for inv in inv_list:
        for inv1 in inv_list:
            if inv != inv1:
                temp_inv_list.append(Disjunction([inv, inv1]))
    return inv_list


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
    invariant_candidates = set(create_invariant_candidates(task))
    # for inv in invariant_candidates:
    #      if isinstance(inv, Disjunction):
    #          inv.dump()
    #      else:
    #          print(inv)

    # contains all possible actions (not depending on inital state)
    list_of_possible_actions = []
    for a in actions:
        x = a.name.split()
        if len(x) > 2:
            y = x[2].split(")")
            if x[1] != y[0]:
                list_of_possible_actions.append(a)
        else:
            list_of_possible_actions.append(a)
    # a = Atom(predicate="on", args=["a", "b"])
    # b = Atom(predicate="on", args=["b", "c"])
    # c = Atom(predicate="clear", args=["a"])
    # d = Atom(predicate="clear", args=["b"])
    # conj1 = Conjunction([a, b])
    # conj2 = Conjunction([c, d.negate()])
    # conj2notnegated = Conjunction([c.negate(), d])
    # conj3fortest2 = JunctorCondition([conj1, conj2notnegated])
    # conj3 = JunctorCondition([conj1, conj2])
    # # nicht junctro
    # axiom1_1 = Atom(predicate="on", args=["?x", "?y"])
    # axiom_on_y_x = Atom(predicate="on", args=["?y", "?x"])
    # axiom1_2 = Atom(predicate="ontable", args=["?x"])
    # axiom1_3 = Atom(predicate="holding", args=["?x"])
    # conjAxiom1 = Disjunction([axiom1_1, axiom1_2, axiom1_3])
    #
    # axiom2_1 = Atom(predicate="clear", args=["?x"])
    # axiom2_2 = Atom(predicate="clear", args=["?y"])
    #
    # junctorAxiom2 = JunctorCondition([axiom1_1, axiom2_2.negate()])
    # axiom3 = Atom(predicate="on", args=["?x", "?x"]).negate()
    # disAxiom4= Disjunction([axiom2_1, axiom_on_y_x])
    # junctorAxiom4 = JunctorCondition([axiom1_2, disAxiom4])
    #
    #
    # axiom_list = [conjAxiom1, junctorAxiom2, axiom3, junctorAxiom4]
    # test_sat_true = is_sat(conj3, axiom_list)
    # test_sat_false = is_sat(conj3fortest2, axiom_list)
    # print("first try: true if 0: ", test_sat_true)
    # print("second try: false if 1: ", test_sat_false)
    # print("end test sat")
    # return
    #print(list_of_possible_actions)

    #conj = Conjunction([a, b])
    # z = regression(b.negate(), action_temp).simplified()
    # print("after regression: ")
    # z.dump()
    C = invariant_candidates
    while True:
        C_0 = C
        for action in list_of_possible_actions:
            for c in C:
                # print("starting regression with: ")
                # c.negate().dump()
                # print("and action: ")
                # action.dump()
                x = regression(c.negate(), action).simplified()
                # print("after regression in while loop")
                # x.dump()
                x = handempty_conversion(x)
                satTest = is_sat(x, C_0)
                if satTest == 0:
                    C.remove(c)
                    C.add(weaken(c, task.objects))
        # print("check...")
        if C == C_0:
            # print("return")
            # for check in C:
            #     print(check)
            #     check.dump()
            return C

