import random
import subprocess
from src.translate.pddl.effects import *
from pddl.conditions import *

# ist keine action sondern state-variable --> oder doch effects? 2 Definitions 1. a and not a for state variables a in A are effects?
def negate_state_var(operator):
    return operator

# weaken: return {c \lor a | a \in A} U {c \lor \lnot a | a \in A}

def weaken(c, action):
    eff = get_effects_from_action(action)
    union = []
    for e in eff:
        union.append(Disjunction([c, e]))
        union.append(Disjunction([c, e.negate()]))
    return list(set(union))




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


# TODO: condition weiter behalten und in liste hinzufügen --> falls cond nicht leer dann conditional effect sonst normaler effect
# --> somit kann auch oben mit isinstance(effect, ConditionalEffect) geprüft werden.
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


def regression(formula, operator):
    eff_list = get_effects_from_action(operator)
    return Conjunction([Conjunction(operator.precondition), regression_rec(formula, Conjunction(eff_list))]).simplified()



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
                arg = "ö"
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


def junctor_to_list(formula):
    l = []
    x_found = False
    y_found = False
    for part in formula.parts:
        list = []
        if isinstance(part, Conjunction):
            part_type = "conj"
        elif isinstance(part, Disjunction):
            part_type = "disj"
        elif isinstance(part, Atom):
            part_type = "atom"
            part_args = ""
            for arg in part.args:
                if arg == " ":
                    arg = "ö"
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
            list.append(f"{part.predicate}({part_args})")
        elif isinstance(part, NegatedAtom):
            part_type = "negatom"
            part_args = ""
            for arg in part.args:
                if arg == " ":
                    arg = "ö"
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
            list.append(f"~ {part.predicate}({part_args})")
        if not isinstance(part, Atom) and not isinstance(part, NegatedAtom):
            for p in part.parts:
                neg = False
                if isinstance(p, NegatedAtom):
                    neg = True
                part_args = ""
                for arg in p.args:
                    if arg == " ":
                        arg = "ö"
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
                if neg:
                    list.append(f"~ {p.predicate}({part_args})")
                else:
                    list.append(f"{p.predicate}({part_args})")
        l.append((list, part_type, x_found, y_found))
    return l


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
    elif isinstance(formula, JunctorCondition):
        list_formula = junctor_to_list(formula)
        part_to_write = ""
        counter = 0
        tx_found = False
        ty_found = False
        for list, part_type, x_found, y_found in list_formula:
            if part_type == "conj":
                part_to_write += " & ".join(list)
            elif part_type == "disj":
                 part_to_write += " | ".join(list)
            else:
                part_to_write += "".join(list)
            if counter == 0:
                part_to_write += " => "
            else:
                part_to_write += ").\n"
            counter += 1
            if x_found:
                tx_found = True
            if y_found:
                ty_found = True
        if tx_found and ty_found:
            file.write("![X]: ![Y]:")
        elif tx_found:
            file.write("![X]:")
        elif ty_found:
            file.write("![Y]:")
        file.write(part_to_write)
    elif isinstance(formula, Atom):
        part_args = ""
        x_found = False
        y_found = False
        for arg in formula.args:
            if arg == " ":
                arg = "ö"
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
                arg = "ö"
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
        s = f"~ {formula.predicate}({part_args})).\n"
        file.write(s)
def is_sat(temp_union, axiom_list):
    with open("src/translate/tptp-formulas.p", "w") as file:
        counter = 1
        for formula in axiom_list:
            write_formula_to_fof(formula, "axiom", file, counter)
            counter += 1
        #union_as_formula = Conjunction([temp_union])
        write_formula_to_fof(temp_union, "conjecture", file, 0)

    result = subprocess.run(['vampire', 'src/translate/tptp-formulas.p'], capture_output=True)
    print(result.stdout.decode())
    return result.returncode


def create_invariant_candidates(task):
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
            inv_list.append(Atom(predicate=name, args=[]))
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
    return inv_list + temp_inv_list


def create_union(C_0, x):
    print(type(C_0), " type c0")
    print(type(x), " type x")
    x_list = []
    for part in x.parts:
        x_list.append(part)
    union_list = C_0.union(set(x_list))

    return Conjunction(union_list)



def get_schematic_invariants(relaxed_reachable, atoms, actions, goal_list, axioms,
                             reachable_action_params, task):
    # print("relaxed reachable: ", relaxed_reachable)
    # print("atoms: ", atoms)
    # print("actions: ", actions)
    # print("goal_list: ", goal_list)
    # print("axioms: ", axioms)
    # print("reachable_action_params: ", reachable_action_params)
    # print("task: ", task)
    # print("task_pred: ")
    # for pred in task.predicates:
    #     print(pred)
    # print("task_objects: ", task.objects)
    print("invariant candidates start: ")
    invariant_candidates = set(create_invariant_candidates(task))
    # for inv in invariant_candidates:
    #     if isinstance(inv, Disjunction):
    #         inv.dump()
    #     else:
    #         print(inv)
    # print("invariant candidates end.")
    #invariant candidates:
    # [<Atom on(b, ?x)>, <Atom holding(d)>, <Atom on(?y, b)>, <Atom on(d, ?y)>, <Atom on(a, ?y)>, <Atom clear(d)>,
    # <Atom ontable(b)>, <Atom ontable(?x)>, <Atom on(d, a)>, <Atom holding(c)>, <Atom on(b, d)>, <Atom clear(c)>,
    # <Atom handempty()>, <Atom on(?y, d)>, <Atom on(b, c)>, <Atom ontable(d)>, <Atom on(?x, a)>, <Atom on(c, ?y)>,
    # <Atom on(?y, c)>, <Atom on(c, a)>, <Atom holding(a)>, <Atom on(a, ?x)>, <Atom on(c, ?x)>, <Atom on(d, b)>,
    # <Atom on(d, ?x)>, <Atom clear(a)>, <Atom on(b, ?y)>, <Atom ontable(c)>, <Atom on(?x, d)>, <Atom on(?x, b)>,
    # <Atom on(?y, a)>, <Atom on(a, d)>, <Atom on(c, d)>, <Atom on(a, b)>, <Atom on(c, b)>, <Atom holding(b)>,
    # <Atom holding(?x)>, <Atom on(?x, c)>, <Atom ontable(a)>, <Atom clear(b)>, <Atom on(a, c)>, <Atom clear(?x)>,
    # <Atom on(d, c)>, <Atom on(b, a)>]
    temp = 0
    action_temp = None
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
        if temp == 0:
            action_temp = a
            temp = 1
    #     if temp == 11:
    #         action_temp = a
    #     temp += 1
    a = Atom(predicate="on", args=["a", "b"])
    b = Atom(predicate="on", args=["b", "c"])
    c = Atom(predicate="clear", args=["a"])
    d = Atom(predicate="clear", args=["b"])
    conj1 = Conjunction([a, b])
    conj2 = Conjunction([c.negate(), d.negate()])
    conj2notnegated = Conjunction([c, d])
    conj3fortest2 = JunctorCondition([conj1, conj2notnegated])
    conj3 = JunctorCondition([conj1, conj2])
    axiom1_1 = Atom(predicate="on", args=["?x", "?y"])
    axiom1_2 = Atom(predicate="ontable", args=["?x"])
    axiom1_3 = Atom(predicate="holding", args=["?x"])
    conjAxiom1 = Disjunction([axiom1_1, axiom1_2, axiom1_3])

    axiom2_1 = Atom(predicate="clear", args=["?x"])
    junctorAxiom2 = JunctorCondition([axiom1_1, axiom2_1.negate()])
    axiom3 = Atom(predicate="on", args=["?x", "?x"]).negate()
    disAxiom4= Disjunction([axiom2_1, axiom1_1])
    junctorAxiom4 = JunctorCondition([axiom1_2, disAxiom4])


    axiom_list = [conjAxiom1, junctorAxiom2, axiom3, junctorAxiom4]
    test_sat_true = is_sat(conj3, axiom_list)
    test_sat_false = is_sat(conj3fortest2, axiom_list)
    print("first try: true if 0: ", test_sat_true)
    print("second try: false if 1: ", test_sat_false)
    print("end test sat")
    return
    #print(list_of_possible_actions)

    #conj = Conjunction([a, b])
    # z = regression(b.negate(), action_temp).simplified()
    # print("after regression: ")
    # z.dump()

    while True:
        C_0 = invariant_candidates
        for action in list_of_possible_actions:
            # TODO: \lnot c\sigma --> im moment wird nur C.part[i].negate() genommen
            for c in invariant_candidates:
                print("starting regression with: ")
                c.negate().dump()
                print("and action: ")
                action.dump()
                x = regression(c.negate(), action).simplified()
                print("after regression in while loop")
                x.dump()
                temp_union = create_union(C_0, x)
                print("temp_union: ")
                temp_union.dump()
                # TODO: is_sat --> im moment wird True zurück gegeben
                # könnte z.b mit pycosat gemacht werden (sat-solver), dann muss jedoch formula umgeformt werden
                # eigenen sat solver implementieren
                if is_sat(temp_union):
                    # TODO: Test weaken?
                    invariant_candidates.remove(c)
                    invariant_candidates = set(invariant_candidates + weaken(c, action))
                # TODO: since isSat always true: invariant candidates gets bigger each iteration,
                #  and therefore endless loop for c in invariant_candidates
                break
        print("check...")
        if invariant_candidates == C_0:
            print("return")
            return invariant_candidates

