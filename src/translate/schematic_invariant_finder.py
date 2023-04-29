from src.translate.pddl.effects import *
from pddl.conditions import *

# ist keine action sondern state-variable --> oder doch effects? 2 Definitions 1. a and not a for state variables a in A are effects?
def negate_state_var(operator):
    return operator

# weaken: return {c \lor a | a \in A} U {c \lor \lnot a | a \in A}

def weaken(C, formula, predicates):
    dis1 = [formula]
    dis2 = [formula]
    for pred in predicates:
        dis1.append(pred)
        dis2.append(pred.negate())
    return set([C, Disjunction(dis1), Disjunction(dis2)])


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
def regression(formula, operator):
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
            eff_list.append(ConditionalEffect(condition=cond, effect=eff))
    return Conjunction([Conjunction(operator.precondition), regression_rec(formula, Conjunction(eff_list))]).simplified()



# add after delete (für <a, (c |> d) and not d) in folie b02 s16
# regr(q,o) ->_o q
# [e]_s consistent effectbedingung
# task anpassen (verkleinern, dann exlplore für grounding)
# for instance in c = c\sigma
# visitor pattern s

# bei grosse Conjunction: for parts in Conjunction.parts --> regr(not parts, action)
# bei Liste: for form in list: --> regr(not form, action)
def is_sat(temp_union):
    return True


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
    print(name_arg_list)
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
    return inv_list


def create_union(C_0, x):
    x_list = []
    for part in x.parts:
        x_list.append(part)
    union_list = list(set(C_0 + x_list))
    return Conjunction(union_list)



def get_schematic_invariants(relaxed_reachable, atoms, actions, goal_list, axioms,
                             reachable_action_params, task):
    print("relaxed reachable: ", relaxed_reachable)
    print("atoms: ", atoms)
    print("actions: ", actions)
    print("goal_list: ", goal_list)
    print("axioms: ", axioms)
    print("reachable_action_params: ", reachable_action_params)
    print("task: ", task)
    print("task_pred: ")
    for pred in task.predicates:
        print(pred)
    print("task_objects: ", task.objects)
    invariant_candidates = list(set(create_invariant_candidates(task)))
    #print(invariant_candidates)
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
    a = Atom(predicate="on", args=["a", "d"])
    b = Atom(predicate="on", args=["d", "c"])

    #print(list_of_possible_actions)

    #conj = Conjunction([a, b])
    z = regression(b.negate(), action_temp).simplified()
    print("after regression: ")
    z.dump()

    while True:
        C_0 = invariant_candidates
        for action in list_of_possible_actions:
            # TODO: \lnot c\sigma --> im moment wird nur C.part[i].negate() genommen
            for c in invariant_candidates:
                #print("starting regression with: ", c.negate(), "and action: ", action)
                x = regression(c.negate(), action).simplified()
                # print("after regression in while loop")
                # x.dump()
                temp_union = create_union(C_0, x)
                # print("temp_union: ")
                # temp_union.dump()
                # TODO: is_sat --> im moment wird True zurück gegeben
                # könnte z.b mit pycosat gemacht werden (sat-solver), dann muss jedoch formula umgeformt werden
                # eigenen sat solver implementieren
                if is_sat(temp_union):
                    # TODO: Test weaken?
                    C = weaken(C, c, task_predicates)

        return

