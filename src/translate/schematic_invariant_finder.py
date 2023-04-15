import copy
import itertools
from src.translate.pddl.effects import *
from src.translate.pddl.actions import *
from src.translate.pddl.axioms import *
from src.translate.pddl.conditions import *

from src.translate import pddl



def weaken(formula, operator):
    eff_list1 = [formula]
    eff_list2 = [formula]
    for con, eff in operator.add_effects:
        eff_list1.append(eff)
        eff_list2.append(eff.negate)
    for con, eff in operator.del_effects:
        eff_list1.append(eff.negate)
        eff_list2.append(eff)
    first = Conjunction(eff_list1)
    second = Conjunction(eff_list2)
    formula = Union(formula, first, second)
    return formula


def regression_rec(formula, effect):
    if isinstance(formula, Truth):
        return Truth()
    if isinstance(formula, Falsity):
        return Falsity()
    if isinstance(formula, NegatedAtom):
        return regression_rec(NegatedAtom.negate(Literal(formula)), effect)
    if isinstance(formula, Disjunction):
        return Disjunction([regression_rec(formula.parts[0], effect), regression_rec(formula.parts[1], effect)])
    if isinstance(formula, Conjunction):
        return Conjunction([regression_rec(formula.parts[0], effect), regression_rec(formula.parts[1], effect)])
    return Disjunction([eff_con(formula, effect), Conjunction([formula, eff_con(formula.negate(), effect).negate()])])


def eff_con(formula, effect):
    if isinstance(effect, Truth):
        return Falsity()
    if isinstance(effect, Conjunction):
        eff_con_list = []
        for part in effect.parts:
            eff_con_list.append(eff_con(formula, part))
        return Disjunction(eff_con_list)
    if isinstance(effect, ConditionalEffect):
        return Conjunction([effect.condition, eff_con(formula, effect.effect)])
    if formula.__eq__(effect):
        return Truth()
    return Falsity()


def regression(formula, operator):
    operator.dump()
    eff_list = []
    for cond, eff in operator.add_effects:
        eff_list.append(eff)
    for cond, eff in operator.del_effects:
        eff_list.append(eff.negate())
    return Conjunction([Conjunction(operator.precondition), regression_rec(formula, Conjunction(eff_list))])



# add after delete (für <a, (c |> d) and not d) in folie b02 s16
# regr(q,o) ->_o q
# [e]_s consistent effectbedingung
# task anpassen (verkleinern, dann exlplore für grounding)
# for instance in c = c\sigma
# visitor pattern s


def get_schematic_invariants(relaxed_reachable, atoms, actions, goal_list, axioms,
                             reachable_action_params):
    print("\n1. relaxed_reachable\n", relaxed_reachable)
    temp = 0
    formula = None
    for a in atoms:
        if temp == 2:
            formula = a
        if temp == 15:
            formula = Conjunction([a, formula])
        temp += 1
    temp = 0
    action_temp = None
    for a in actions:
        if temp == 11:
            action_temp = a
        temp += 1
    print("\n4. goal_list\n", goal_list)
    print("\n5. axioms\n", axioms)
    print("\n6. reachable_action_params\n", reachable_action_params)
    print("\n\n")



    z = regression(formula, action_temp)
    print("after regression: ")
    z.dump()
