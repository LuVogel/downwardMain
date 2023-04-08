import copy
import itertools
from src.translate.pddl.effects import *
from src.translate.pddl.actions import *
from src.translate.pddl.axioms import *
from src.translate.pddl.conditions import *

from src.translate import pddl


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
    x = Atom.negate(formula)
    y = eff_con(x, effect[0][1])
    z = None
    if isinstance(y, Truth):
        z = Falsity()
    elif isinstance(y, Falsity):
        z = Truth()
    else:
        z = Atom.negate(y)
    return Disjunction([eff_con(formula, effect), Conjunction(formula, z)])


def eff_con(formula, effect):
    if isinstance(effect, Truth):
        return Falsity()
    if isinstance(effect, Conjunction):
        return Disjunction([eff_con(formula, effect.parts[0]), eff_con(formula, effect.parts[1])])
    if isinstance(effect, ConditionalEffect):
        return Conjunction([effect.parts[0], eff_con(formula, effect.parts[1])])
    if formula.__eq__(effect):
        return Truth()
    return Falsity()


def regression(formula, operator):
    operator.precondition.dump()
    print("\nop.add_eff: ", operator.add_effects, "\n")

    return Conjunction([operator.precondition, regression_rec(formula, operator.add_effects)])


# add after delete (für <a, (c |> d) and not d) in folie b02 s16
# regr(q,o) ->_o q
# [e]_s consistent effectbedingung
# task anpassen (verkleinern, dann exlplore für grounding)
# for instance in c = c\sigma
# visitor pattern s


def get_schematic_invariants(relaxed_reachable, atoms, actions, goal_list, axioms,
                             reachable_action_params):
    print("\n1. relaxed_reachable\n", relaxed_reachable)
    print("\n2. atoms:\n ", atoms)
    print("\n3. actions\n", actions)
    print("\n4. goal_list\n", goal_list)
    print("\n5. axioms\n", axioms)
    print("\n6. reachable_action_params\n", reachable_action_params)
    print("\n\n")
    A = Atom("A", [])
    B = Atom("B", [])
    C = Atom("C", [])


    action_temp = PropositionalAction(name="test", precondition=A, effects=[(B,)], cost=1)
    z = regression(B, action_temp)
    print("after regression: ")
    z.dump()
