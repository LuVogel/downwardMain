import copy
import itertools
from src.translate.pddl.effects import *
from src.translate.pddl.actions import *
from src.translate.pddl.axioms import *
from src.translate.pddl.conditions import *

from src.translate import pddl


def regression_rec(formula, effect, negated=False):
    if type(formula) is bool:
        if negated:
            if formula:
                return False
            else:
                return True
        else:
            return formula
    if isinstance(formula, NegatedAtom):
        return regression_rec(NegatedAtom.negate(Literal(formula)), effect, negated=True)
    if isinstance(formula, Disjunction):
        return Disjunction([regression_rec(formula.parts[0], effect), regression_rec(formula.parts[1], effect)])
    if isinstance(formula, Conjunction):
        return Conjunction([regression_rec(formula.parts[0], effect), regression_rec(formula.parts[1], effect)])
    x = Atom.negate(formula)
    y = eff_con(x, effect.pop(0)[1])
    z = Atom.negate(y)
    return Disjunction([eff_con(formula, effect), Conjunction(formula, Atom.negate(eff_con(Atom.negate(formula), effect)))])
    print("nothing was true")



def eff_con(formula, effect):
    if type(effect) is bool:
        if effect:
            return False
    if isinstance(effect, Conjunction):
        return Disjunction([eff_con(formula, effect.parts[0]), eff_con(formula, effect.parts[1])])
    if isinstance(effect, ConditionalEffect):
        return Conjunction([effect.parts[0], eff_con(formula, effect.parts[1])])
    if formula.__eq__(effect):
        return True
    return False


def regression(formula, operator):
    operator.precondition.dump()
    print("\nop.add_eff: ", operator.add_effects, "\n")

    return Conjunction([operator.precondition, regression_rec(formula, operator.add_effects)])




 # add after delete (für <a, (c |> d) and not d) in folie b02 s16
    #regr(q,o) ->_o q
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
    conj = Conjunction([A, B])
    disjunction = Disjunction([conj, C])
    action = actions[0]

    action_temp = PropositionalAction(name="test", precondition=A, effects=[(A, B)], cost=1)
    z = regression(B, action_temp)
    print("after regression: ")
    z.dump()




