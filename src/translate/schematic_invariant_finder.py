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
    if formula.negate():
        return regression_rec(NegatedAtom.negate(Literal(formula)), effect, negated=True)
    if isinstance(formula, Disjunction):
        return Disjunction([regression_rec(formula.parts[0], effect), regression_rec(formula.parts[1], effect)])
    if isinstance(formula, Conjunction):
        return Conjunction([regression_rec(formula.parts[0], effect), regression_rec(formula.parts[1], effect)])


def eff_con(effect):
    pass


def regression(formula, operator):
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
    z = regression(disjunction, action)
    print("after regression: ", z)




