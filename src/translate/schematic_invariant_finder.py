from src.translate.pddl import Truth, Falsity, NegatedAtom, Disjunction, Conjunction, Atom
from src.translate.pddl.effects import *


#Besprechung: del und add effects --> del effects einfach negieren
# rintannen: schmematische vs gegroundete invarianten.
# invarianten: Kernaussagen von Blocksworld --> nicht für spezifisches problem
# regression test mit Action die Conditional Effect hat


# TODO: wie action negieren?
# ist keine action sondern state-variable
def negateAction(operator):
    operator.name = "not " + operator.name
    return operator

# weaken: return {c \lor a | a \in A} U {c \lor \lnot a | a \in A}

def weaken(formula, operator):
    return Union(Disjunction([formula, operator]), Disjunction([formula, negateAction(operator)]))
# anstatt Union set --> set hat union


def regression_rec(formula, effect):
    if isinstance(formula, Truth):
        return Truth()
    if isinstance(formula, Falsity):
        return Falsity()
    if isinstance(formula, NegatedAtom):
        return regression_rec(NegatedAtom.negate(Literal(formula)), effect)
    if isinstance(formula, Disjunction):
        return Disjunction([regression_rec(formula.parts[0], effect), regression_rec(formula.parts[1], effect)]).simplified()
    if isinstance(formula, Conjunction):
        return Conjunction([regression_rec(formula.parts[0], effect), regression_rec(formula.parts[1], effect)]).simplified()
    return Disjunction([eff_con(formula, effect), Conjunction([formula, eff_con(formula.negate(), effect).negate()])]).simplified()


def eff_con(formula, effect):
    if isinstance(effect, Truth):
        return Falsity()
    if isinstance(effect, Conjunction):
        eff_con_list = []
        for part in effect.parts:
            eff_con_list.append(eff_con(formula, part))
        return Disjunction(eff_con_list).simplified()
    if isinstance(effect, ConditionalEffect):
        return Conjunction([effect.condition, eff_con(formula, effect.effect)]).simplified()
    if formula == effect:
        #formula == effect!
        return Truth()  # simplified streichen
    return Falsity()


def regression(formula, operator):
    eff_list = []
    for cond, eff in operator.add_effects:
        eff_list.append(eff)
   # for cond, eff in operator.del_effects:
      #  eff_list.append(eff)
    return Conjunction([Conjunction(operator.precondition), regression_rec(formula, Conjunction(eff_list))]).simplified()



# add after delete (für <a, (c |> d) and not d) in folie b02 s16
# regr(q,o) ->_o q
# [e]_s consistent effectbedingung
# task anpassen (verkleinern, dann exlplore für grounding)
# for instance in c = c\sigma
# visitor pattern s



# TODO: input müsste schon invarianten enthalten und mögliche action. dann auch algorithmus abfoge implementieren
def get_schematic_invariants(relaxed_reachable, atoms, actions, goal_list, axioms,
                             reachable_action_params):

    print(atoms)
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

    a = Atom(predicate="on", args=["a", "d"])
    b = Atom(predicate="on", args=["d", "c"])
    conj = Conjunction([a, b])
    print("conj: ")
    conj.dump()
    print("\naction: ")
    action_temp.dump()
    z = regression(conj, action_temp)
    print("after regression: ")
    z.dump()



