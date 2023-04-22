from src.translate.pddl import Truth, Falsity, NegatedAtom, Disjunction, Conjunction, Atom
from src.translate.pddl.effects import *


#Besprechung: del und add effects --> del effects einfach negieren
# rintannen: schmematische vs gegroundete invarianten.
# invarianten: Kernaussagen von Blocksworld --> nicht für spezifisches problem
# regression test mit Action die Conditional Effect hat


# TODO: wie action negieren?
# ist keine action sondern state-variable
def negate_state_var(operator):
    operator.name = "not " + operator.name
    return operator

# weaken: return {c \lor a | a \in A} U {c \lor \lnot a | a \in A}

def weaken(formula, operator):
    return set(Disjunction([formula, operator]), Disjunction([formula, negate_state_var(operator)]))
# anstatt Union set --> set hat union



# add after delete?? vlt mal mit einfacherer aktion (mit weniger effects testen)
def regression_rec(formula, effect):
    if isinstance(formula, Truth):
        return Truth()
    if isinstance(formula, Falsity):
        return Falsity()
    if isinstance(formula, NegatedAtom):
        return regression_rec(formula, effect).negate()
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
    # TODO: atomic_effect == effect?
    if atomic_effect.parts == effect.parts and atomic_effect.args == effect.args:
        return Truth()
    return Falsity()



def regression(formula, operator):
    eff_list = []
    for cond, eff in operator.add_effects:
        eff_list.append(eff)
    for cond, eff in operator.del_effects:
        eff_list.append(eff.negate())
    return Conjunction([Conjunction(operator.precondition), regression_rec(formula, Conjunction(eff_list))]).simplified()



# add after delete (für <a, (c |> d) and not d) in folie b02 s16
# regr(q,o) ->_o q
# [e]_s consistent effectbedingung
# task anpassen (verkleinern, dann exlplore für grounding)
# for instance in c = c\sigma
# visitor pattern s



# TODO: invarianten:
# Eine grosse Conjunction von diesen Punkten oder eine Liste von einzelnen Formulas für C?
# 1. Anzahl d. Blöcke ändern sich nicht während eines Problems
# 2. Jeder Block liegt entweder auf dem Tisch oder auf einem anderen Block --> oder auch in der Hand? dann nicht zu beginn gültig
#          könnte in dieser art gemacht werden: for all i \in {1, ..., N} für N Blöcke: onTable(i) or (exist j != i mit on(i,j))
# 3. ein Block kann sich nur bewegen, wenn er frei ist
# 4. es gibt eine begrenze Anzahl an Aktionen die ausgeführt werden können: zu Beginn alle möglichen Actions sammeln
# 5. Regeln wie es is nicht möglich Blöcke zu zerstören oder in der Luft zu schweben??
# 6. es ist nicht möglich gleichzeitig mehrere Blöcke zu bewegen oder zu stapeln
# 7. es gibt eine bestimmte Anzahl an positionen wo sich ein Block befinden kann
# 8. jede Block ist eindeutig --> name == id?

# bei grosse Conjunction: for parts in Conjunction.parts --> regr(not parts, action)
# bei Liste: for form in list: --> regr(not form, action)
def get_schematic_invariants(relaxed_reachable, atoms, actions, goal_list, axioms,
                             reachable_action_params, task_init):
    list_of_true_in_init = []
    for i in task_init:
        if i.predicate != "=":
            list_of_true_in_init.append(i)
    C = Conjunction(list_of_true_in_init)
    temp = 0
    action_temp = None
    for a in actions:
        if temp == 11:
            action_temp = a
        temp += 1
    a = Atom(predicate="on", args=["a", "d"])
    b = Atom(predicate="on", args=["d", "c"])


    conj = Conjunction([a, b])
    z = regression(conj, action_temp).simplified()
    print("after regression: ")
    z.dump()

    while True:
        C_0 = C
        for action in actions:
            for c in C.parts:
                x = regression(c.negate(), action)
                print("x after regr: ")
                x.dump()
                temp_union = set([C_0, x])
                print("temp_union: ", temp_union)
        return

