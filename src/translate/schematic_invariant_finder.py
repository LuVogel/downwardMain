import collections
import copy
import subprocess
from queue import Queue

import invariant_candidate
from invariant_candidate import *
from pddl.conditions import *


seen_inv_candidates = {}

# a ist objekt
# x ist variable
# weakening
# TODO: check weaken --> hier müssen schematische inv cand hinzugefügt werden, im moment sind sie gegroundet
# parsing function von action effects  (objekten) zu möglichen variabeln
# im moment: für jede add/del effect in Action: Invariant Candidate bekommt einen part mehr (also literal zu Disjunktion,
# disjunktion zu disjunktion mit einer Klausel mehr
# für jeden add effect und del effect der nicht schon als part in Inv-Kandidat ist, wird ein neuer Invariant Candidate erstellt
# weaken führ so je nach dem zu mehreren neuen Invariant kandidaten
def weaken(inv_cand: InvariantCandidate, action: PropositionalAction):
    inv_cand_set = set()
    curr_inv_list = set(inv_cand.parts)
    for cond, eff in action.add_effects:
        if eff not in curr_inv_list:
            curr_inv_list.add(eff)
            inv_cand_set.add(InvariantCandidate(part=curr_inv_list))
            curr_inv_list.remove(eff)
    for cond, eff in action.del_effects:
        if eff.negate() not in curr_inv_list:
            curr_inv_list.add(eff.negate())
            inv_cand_set.add(InvariantCandidate(part=curr_inv_list))
            curr_inv_list.remove(eff.negate())
    return inv_cand_set
    # weaken of form X -> l_1 to X -> l_1 v l_2


# Regression ruft rekursiv regression_rec und eff_con auf und gibt am Schluss eine Conjunktion zurück die auch Truth oder Falsity sein kann
def regression(formula: Condition, operator: PropositionalAction):
    # eff_list = eff(o)
    eff_list = get_effects_from_action(operator)
    # start recursive call
    return Conjunction(
        [Conjunction(operator.precondition), regression_rec(formula, Conjunction(eff_list))]).simplified()


def regression_rec(formula: Condition, effect: Condition):
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


def eff_con(atomic_effect: Condition, effect: Condition):
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


def get_effects_from_action(operator: Condition):
    eff_list = []
    # add all add_effects
    for cond, eff in operator.add_effects:
        if len(cond) == 0:
            eff_list.append(eff)
        else:
            eff_list.append(ConditionalEffect(condition=cond, effect=eff))
    # add all del_effects as negated effect
    for cond, eff in operator.del_effects:
        if len(cond) == 0:
            eff_list.append(eff.negate())
        else:
            eff_list.append(ConditionalEffect(condition=cond, effect=eff.negate()))
    return eff_list


# nur als vorbereitung für vampire
def formula_to_list(formula: Condition):
    l = []
    x_found = False
    y_found = False
    # iterate through all parts in formulas and all arguments from each part
    for part in formula.parts:
        part_args = ""
        if len(part.args) == 0:
            part_args = "noargs"
        else:
            for arg in part.args:
                if isinstance(arg, TypedObject):
                    arg = arg.name
                if arg == "?x":
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


# schreibt die formeln (axiome und zu beweisen) ins fof file
def write_formula_to_fof(formula: Condition, type: str, file, counter: int):
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
        if len(formula.args) == 0:
            part_args = "noargs"
        else:
            for arg in formula.args:
                if isinstance(arg, TypedObject):
                    arg = arg.name
                if arg == "?x":
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


# tested ob die formeln satisfiable sind. negated_conjecture kann Truth/Falsity sein, was bei vampire auf probleme stösst
def is_sat(negated_conjecture: Condition, axiom_list: list[Condition]):
    with open("src/translate/tptp-formulas.p", "w") as file:
        counter = 1
        # create for all axioms the tptp file
        for inv_cand in axiom_list:
            if len(inv_cand.parts) == 1:
                write_formula_to_fof(inv_cand.parts[0], "axiom", file, counter)
            else:
                write_formula_to_fof(Disjunction(parts=inv_cand.parts), "axiom", file, counter)
            counter += 1
        # add formula we want to check to tptp file
        write_formula_to_fof(negated_conjecture, "negated_conjecture", file, 0)
    # run vampire
    result = subprocess.run(['vampire', 'src/translate/tptp-formulas.p'], capture_output=True)
    # return 0 for Satisfiable, else Refutation
    return result.returncode == 0


# wird am anfang gebraucht um alle prädikate und objekte die im task enthalten sind u erstellen.
# erstelle zuerst alle möglichen kombination aus objekten mit dem gegebenen prädikat
# kommen alle diese erstellten kombination in task.init vor --> als invariant candidate hinzufügen
# kommen keine dieser erstellten kombination in task.init vor --< als invariant candidate hinzufügen (aber als Negated)
# sonst --> kein Invariant Candidate return None
def parse_objects_with_current_pred(task: Task, task_objects: list[TypedObject], task_pred: Predicate):
    p_should_have_length = 0
    if len(task_pred.arguments) == 2:
        p_should_have_length = len(task_objects) * len(task_objects)
    elif len(task_pred.arguments) == 1:
        p_should_have_length = len(task_objects)
    elif len(task_pred.arguments) == 0:
        p_should_have_length = 1
    count_pred_in_init = 0
    for atom in task.init:
        if atom.predicate == task_pred.name:
            count_pred_in_init += 1
    if count_pred_in_init == p_should_have_length:
        return InvariantCandidate(part=[Atom(predicate=task_pred.name, args=task_pred.arguments)])
    elif count_pred_in_init == 0:
        return InvariantCandidate(part=[NegatedAtom(predicate=task_pred.name, args=task_pred.arguments)])
    else:
        return None

# mit obiger parsing function werden kandidaten erstellt
def create_invariant_candidates(task: Task):
    # create simple invariants: all atoms in init are used as invariant candidates
    inv_list = set()
    task_objects = list(task.objects)
    for task_pred in task.predicates:
        inv_cand = parse_objects_with_current_pred(task, task_objects, task_pred)
        if inv_cand is not None:
            inv_list.add(inv_cand)
    return set(inv_list)

# schaut das set durch und entfernt den gegebenen kandidaten sofern vorhanden
def remove_inv_cand(inv_cand_queue: Queue[InvariantCandidate], inv_cand: InvariantCandidate):
    if inv_cand in inv_cand_queue.queue:
        while not inv_cand_queue.empty():
            item = inv_cand_queue.get()
            if item != inv_cand:
                inv_cand_queue.put(item)
            else:
                break

        # if len(inv_cand.parts) == 1 and len(curr_cand.parts) == 1:
        #     if curr_cand.parts[0].predicate == inv_cand.parts[0].predicate:
        #         if len(curr_cand.parts[0].args) == 0:
        #             if (isinstance(curr_cand.parts[0], Atom) and isinstance(inv_cand.parts[0], Atom)) or (
        #                     isinstance(curr_cand.parts[0], NegatedAtom) and isinstance(inv_cand.parts[0], Atom)):
        #                 inv_cand_temp_set.remove(curr_cand)
        #                 return set(inv_cand_temp_set)
        #         elif len(curr_cand.parts[0].args) == 1:
        #             if isinstance(curr_cand.parts[0].args[0], TypedObject) and not isinstance(inv_cand.parts[0].args[0],
        #                                                                                       TypedObject):
        #                 pass
        #             elif curr_cand.parts[0].args[0] == inv_cand.parts[0].args[0]:
        #                 if (isinstance(curr_cand.parts[0], Atom) and isinstance(inv_cand.parts[0], Atom)) or (
        #                         isinstance(curr_cand.parts[0], NegatedAtom) and isinstance(inv_cand.parts[0],
        #                                                                                    Atom)):
        #                     inv_cand_temp_set.remove(curr_cand)
        #                     return set(inv_cand_temp_set)
        #         elif len(curr_cand.parts[0].args) == 2:
        #             if isinstance(curr_cand.parts[0].args[0], TypedObject) and not isinstance(inv_cand.parts[0].args[0],
        #                                                                                       TypedObject):
        #                 pass
        #             elif (curr_cand.parts[0].args[0] == inv_cand.parts[0].args[0]) and (
        #                     curr_cand.parts[0].args[1] == inv_cand.parts[0].args[1]):
        #                 if (isinstance(curr_cand.parts[0], Atom) and isinstance(inv_cand.parts[0], Atom)) or (
        #                         isinstance(curr_cand.parts[0], NegatedAtom) and isinstance(inv_cand.parts[0],
        #                                                                                    Atom)):
        #                     inv_cand_temp_set.remove(curr_cand)
        #                     return set(inv_cand_temp_set)
        # elif len(inv_cand.parts) > 0 and len(curr_cand.parts) == len(inv_cand.parts):
        #     print("try to remove disjunction")
        #     print("to remove: ")
        #     inv_cand.dump()
        #     print("check current: ")
        #     curr_cand.dump()
        #     if set(inv_cand.parts) == set(curr_cand.parts):
        #         print("current and to remove are same")
        #         inv_cand_temp_set.remove(curr_cand)
        #         return set(inv_cand_temp_set)

    return inv_cand_queue

# zuerst entfernen mit obiger funktionen und dann wird weaken aufgerufen
def remove_and_weaken(inv_cand_temp: InvariantCandidate, inv_cand_temp_set: set[InvariantCandidate],
                      action: PropositionalAction):
    #print("no invariant")
    inv_cand = invariant_candidate.InvariantCandidate(inv_cand_temp.parts)
    # inv candidates X_1 or X_2 == X_2 or X_1 --> im moment wird das nicht als gleich erkannt und daher key error
    # --> wurde behoben --> remove_inv_cand überprüft ob invariant candidate is in set falls ja entferne diesen (sollte zu diesem zeitpunkt im set sein)
    inv_cand_temp_set = remove_inv_cand(set(inv_cand_temp_set), inv_cand)
    # aktion übergeben zu sat test
    # schwächt schematische invarianten ab
    # hier muss geprüft werden ob C wächst, falls nicht --> emptyObject oder so übergeben (da C sonst grösse ändert innerhalb iteration)

    weakened_inv_cand_set = weaken(inv_cand, action)
    for weakend_inv_cand in weakened_inv_cand_set:
        if weakend_inv_cand is not None:
            inv_cand_temp_set.add(weakend_inv_cand)
    check_set = set()
    for check_for_none in inv_cand_temp_set:
        if check_for_none is not None:
            check_set.add(check_for_none)
    return set(check_set)

# erstellt aus schematischen invarianten gegroundete
# --> TODO: nur nötig sofern inv_cand schematisch ist? falls schon gegroundet nichts machen?? --> inv_cand kann nur schematisch sein!!
def create_c_sigma(inv_cand: InvariantCandidate, task_objects: list[TypedObject]):
    c_sigma = []
    for parts in inv_cand.parts:
        negated = False
        if isinstance(parts, Atom):
            negated = True
        if len(parts.args) == 0:
            if negated:
                c_sigma.append(
                    InvariantCandidate(part=[NegatedAtom(predicate=parts.predicate, args=[])]))
            else:
                c_sigma.append(InvariantCandidate(part=[Atom(predicate=parts.predicate, args=[])]))
        elif len(parts.args) == 1:
            for obj in task_objects:
                if negated:
                    c_sigma.append(
                        InvariantCandidate(
                            part=[NegatedAtom(predicate=parts.predicate, args=[obj.name])]))
                else:
                    c_sigma.append(
                        InvariantCandidate(part=[Atom(predicate=parts.predicate, args=[obj.name])]))
        elif len(parts.args) == 2:
            for obj in task_objects:
                for obj2 in task_objects:
                    if negated:
                        c_sigma.append(InvariantCandidate(
                            part=[NegatedAtom(predicate=parts.predicate, args=[obj.name, obj2.name])]))
                    else:
                        c_sigma.append(InvariantCandidate(
                            part=[Atom(predicate=parts.predicate, args=[obj.name, obj2.name])]))
    return set(c_sigma)


# startet regression und mach den sat test --> da regression Truth/falsity zurück geben kann, ist hier fehlerpotential vorhanden
def regr_and_sat(action: PropositionalAction, inv_cand_temp: InvariantCandidate,
                 inv_cand_set_C_0: set[InvariantCandidate]):
    if len(inv_cand_temp.parts) == 1:
        input_for_regression = inv_cand_temp.parts[0]
    else:
        input_for_regression = Disjunction(inv_cand_temp.parts)

    after_reg = regression(input_for_regression.negate(), action).simplified()
    # wenn after reg falsity -> direkt false return
    # theoretisch wenn Truth dann true zurückgeben, weil anfangs ist C erfüllbar (inital state)
    # Da weakening nur schwächere Formeln hinzufügt, bleib C in diesem Punkt erfüllbar.
    if isinstance(after_reg, Falsity):
        return False
    elif isinstance(after_reg, Truth):
        return True
    else:
        return is_sat(after_reg, inv_cand_set_C_0)

# eigentliche Funktion die Aktionen vorbereite, und den Algorithmus durchführt
def get_schematic_invariants(task: Task, actions: list[PropositionalAction]):
    # use deepcopy, so we can modify actions and task freely
    task = copy.deepcopy(task)
    available_objects = []
    for obj in task.objects:
        available_objects.append(obj.name)
    actions = copy.deepcopy(actions)
    inv_cand_set_C = set(create_invariant_candidates(task))
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

    next_queue = collections.deque()
    for i in inv_cand_set_C:
        next_queue.append(i)
    # TODO: gesehene invariant candidates als Hashmap (global) --> damit nicht mehrmals in queue hinzugefügt wird durch weaken (bzw in weakening schon beachten)
    # wenn inv cand erstellt überprüfen ob schon gesehen, falls nicht hinufügen und fortfahren, falls nein, skippen
    while True:
        print("invariant candidates found at beginning of each while loop: ", len(next_queue))
        for i in next_queue:
            i.dump()
        inv_cand_set_C_0 = set(next_queue)
        for action in list_of_possible_actions:
            print("picked action: ")
            action.dump()
            queue_cq = next_queue.copy()
            print("current queue: ")
            for i in queue_cq:
                i.dump()

            next_queue = collections.deque()
            # kommt in der aktion ein negiertes literal vor welches in c enthalten ist --> kann action überhaupt effekt auf candidates haben
            # if else check
            while len(queue_cq) != 0:
                inv_cand = queue_cq.popleft()
                print("picked invariant candidate: ")
                inv_cand.dump()
                print("remaining... ")
                for i in queue_cq:
                    i.dump()
                print("end remaining.")
                if inv_cand.contains(action):
                    # return c sigma: each item in list test in regression and sat test, if any is sat --> then weaken inv cand
                    c_sigma = create_c_sigma(inv_cand, task.objects)
                    is_inv_cand_sat = False

                    for c_sig in c_sigma:
                        if regr_and_sat(action, c_sig, inv_cand_set_C_0):
                            is_inv_cand_sat = True
                            break
                    if is_inv_cand_sat:
                        print("invariant candidate is sat")
                        # remove not needed, since already removed. if not inv cand: add to next queue

                        # then weaken
                        weakend_inv_cand_set = weaken(inv_cand, action)
                        print("appending to weakend candidates to queue...")
                        for weakend_inv_cand in weakend_inv_cand_set:
                            if weakend_inv_cand is not None:
                                print("appending: ")
                                weakend_inv_cand.dump()
                                queue_cq.append(weakend_inv_cand)
                        print("appending done.")
                    else:
                        next_queue.append(inv_cand)
                        print("invariant, append to next_queue")
                else:
                    pass
                    print("action has no influence")
            print("while loop ended: ")
            print("passing queue: ")
            for i in next_queue:
                i.dump()
            print("end passing queue...")

        print("end of both for-loops")
        print("number of invariant candidates at current status: ", len(next_queue))
        for i in next_queue:
            i.dump()
        # TODO: print statements anpassen --> gebe grösse der queues aus damit ich sehe wann und wie die resultierende queue zu 0 wird.
        # vorher weakening noch verbessern und restliche todos angehen
        if set(next_queue) == inv_cand_set_C_0:

            # solution found, return
            return set(next_queue)
        print("stating new for loop")
