import collections
import copy
import itertools
import subprocess
from queue import Queue

import invariant_candidate
from invariant_candidate import *
from pddl.conditions import *


seen_inv_candidates = []
predicates_in_task = {}
object_types_in_task = {}


def parse_literal_with_objects_to_literals_with_vars(literal: Literal, task: Task, negated: bool):
    objects = task.objects
    current_pred = None
    for pred in task.predicates:
        if literal.predicate == pred.name:
            if negated:
                return [NegatedAtom(predicate=pred.name, args=pred.arguments)]
            else:
                return [Atom(predicate=pred.name, args=pred.arguments)]
            current_pred = pred
            break

    object_list = []
    for _ in range(len(current_pred.arguments)):
        object_list.append(objects)
    combinations = list(itertools.product(*object_list))
    result = []
    for combo in combinations:
        typelist = []
        for obj in combo:
            for args in current_pred.arguments:
                if obj.type_name == args.type_name:
                    typelist.append(TypedObject(name="?" + obj.name, type_name=obj.type_name))
        if len(typelist) == len(current_pred.arguments):
            if negated:
                result.append(NegatedAtom(predicate=pred.name, args=typelist))
            else:
                result.append(Atom(predicate=pred.name, args=typelist))

    return result



# a ist objekt
# x ist variable
# weakening
# TODO: check weaken --> hier müssen schematische inv cand hinzugefügt werden, im moment sind sie gegroundet
# parsing function von action effects  (objekten) zu möglichen variabeln
# im moment: für jede add/del effect in Action: Invariant Candidate bekommt einen part mehr (also literal zu Disjunktion,
# disjunktion zu disjunktion mit einer Klausel mehr
# für jeden add effect und del effect der nicht schon als part in Inv-Kandidat ist, wird ein neuer Invariant Candidate erstellt
# weaken führ so je nach dem zu mehreren neuen Invariant kandidaten



def weaken2(inv_cand: InvariantCandidate):
    def get_new_var(existing):
        val = 0
        while True:
            if "?val%i" % val in existing:
                val += 1
            else:
                return f"?val{val}"

    def fill_params(used, num_to_add, current=[], params=[]):
        if num_to_add == 0:
            params.append(current)
        else:
            # use_new_variable
            new_var = get_new_var(used)
            extended = list(current)
            extended.append(new_var)
            new_used = set(used)
            new_used.add(new_var)
            fill_params(new_used, num_to_add - 1, extended, params)
            # use an existing variable
            for var in used:
                extended = list(current)
                extended.append(var)
                fill_params(used, num_to_add - 1, extended, params)
        return params

    inv_cand_set = set()
    # extend by a literal
    if len(inv_cand.parts) == 1:
        exist_vars = set(inv_cand.parts[0].args)
        for pred, type_names in predicates_in_task.items():
            params = fill_params(exist_vars, len(type_names))
            for args in params:
                type_counter = 0
                arg_temp = []
                for arg in args:
                    arg_temp.append(TypedObject(name=arg, type_name=type_names[type_counter].type_name))
                    type_counter += 1
                pos = Atom(pred, arg_temp)
                neg = NegatedAtom(pred, arg_temp)
                inv_cand_set.add(InvariantCandidate(parts=inv_cand.parts+(pos,), ineq=[]))
                inv_cand_set.add(InvariantCandidate(parts=inv_cand.parts+(neg,), ineq=[]))
            params.clear()

    # add inequality
    exist_vars = set(inv_cand.parts[0].args)
    if len(inv_cand.parts) == 2:
        exist_vars |= set(inv_cand.parts[1].args)
    # TODO don't add existing inequalities again
    existing_inequalities = set(inv_cand.ineq)
    for c in itertools.combinations(exist_vars, 2):
    # for c in itertools.combinations(sorted(exist_vars), 2):
        temp = False
        if c not in existing_inequalities:
            temp = True
            ineq = set(existing_inequalities)
            ineq.add(c)
        if temp:
            inv_cand_set.add(InvariantCandidate(parts=inv_cand.parts, ineq=ineq))
    return inv_cand_set
def weaken(inv_cand: InvariantCandidate, action: PropositionalAction):
    inv_cand_set = set()
    curr_inv_list = set(inv_cand.parts)
    for cond, eff in action.add_effects:
        if eff not in curr_inv_list:
            args = predicates_in_task[eff.predicate]
            atom = Atom(predicate=eff.predicate, args=args)
            curr_inv_list.add(atom)
            curr_inv_list = set(curr_inv_list)
            new_inv_cand = InvariantCandidate(parts=curr_inv_list, ineq=[])
            if new_inv_cand not in seen_inv_candidates:
                inv_cand_set.add(inv_cand)
            curr_inv_list.remove(atom)
    for cond, eff in action.del_effects:
        if eff.negate() not in curr_inv_list:
            args = predicates_in_task[eff.predicate]
            atom = NegatedAtom(predicate=eff.predicate, args=args)
            curr_inv_list.add(atom)
            curr_inv_list = set(curr_inv_list)
            new_inv_cand = InvariantCandidate(parts=curr_inv_list, ineq=[])
            if new_inv_cand not in seen_inv_candidates:
                inv_cand_set.add(inv_cand)
            curr_inv_list.remove(atom)
    # for cond, eff in action.add_effects:
    #     if eff not in curr_inv_list:
    #         temp_list = parse_literal_with_objects_to_literals_with_vars(eff, task, negated=False)
    #         for temp in temp_list:
    #             curr_inv_list.add(temp)
    #         curr_inv_list = set(curr_inv_list)
    #         new_inv_cand = InvariantCandidate(part=curr_inv_list)
    #         if new_inv_cand not in seen_inv_candidates:
    #             inv_cand_set.add(inv_cand)
    #         for temp in temp_list:
    #             curr_inv_list.remove(temp)
    # for cond, eff in action.del_effects:
    #     if eff.negate() not in curr_inv_list:
    #         temp_list = parse_literal_with_objects_to_literals_with_vars(eff.negate(), task, negated=True)
    #         for temp in temp_list:
    #             curr_inv_list.add(temp)
    #         curr_inv_list = set(curr_inv_list)
    #         new_inv_cand = InvariantCandidate(part=curr_inv_list)
    #         if new_inv_cand not in seen_inv_candidates:
    #             inv_cand_set.add(inv_cand)
    #         for temp in temp_list:
    #             curr_inv_list.remove(temp)
    return set(inv_cand_set)
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
            found_variables = []
            for arg in part.args:
                if isinstance(arg, TypedObject):
                    arg = arg.name
                if "?" in arg:
                    arg = arg.split("?")[1].upper()
                    if arg not in found_variables:
                        found_variables.append(arg)
                # if arg == "?x":
                #     arg = "X"
                #     x_found = True
                # elif arg == "?y":
                #     arg = "Y"
                #     y_found = True
                if part_args == "":
                    part_args = arg
                else:
                    part_args = part_args + "," + arg
        # add entry to list for each part we have one line
        l.append(f"{part.predicate}({part_args})")
    # return list of formulas as well as if generic variables were found (e.g. not objects a,b,c but vars x,y)
    return l, found_variables


# schreibt die formeln (axiome und zu beweisen) ins fof file
def write_formula_to_fof(formula: Condition, type: str, file, counter: int):
    # write one line to tptp-formulas.p
    file.write("fof(formula{}, ".format(counter) + type + ",")
    if isinstance(formula, Conjunction):
        # conjunction joins with &
        # get strings from formulas
        list_formula, found_list = formula_to_list(formula)
        # needed for generic variables
        write_generic = ""
        for found in found_list:
            write_generic += f"![{found}]: "
        # if x_found and y_found:
        #     file.write("![X]: ![Y]:")
        # elif x_found:
        #     file.write("![X]:")
        # elif y_found:
        #     file.write("![Y]:")
        file.write(write_generic)
        file.write(" & ".join(list_formula) + ").\n")
    elif isinstance(formula, Disjunction):
        # disjunction needs | to join
        list_formula, found_list = formula_to_list(formula)
        write_generic = ""
        for found in found_list:
            write_generic += f"![{found}]: "
        # if x_found and y_found:
        #     file.write("![X]: ![Y]:")
        # elif x_found:
        #     file.write("![X]:")
        # elif y_found:
        #     file.write("![Y]:")
        file.write(write_generic)
        file.write(" | ".join(list_formula) + ").\n")
    elif isinstance(formula, Atom) or isinstance(formula, NegatedAtom):
        # atom does not need formula conversion
        part_args = ""
        found_variables = []
        if len(formula.args) == 0:
            part_args = "noargs"
        else:
            for arg in formula.args:
                if isinstance(arg, TypedObject):
                    arg = arg.name
                if "?" in arg:
                    arg = arg.split("?")[1].upper()
                    if arg not in found_variables:
                        found_variables.append(arg)
                # if arg == "?x":
                #     arg = "X"
                #     x_found = True
                # elif arg == "?y":
                #     arg = "Y"
                #     y_found = True
                if part_args == "":
                    part_args = arg
                else:
                    part_args = part_args + "," + arg
        # if x_found and y_found:
        #     file.write("![X]: ![Y]:")
        # elif x_found:
        #     file.write("![X]:")
        # elif y_found:
        #     file.write("![Y]:")
        write_generic = ""
        for found in found_variables:
            write_generic += f"![{found}]: "
        if len(write_generic) > 1:
            file.write(write_generic)
        if isinstance(formula, Atom):
            # check again if negated or not
            s = f"{formula.predicate}({part_args})).\n"
        else:
            s = f"~{formula.predicate}({part_args})).\n"
        # finally write string/line to file
        file.write(s)


# tested ob die formeln satisfiable sind. negated_conjecture kann Truth/Falsity sein, was bei vampire auf probleme stösst
def write_tptp_file_to_txt_for_analyzing(source_path, dest_path, vampire_res):
    with open(source_path, 'r') as source:
        content = source.read()
    with open(dest_path, 'a') as dest:
        dest.write("start\n\n\n\n\n")

        dest.write(content)
        dest.write(vampire_res)
        dest.write("end\n\n\n\n\n")


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
    res = result.stdout.decode()
    if "Termination reason: Refutation" in res:
        return False
    elif "Termination reason: Satisfiable" in res:
        return True
    else:
        print("something went wrong in vampire")
        print(res)
        # TODO: predicate-namen sind für vampire nicht lesbar (new-axiom@0(A1,T))
        write_tptp_file_to_txt_for_analyzing("src/translate/tptp-formulas.p", "src/translate/tptp-analyze.txt", res)
        return False




# schaut das set durch und entfernt den gegebenen kandidaten sofern vorhanden
def remove_inv_cand(inv_cand_queue: Queue[InvariantCandidate], inv_cand: InvariantCandidate):
    if inv_cand in inv_cand_queue.queue:
        while not inv_cand_queue.empty():
            item = inv_cand_queue.get()
            if item != inv_cand:
                inv_cand_queue.put(item)
            else:
                break
    return inv_cand_queue

# zuerst entfernen mit obiger funktionen und dann wird weaken aufgerufen
def remove_and_weaken(inv_cand_temp: InvariantCandidate, inv_cand_temp_set: set[InvariantCandidate],
                      action: PropositionalAction, task: Task):
    #print("no invariant")
    inv_cand = invariant_candidate.InvariantCandidate(parts=inv_cand_temp.parts, ineq=[])
    # inv candidates X_1 or X_2 == X_2 or X_1 --> im moment wird das nicht als gleich erkannt und daher key error
    # --> wurde behoben --> remove_inv_cand überprüft ob invariant candidate is in set falls ja entferne diesen (sollte zu diesem zeitpunkt im set sein)
    inv_cand_temp_set = remove_inv_cand(set(inv_cand_temp_set), inv_cand)
    # aktion übergeben zu sat test
    # schwächt schematische invarianten ab
    # hier muss geprüft werden ob C wächst, falls nicht --> emptyObject oder so übergeben (da C sonst grösse ändert innerhalb iteration)

    weakened_inv_cand_set = weaken(inv_cand, action, task)
    for weakend_inv_cand in weakened_inv_cand_set:
        if weakend_inv_cand is not None:
            inv_cand_temp_set.add(weakend_inv_cand)
    check_set = set()
    for check_for_none in inv_cand_temp_set:
        if check_for_none is not None:
            check_set.add(check_for_none)
    return set(check_set)


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


def create_grounded_invariant_for_c_sigma(list_of_vars, predicate, negated):
    inv_list = []
    count_of_lists = len(list_of_vars)
    if count_of_lists == 1:
        for var in list_of_vars[0]:
            if negated:
                inv_list.append(InvariantCandidate(parts=[NegatedAtom(predicate=predicate, args=[var])], ineq=[]))
            else:
                inv_list.append(InvariantCandidate(parts=[Atom(predicate=predicate, args=[var])], ineq=[]))
        return inv_list
    combo_list = []
    for combination in itertools.product(*list_of_vars):
        combo_list.append(list(combination))
    for combo in combo_list:
        temp_list = []
        count = 0
        for types in predicates_in_task[predicate]:
            temp_list.append(TypedObject(name=combo[count], type_name=types.type_name))
            count += 1
        if negated:
            inv_list.append(InvariantCandidate(parts=[NegatedAtom(predicate=predicate, args=temp_list)], ineq=[]))
        else:
            inv_list.append(InvariantCandidate(parts=[Atom(predicate=predicate, args=temp_list)], ineq=[]))

    return inv_list

# erstellt aus schematischen invarianten gegroundete
#  inv_cand kann nur schematisch sein!!
def create_c_sigma(inv_cand: InvariantCandidate):
    c_sigma = []
    for literal in inv_cand.parts:
        negated = False
        if isinstance(literal, Atom):
            negated = True
        if len(literal.args) == 0:
            c_sigma.append(literal)
        else:
            list_of_objects = predicates_in_task[literal.predicate]
            list_of_vars = []
            for object in list_of_objects:
                list_of_vars.append(object_types_in_task[object.type_name])
            c_sigma += create_grounded_invariant_for_c_sigma(list_of_vars, literal.predicate, negated)
    return c_sigma

def count_predicates_in_init(task: Task):
    map = {}
    for atom in task.init:
        if atom.predicate not in map:
            map[atom.predicate] = 1
        else:
            map[atom.predicate] += 1
    return map

# wird am anfang gebraucht um alle prädikate und objekte die im task enthalten sind u erstellen.
# erstelle zuerst alle möglichen kombination aus objekten mit dem gegebenen prädikat
# kommen alle diese erstellten kombination in task.init vor --> als invariant candidate hinzufügen
# kommen keine dieser erstellten kombination in task.init vor --< als invariant candidate hinzufügen (aber als Negated)
# sonst --> kein Invariant Candidate return None
def parse_objects_with_current_pred(task_pred: Predicate, map):
    p_should_have_length = 1
    used_object_list = predicates_in_task[task_pred.name]
    for used_object in used_object_list:
        p_should_have_length *= len(object_types_in_task[used_object.type_name])
    if task_pred.name not in map:
        count_pred_in_init = 0
    else:
        count_pred_in_init = map[task_pred.name]
    if count_pred_in_init == p_should_have_length:
        return InvariantCandidate(parts=[Atom(predicate=task_pred.name, args=task_pred.arguments)], ineq=[])
    elif count_pred_in_init == 0:
        return InvariantCandidate(parts=[NegatedAtom(predicate=task_pred.name, args=task_pred.arguments)], ineq=[])
    else:
        return None

# mit obiger parsing function werden kandidaten erstellt
def create_invariant_candidates(task: Task):
    # create simple invariants: all atoms in init are used as invariant candidates
    inv_list = set()
    map = count_predicates_in_init(task)
    for task_pred in task.predicates:
        inv_cand = parse_objects_with_current_pred(task_pred, map)
        if inv_cand is not None:
            inv_list.add(inv_cand)
    return set(inv_list)

# eigentliche Funktion die Aktionen vorbereite, und den Algorithmus durchführt
def get_schematic_invariants(task: Task, actions: list[PropositionalAction]):
    # use deepcopy, so we can modify actions and task freely
    task = copy.deepcopy(task)
    for obj in task.objects:
        if obj.type_name not in object_types_in_task:
            object_types_in_task[obj.type_name] = []
        object_types_in_task[obj.type_name].append(obj.name)
    still_to_add = collections.deque()
    for t in task.types:
        child = t.name
        parent = t.basetype_name
        print("child: ", child, ", parent: ", parent)
        if parent is not None:
            if parent not in object_types_in_task:
                object_types_in_task[parent] = []
            if child not in object_types_in_task:
                still_to_add.append((child, parent))
            else:
                for i in object_types_in_task[child]:
                    object_types_in_task[parent].append(i)
    while still_to_add:
        child, parent = still_to_add.pop()
        print("child: ", child, ", parent: ", parent)
        if parent is not None:
            if parent not in object_types_in_task:
                object_types_in_task[parent] = []
            if child not in object_types_in_task:
                still_to_add.append((child, parent))
            else:
                for i in object_types_in_task[child]:
                    object_types_in_task[parent].append(i)
    for pred in task.predicates:
        predicates_in_task[pred.name] = pred.arguments
    print("object_types_in_task: ")
    for i, j in object_types_in_task.items():
        print(i, ": ", j)
    print("predicates_in_task: ")
    for i, j in predicates_in_task.items():
        print(i, ": ", j)
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
    print("starting with following inv-candidates: ")
    for i in inv_cand_set_C:
        next_queue.append(i)
        i.dump()
    # gesehene invariant candidates als Hashmap (global) --> damit nicht mehrmals in queue hinzugefügt wird durch weaken (bzw in weakening schon beachten)
    # wenn inv cand erstellt überprüfen ob schon gesehen, falls nicht hinufügen und fortfahren, falls nein, skippen
    while True:
        inv_cand_set_C_0 = set(next_queue)
        for action in list_of_possible_actions:
            queue_cq = next_queue.copy()
            next_queue = collections.deque()
            # kommt in der aktion ein negiertes literal vor welches in c enthalten ist --> kann action überhaupt effekt auf candidates haben
            # if else check
            while queue_cq:
                inv_cand = queue_cq.popleft()
                if inv_cand.contains(action):
                    # return c sigma: each item in list test in regression and sat test, if any is sat --> then weaken inv cand
                    c_sigma = create_c_sigma(inv_cand)

                    is_inv_cand_sat = False

                    for c_sig in c_sigma:
                        if regr_and_sat(action, c_sig, inv_cand_set_C_0):
                            is_inv_cand_sat = True
                            break
                    if is_inv_cand_sat:
                        # remove not needed, since already removed. if not inv cand: add to next queue
                        seen_inv_candidates.append(inv_cand)
                        # then weaken
                        weakend_inv_cand_set = weaken2(inv_cand)

                        #weakend_inv_cand_set = weaken(inv_cand, action)

                        for weakend_inv_cand in weakend_inv_cand_set:
                            if weakend_inv_cand is not None:
                                queue_cq.append(weakend_inv_cand)

                    else:
                        next_queue.append(inv_cand)
                else:
                    next_queue.append(inv_cand)
        # TODO: print statements anpassen --> gebe grösse der queues aus damit ich sehe wann und wie die resultierende queue zu 0 wird.
        # TODO: später: für weakening: x != y --> dafür bei InvariantCandidate neues Feld wo man sowas definieren kann
        # vorher weakening noch verbessern und restliche todos angehen
        if set(next_queue) == inv_cand_set_C_0 or set(queue_cq) == inv_cand_set_C_0:

            # solution found, return
            return next_queue