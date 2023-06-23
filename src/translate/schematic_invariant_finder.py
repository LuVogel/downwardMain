import collections
import copy
import itertools
import subprocess
from queue import Queue

from invariant_candidate import *
from pddl.conditions import *


seen_inv_candidates = []
predicates_in_task = {}
object_types_in_task = {}
condition_type_to_logical_string = {
    Conjunction : "&",
    Disjunction : "|",
    NegatedAtom : "~"
}


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

def weaken(inv_cand: InvariantCandidate):
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
                types_temp = set()
                for arg in arg_temp:
                    types_temp.add(arg)
                for part in inv_cand.parts:
                    for i in range(len(predicates_in_task[part.predicate])):
                        types_temp.add(TypedObject(name=part.args[i], type_name=predicates_in_task[part.predicate][i]))
                for type in types_temp:
                    inv_cand_set.add(InvariantCandidate(parts=inv_cand.parts+(pos,), ineq=[], type=type))
                    inv_cand_set.add(InvariantCandidate(parts=inv_cand.parts+(neg,), ineq=[], type=type))
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
            for part in inv_cand.parts:
                for i in range(len(predicates_in_task[part.predicate])):
                    type = TypedObject(name=part.args[i], type_name=predicates_in_task[part.predicate][i])
                    inv_cand_set.add(InvariantCandidate(parts=inv_cand.parts, ineq=ineq, type=type))
    return inv_cand_set






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


def write_invariant_to_fof(inv_cand: InvariantCandidate, file, counter: int):

    found_variables = set()
    def get_vampire_var(variable):
        if variable.startswith("?"):
            variable = variable.split("?")[1].upper()
            found_variables.add(variable)
            return variable
        else:
            assert False

    def get_vampire_literal(literal: Literal):

        name = literal.predicate
        args = ",".join(get_vampire_var(var) for var in literal.args)
        if not literal.args:
            args = "noargs"
        neg = "~" if literal.negated else ""
        return f"{neg}{name}({args})"

        # write one line to tptp-formulas.p
    vars = inv_cand.get_variables()
    inv_type = inv_cand.type
    all_quantifiers = " ".join("![%s]: " % get_vampire_var(var) for var in vars)
    parts = [get_vampire_literal(part) for part in inv_cand.parts]
    parts = " | ".join(parts)
    inv_type_name = inv_type.name.split("?")[1].upper()
    file.write(f"fof(formula{counter}, axiom, {all_quantifiers} ({inv_type.type_name}({inv_type_name}) => ( {parts} ))).\n")

# schreibt die formeln (axiome und zu beweisen) ins fof file
def write_neg_conjecture_to_fof(formula: Condition, file, counter):

    def get_vampire_literal_for_neg_conjecture(literal: Literal):
        name = literal.predicate
        arg_list = []
        for var in literal.args:
            if isinstance(var, TypedObject):
                var = var.name
            arg_list.append(var)
        args = ",".join(arg_list)
        if not literal.args:
            args = "noargs"
        neg = "~" if literal.negated else ""
        return f"{neg}{name}({args})"

    join_s = condition_type_to_logical_string[formula.__class__]
    parts = [get_vampire_literal_for_neg_conjecture(part) for part in formula.parts]
    parts = f" {join_s} ".join(parts)

    file.write(f"fof(formula{counter}, negated_conjecture, ({parts})).")


def is_sat(negated_conjecture: Condition, axiom_list: list[Condition]):
    with open("src/translate/tptp-formulas.p", "w") as file:
        counter = 1
        # create for all axioms the tptp file

        for inv_cand in axiom_list:
            print("inv_cand: ")
            inv_cand.dump()
            write_invariant_to_fof(inv_cand, file, counter)
            counter += 1
        # add formula we want to check to tptp file
        # eigene funktion oder umschreiben
        write_neg_conjecture_to_fof(negated_conjecture, file, 0)
    # run vampire
    print("start\n-----------------")
    with open("src/translate/tptp-formulas.p", "r") as file:
        for line in file:
            print("line: ", line)
    print("end\n-----------------")

    result = subprocess.run(['vampire', 'src/translate/tptp-formulas.p'], capture_output=True)
    res = result.stdout.decode()
    if "Termination reason: Refutation" in res:
        return False
    elif "Termination reason: Satisfiable" in res:
        return True
    else:
        print("something went wrong in vampire")
        print("failure: ", res)
        # TODO: predicate-namen sind für vampire nicht lesbar (new-axiom@0(A1,T))
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
            type = TypedObject(name=var, type_name=predicates_in_task[predicate][0])
            if negated:
                inv_list.append(InvariantCandidate(parts=[NegatedAtom(predicate=predicate, args=[var])], ineq=[], type=type))
            else:
                inv_list.append(InvariantCandidate(parts=[Atom(predicate=predicate, args=[var])], ineq=[], type=type))
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
        for type in temp_list:
            if negated:
                inv_list.append(InvariantCandidate(parts=[NegatedAtom(predicate=predicate, args=temp_list)], ineq=[], type=type))
            else:
                inv_list.append(InvariantCandidate(parts=[Atom(predicate=predicate, args=temp_list)], ineq=[], type=type))

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

def collect_predicates_in_init(task: Task, fluent_predicates):
    map = collections.defaultdict(list)
    for atom in task.init:
        if atom.predicate in fluent_predicates:
            map[atom.predicate].append(atom)
    return map

# wird am anfang gebraucht um alle prädikate und objekte die im task enthalten sind u erstellen.
# erstelle zuerst alle möglichen kombination aus objekten mit dem gegebenen prädikat
# kommen alle diese erstellten kombination in task.init vor --> als invariant candidate hinzufügen
# kommen keine dieser erstellten kombination in task.init vor --< als invariant candidate hinzufügen (aber als Negated)
# sonst --> kein Invariant Candidate return None
def parse_objects_with_current_pred(task_pred: Predicate, init_pred_map):
    # if pred does not occurrent in init-state, we add invariant that is always false
    if task_pred.name not in init_pred_map:
        args = ["?x%i"%i for i in range(len(task_pred.arguments))]
        for i in range(len(args)):
            type = TypedObject(name=args[i], type_name=predicates_in_task[task_pred.name][i].type_name)
            yield InvariantCandidate(parts=[NegatedAtom(predicate=task_pred.name, args=args)], ineq=[], type=type)
        return
    # next we test whether all possible instantiations are initially true, with simple counting test (considering types)
    p_should_have_length = 1
    for pred_arg in predicates_in_task[task_pred.name]:
        p_should_have_length *= len(object_types_in_task[pred_arg.type_name])

    if len(init_pred_map[task_pred.name]) == p_should_have_length:
        args = ["?x%i" % i for i in range(len(task_pred.arguments))]
        for i in range(len(args)):
            type = TypedObject(name=args[i], type_name=predicates_in_task[task_pred.name][i].type_name)
            yield InvariantCandidate(parts=[Atom(predicate=task_pred.name, args=args)], ineq=[], type=type)
        return
    # we next identify mutexes of the form x \neq y --> \lnot P(x,z) \lor P(y,z) always fixing all but one argument
    for pos, arg in enumerate(task_pred.arguments):
        init_dict = {}
        for atom in init_pred_map[task_pred.name]:
            atom_args = list(atom.args)
            atom_args[pos] = "?"
            atom_args = tuple(atom_args)
            if atom_args in init_dict and init_dict[atom_args] != atom.args[pos]:
                break
            else:
                init_dict[atom_args] = atom.args[pos]
        else:
            args1 = ["?x%i" % i for i in range(len(task_pred.arguments))]
            args2 = list(args1)
            args2[pos] = "?x%i" % len(task_pred.arguments)
            type_list = set()
            for i in range(len(args1)):
                type_list.add(TypedObject(name=args1[i], type_name=predicates_in_task[task_pred.name][i].type_name))
            for i in range(len(args2)):
                type_list.add(TypedObject(name=args2[i], type_name=predicates_in_task[task_pred.name][i].type_name))
            for type in type_list:
                inv = InvariantCandidate(parts=[NegatedAtom(predicate=task_pred.name, args=args1),
                                            NegatedAtom(predicate=task_pred.name, args=args2)],
                                     ineq=[[args1[pos], args2[pos]]], type=type)
            yield inv

    return None

# mit obiger parsing function werden kandidaten erstellt
def create_invariant_candidates(task: Task, fluent_ground_atoms):
    # create simple invariants: all atoms in init are used as invariant candidates
    inv_list = set()
    fluent_predicates = set()
    for atom in fluent_ground_atoms:
        fluent_predicates.add(atom.predicate)

    init_pred_map = collect_predicates_in_init(task, fluent_predicates)
    for task_pred in task.predicates:
        if task_pred.name in fluent_predicates:
            for inv_cand in parse_objects_with_current_pred(task_pred, init_pred_map):
                inv_list.add(inv_cand)
    return inv_list

def register_object_for_type(name: str, type: str, type_dict: dict, type_to_supertype: dict):
    objects = type_dict.setdefault(type, [])
    objects.append(name)
    if type_to_supertype[type] is not None:
        register_object_for_type(name, type_to_supertype[type], type_dict, type_to_supertype)

# eigentliche Funktion die Aktionen vorbereite, und den Algorithmus durchführt
def get_schematic_invariants(task: Task, actions: list[PropositionalAction], fluent_ground_atoms):
    # use deepcopy, so we can modify actions and task freely
    task = copy.deepcopy(task)
    type_to_supertype = {t.name : t.basetype_name for t in task.types}
    for obj in task.objects:
        register_object_for_type(obj.name, obj.type_name, object_types_in_task, type_to_supertype)

    for pred in task.predicates:
        predicates_in_task[pred.name] = pred.arguments
    print("object_types_in_task: ")
    for i, j in object_types_in_task.items():
        print(i, ": ", j)
    print("predicates_in_task: ")
    for i, j in predicates_in_task.items():
        print(i, ": ", j)
    actions = copy.deepcopy(actions)
    inv_cand_set_C = set(create_invariant_candidates(task, fluent_ground_atoms))
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
                        weakend_inv_cand_set = weaken(inv_cand)
                        for weakend_inv_cand in weakend_inv_cand_set:
                            if weakend_inv_cand is not None:
                                queue_cq.append(weakend_inv_cand)
                    else:
                        next_queue.append(inv_cand)
                else:
                    next_queue.append(inv_cand)
        if set(next_queue) == inv_cand_set_C_0 or set(queue_cq) == inv_cand_set_C_0:
            # solution found, return
            return next_queue