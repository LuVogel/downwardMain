import collections
import copy
import itertools
import math
import os
import subprocess
import sys
from queue import Queue


from invariant_candidate import *
from pddl.conditions import *

filenum_list = []
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


# performs weakening on a given invariant candidate.
# 1. invariant candidate is extended by a literal
# 2. invariant candidate is extended by an inequality
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
    arg_set = set()
    for part in inv_cand.parts:
        for arg in part.args:
            arg_set.add(arg)
    # extend by a literal
    exist_vars = set(inv_cand.parts[0].args)
    if len(inv_cand.parts) == 1:
        print("weaken by extending literal")
        for pred, type_names in predicates_in_task.items():
            params = fill_params(exist_vars, len(type_names))
            for args in params:
                type_counter = 0
                types_temp = set()
                # for arg in args:
                #     types_temp.add(TypedObject(name=arg, type_name=type_names[type_counter].type_name))
                #     type_counter += 1
                pos = Atom(pred, args)
                neg = NegatedAtom(pred, args)
                for part in inv_cand.parts:
                    for i in range(len(predicates_in_task[part.predicate])):
                        types_temp.add(TypedObject(name=part.args[i], type_name=predicates_in_task[part.predicate][i].type_name))
                for i in range(len(predicates_in_task[pred])):
                    types_temp.add(TypedObject(name=args[i], type_name=predicates_in_task[pred][i].type_name))
                inv = InvariantCandidate(parts=inv_cand.parts + (pos,), ineq=[], types=types_temp)
                if inv not in seen_inv_candidates and pos != inv_cand.parts[0]:
                    inv_cand_set.add(inv)
                inv = InvariantCandidate(parts=inv_cand.parts + (neg,), ineq=[], types=types_temp)
                if inv not in seen_inv_candidates and neg != inv_cand.parts[0]:
                    inv_cand_set.add(inv)


            params.clear()
        return inv_cand_set

    # add inequality
    existing_inequalities = set(inv_cand.ineq)
    max_ineq = 0
    n = 0
    for i in inv_cand.parts:
        n += len(i.args)
    for k in range(1, n + 1):
        max_ineq += math.comb(n, k)


    if len(inv_cand.parts) == 2:
        exist_vars |= set(inv_cand.parts[1].args)
    if len(existing_inequalities) >= max_ineq:
        print("max inequalities reached")
        return [None]
    elif len(inv_cand.parts) > 2:
        print("more than 2 literals in disjunction, stop weakening")
        return [None]
    for c in itertools.combinations(exist_vars, 2):
        temp = False
        if c not in existing_inequalities:
            for part in inv_cand.parts:
                if part.predicate == "=" and isinstance(part, Atom):
                    if set(part.args) != set(c):
                        temp = True
                        ineq = set(existing_inequalities)
                        ineq.add(c)
                        break
        if temp:
            for part in inv_cand.parts:
                types = set()
                for i in range(len(predicates_in_task[part.predicate])):
                    types.add(TypedObject(name=part.args[i], type_name=predicates_in_task[part.predicate][i].type_name))
                inv = InvariantCandidate(parts=inv_cand.parts, ineq=ineq, types=types)

                if inv not in seen_inv_candidates:
                    inv_cand_set.add(InvariantCandidate(parts=inv_cand.parts, ineq=ineq, types=types))

    return inv_cand_set


# call of regression: regression of a formula through an operator
def regression(formula: Condition, operator: PropositionalAction):
    # eff_list = eff(o)
    eff_list = get_effects_from_action(operator)
    # start recursive call
    return Conjunction(
        [Conjunction(operator.precondition), regression_rec(formula, Conjunction(eff_list))]).simplified()


# recursive call of regression: regression of a formula through an effect
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


# effect condition, used in recusrive call of regression
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


# creates a list of all effects (add/del effects) incl. their condition (if ConditionalEffect) of a given Condition
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


# writes a given invariant candidate to a given file
def write_invariant_to_fof(inv_cand: InvariantCandidate, file, counter: int):
    found_variables = set()
    def get_vampire_var(variable, inv_cand, quantifier):
        if variable.startswith("?"):
            if quantifier:
                s = ""
                for type in inv_cand.types:
                    if variable == type.name:
                        s = f":{type.type_name}"
                for ineq in inv_cand.ineq:
                    for val in ineq:
                        if variable == val:
                            for part in inv_cand.parts:
                                if variable in part.args:
                                    pos = part.args.index(variable)
                                    s = f":{predicates_in_task[part.predicate][pos].type_name}"
                variable = variable.split("?")[1].upper()
                variable += s
                found_variables.add(variable)
            else:
                variable = variable.split("?")[1].upper()
                found_variables.add(variable)

            return variable
        else:
            assert False

    def get_vampire_literal(literal: Literal, inv_types):

        name = literal.predicate
        args = ",".join(get_vampire_var(var, inv_types, quantifier=False) for var in literal.args)
        if not literal.args:
            args = "NOARGS"
        neg = "~" if literal.negated else ""
        if name == "=":
            if literal.negated:
                return f"{neg}equal({args})"
            else:
                a = "=".join(args.split(","))
                return a

        return f"{neg}{name}({args})"
    vars = inv_cand.get_variables()
    inv_types = inv_cand
    all_quantifiers = "![%s]: " % ", ".join(get_vampire_var(var, inv_cand, quantifier=True) for var in vars)
    parts = [get_vampire_literal(part, inv_types) for part in inv_cand.parts]

    parts = " | ".join(parts)
    # fof(formulaX, axiom, ![X0]: ![X1]: object(X0) -> clear(X0))
    # tff(formulaX, axiom, ![X0: object] : ![X1: object] : clear(X0))
    # tff(formulaX, axiom, ![X0: object, X1] : on(X0,X1))


    file.write(f"tff(formula{counter}, axiom, {all_quantifiers}  {parts}).\n")

# write a given formula (as negated conjecture) into a given file
def write_neg_conjecture_to_fof(formula: Condition, file, counter):
    def get_classifiers(formula):
        s = "!["
        for literal in formula.parts:
            if not literal.args:
                s += f"NOARGS:empty,"
            types = predicates_in_task[literal.predicate]
            for i in range(len(types)):
                if isinstance(literal.args[i], TypedObject):
                    lit_arg = literal.args[i].name.upper()
                else:
                    lit_arg = literal.args[i].upper()

                s += f"{lit_arg}:{types[i].type_name},"
        if s.endswith(","):
            s = s[:-1]
        s += "]:"
        return s
    def get_vampire_literal_for_neg_conjecture(literal: Literal):
        name = literal.predicate
        arg_list = []
        for var in literal.args:
            if isinstance(var, TypedObject):
                var = var.name
            arg_list.append(var)
        args = ",".join(arg_list).upper()
        if not literal.args:
            args = "NOARGS"
        neg = "~" if literal.negated else ""
        if name == "=":
            if literal.negated:
                return f"equal({args})"
            else:
                a = "=".join(arg_list)
                return a
        return f"{neg}{name}({args})"
    join_s = condition_type_to_logical_string[formula.__class__]
    parts = [get_vampire_literal_for_neg_conjecture(part) for part in formula.parts]
    parts = f" {join_s} ".join(parts)
    classifier = get_classifiers(formula)
    file.write(f"tff(formula{counter}, negated_conjecture, {classifier} ({parts})).")

# checks with help of a given list if a given Condition is satisfiable. this is done by creating a new file
# with previous functions and do a satisfiable-test with the help of vampire prover
def write_type_restriction_to_tff(inv_cand, file, counter):
    # fof(typeX, type, object: $tType).
    for type in inv_cand.types:
        file.write(f"tff(type_dec{counter}, type, {type.type_name}: $tType).")
    pass


def is_sat(negated_conjecture: Condition, axiom_list: list[Condition], filenum, tff_typelist):
    # path = "src/translate/vampire/tptp-formulas" + str(filenum) + ".p"
    path = "src/translate/vampire/tptp-formulas.p"

    with open(path, "w") as file:
        for tff_line in tff_typelist:
            file.write(tff_line)
        counter = 1
        for inv_cand in axiom_list:
            write_invariant_to_fof(inv_cand, file, counter)
            counter += 1
        write_neg_conjecture_to_fof(negated_conjecture, file, 0)
    file.close()
    command = ['vampire', path]
    try:
        output = subprocess.check_output(command, stderr=subprocess.STDOUT, universal_newlines=True)
        res = output
        if "Termination reason: Refutation" in res:
            print("refutation")
            return False
        elif "Termination reason: Satisfiable" in res:
            print("satisfiable")
            return True
        else:
            print("something went wrong in vampire (not refutation, not sat, not process-error")
            return False
    except subprocess.CalledProcessError as e:
        filenum_list.append(filenum)
        print(f"Error in vampire process: {e} in tptp-formulas")
        return False

# removing a given invariant candidate from a queue of invariant candidates
def remove_inv_cand(inv_cand_queue: Queue[InvariantCandidate], inv_cand: InvariantCandidate):
    if inv_cand in inv_cand_queue.queue:
        while not inv_cand_queue.empty():
            item = inv_cand_queue.get()
            if item != inv_cand:
                inv_cand_queue.put(item)
            else:
                break
    return inv_cand_queue


# starting regression of a formula through an operator. formula is given by parts of given invariant candidate
# operator is given by action
# starts the sat-test with result of regression or return True/False if result was Truth/Falsity
def regr_and_sat(action: PropositionalAction, inv_cand_temp: InvariantCandidate,
                 inv_cand_set_C_0: set[InvariantCandidate], filenum, tff_typelist):
    if len(inv_cand_temp.parts) == 1:
        input_for_regression = inv_cand_temp.parts[0]
    else:
        input_for_regression = Disjunction(inv_cand_temp.parts)

    after_reg = regression(input_for_regression.negate(), action).simplified()
    if isinstance(after_reg, Falsity):
        return False
    elif isinstance(after_reg, Truth):
        return True
    else:
        return is_sat(after_reg, inv_cand_set_C_0, filenum, tff_typelist)


# helper function for c_sigma
# used if there are more possible variables which can be combined with a predicate
def create_grounded_invariant_for_c_sigma(list_of_vars, predicate, negated):
    inv_list = []
    count_of_lists = len(list_of_vars)
    if count_of_lists == 1:
        types = set()
        for var in list_of_vars[0]:
            types.add(TypedObject(name=var, type_name=predicates_in_task[predicate][0].type_name))
        for var in list_of_vars[0]:
            if negated:
                inv_list.append(InvariantCandidate(parts=[NegatedAtom(predicate=predicate, args=[var])], ineq=[], types=types))
            else:
                inv_list.append(InvariantCandidate(parts=[Atom(predicate=predicate, args=[var])], ineq=[], types=types))
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
            inv_list.append(InvariantCandidate(parts=[NegatedAtom(predicate=predicate, args=temp_list)], ineq=[], types=temp_list))
        else:
            inv_list.append(InvariantCandidate(parts=[Atom(predicate=predicate, args=temp_list)], ineq=[], types=temp_list))
    return inv_list

# create from a given predicate and variables all possible combinations
# return list of invariant candidates used for regression
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

# parsing a given predicate to their possible types and creating invariant candidates
def parse_objects_with_current_pred(task_pred: Predicate, init_pred_map):
    # if pred does not occurrent in init-state, we add invariant that is always false
    if task_pred.name not in init_pred_map:
        args = ["?x%i"%i for i in range(len(task_pred.arguments))]
        types = set()
        for i in range(len(args)):
            types.add(TypedObject(name=args[i], type_name=predicates_in_task[task_pred.name][i].type_name))
        for i in range(len(args)):
            yield InvariantCandidate(parts=[NegatedAtom(predicate=task_pred.name, args=args)], ineq=[], types=types)
        return
    # next we test whether all possible instantiations are initially true, with simple counting test (considering types)
    p_should_have_length = 1
    for pred_arg in predicates_in_task[task_pred.name]:
        p_should_have_length *= len(object_types_in_task[pred_arg.type_name])

    if len(init_pred_map[task_pred.name]) == p_should_have_length:
        args = ["?x%i" % i for i in range(len(task_pred.arguments))]
        types = set()
        for i in range(len(args)):
            types.add(TypedObject(name=args[i], type_name=predicates_in_task[task_pred.name][i].type_name))
        for i in range(len(args)):
            yield InvariantCandidate(parts=[Atom(predicate=task_pred.name, args=args)], ineq=[], types=types)
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

            inv = InvariantCandidate(parts=[NegatedAtom(predicate=task_pred.name, args=args1),
                                            NegatedAtom(predicate=task_pred.name, args=args2)],
                                     ineq=[[args1[pos], args2[pos]]], types=type_list)
            yield inv

    return None

# create invariant candidates from init-task.
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

def delete_vampire_files():
    folder_path = "src/translate/vampire/"
    file_list = os.listdir(folder_path)
    for file_name in file_list:
        if any(str(num) in file_name for num in file_list):
            continue
        file_path = os.path.join(folder_path, file_name)
        os.remove(file_path)

# eigentliche Funktion die Aktionen vorbereite, und den Algorithmus durchführt
def get_limited_instantiation(task):
    # Let prms_t(a) be number of schema variables of type t in action a
    # Let prms_t(p) be number of terms of type t in schematic atomic formulas with predicate p
    max_action_params = max(len(action.parameters) for action in task.actions)
    max_predicate_params = max(len(pred.arguments) for pred in task.predicates)
    max_params_t = max(max_action_params, max_predicate_params)
    return max_params_t + (2 - 1) * max_predicate_params


def create_restricted_domain(task, actions):
    res_dom = {}
    for action in actions:
        for typedobject in action.parameters:
            if typedobject.type_name not in res_dom:
                res_dom[typedobject.type_name] = set()
            res_dom[typedobject.type_name].add(typedobject.name)
    return res_dom



def get_schematic_invariants(task: Task, actions: list[PropositionalAction], fluent_ground_atoms):
    delete_vampire_files()
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
    tff_type_list = []
    type_counter = 1
    tff_type_list.append("tff(noargs_type, type, empty: $tType).\n")
    for type in task.types:
        if type.basetype_name == None:
            s = f"tff(type_dec{type_counter}, type, {type.name}: $tType).\n"
        else:
            s = f"tff(type_dec{type_counter}, type, {type.name}: {type.basetype_name}).\n"
        tff_type_list.append(s)
        type_counter += 1
    for pred in task.predicates:
        if pred.name == "=":
            predname = "equal"
        else:
            predname = pred.name
        s = ""
        for arg in pred.arguments:
            if s == "":
                s = arg.type_name
            else:
                s += f" * {arg.type_name}"
        if "*" in s:
            tff_type_list.append(f"tff({predname}_decl, type, {predname}: ({s}) > $o).\n")
        elif s == "":
            tff_type_list.append(f"tff({predname}_decl, type, {predname}: NOARGS > $o).\n")
        else:
            tff_type_list.append(f"tff({predname}_decl, type, {predname}: {s} > $o).\n")

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
    filenum = 0
    while True:
        print("store nextqueue in inv cand set")
        inv_cand_set_C_0 = set(next_queue)
        for action in list_of_possible_actions:
            # user_unput = input("gibt exit ein falls du beenden möchtest")
            # if user_unput == "exit":
            #     delete_vampire_files()
            #     sys.exit()
            print("restart next_queue with action len: ", len(list_of_possible_actions), " and len current queue: ", len(next_queue))
            queue_cq = next_queue.copy()
            next_queue = collections.deque()
            while queue_cq:
                print("remove from current queue..")
                inv_cand = queue_cq.popleft()
                if inv_cand.contains(action):
                    print("create sigma, doing sat test with invariant candidate: ")
                    inv_cand.dump()
                    print("and action: ")
                    action.dump()
                    c_sigma = create_c_sigma(inv_cand)

                    is_inv_cand_sat = False
                    for c_sig in c_sigma:
                        if c_sig not in seen_inv_candidates:
                            if regr_and_sat(action, c_sig, inv_cand_set_C_0, filenum, tff_type_list):
                                seen_inv_candidates.append(c_sig)
                                is_inv_cand_sat = True
                                filenum += 1
                                break
                        filenum += 1
                    if is_inv_cand_sat:

                        weakend_inv_cand_set = weaken(inv_cand)
                        print("appending to queue from weakening...")
                        for weakend_inv_cand in weakend_inv_cand_set:
                            if weakend_inv_cand is not None:
                                print("append: ")
                                weakend_inv_cand.dump()
                                queue_cq.append(weakend_inv_cand)
                        print("done appending")

                    else:
                        print("no inv cand")
                        next_queue.append(inv_cand)
                else:
                    print("action no influence")
                    next_queue.append(inv_cand)
        print("check is queue is same as before")
        if set(next_queue) == inv_cand_set_C_0 or set(queue_cq) == inv_cand_set_C_0:
            # solution found, return
            print("solution finally found")


            return next_queue