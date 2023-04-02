import copy
import itertools

import invariant_finder

def regression(action, invariant, param):
    pass


def union_of(invariant_zero, param):
    pass


def is_sat(param):
    pass


def set_minus(invariants, invariant):
    pass


def weaken(invariant):
    pass


def get_schematic_invariants(invariants, actions):
    while True:
        invariant_zero = copy.copy(invariants)
        for action in actions:
            for invariant in invariants:
                if is_sat(union_of(invariant_zero,
                                   regression(action, invariant, invariant_finder.find_substitutions(action, invariant)))):
                    union_of(set_minus(invariants, invariant), weaken(invariant))
        if invariants == invariant_zero:
            return invariants
    return None


