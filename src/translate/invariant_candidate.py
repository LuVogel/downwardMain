from pddl import  *
from typing import List

class InvariantCandidate:

    # part1 is X
    # part2 is l_1 or l_2 // l_1
    # X is empty of conjuction of inequalities
    # l_1/l_2 are bool/schematic state variables
    # frozenset --> reihenfolge nicht beachten, hashbar im gegesatz zu set
    def __init__(self, parts: List[conditions.Literal], ineq, types):
        self.parts = tuple(parts)
        self.ineq = frozenset(frozenset(i) for i in ineq)
        self.types = tuple(types)
        self.hash = hash((self.__class__, self.parts, self.ineq, self.types))

    def __hash__(self):
        return self.hash

    def __ne__(self, other):
        return not self == other
    def __lt__(self, other):
        return self.hash < other.hash
    def __le__(self, other):
        return self.hash <= other.hash

    def __eq__(self, other):
        # Compare hash first for speed reasons.
        return (self.hash == other.hash and
                self.__class__ is other.__class__ and
                self.parts == other.parts and
                self.ineq == other.ineq and
                self.types == other.types)

    def dump(self, indent="  "):
        print("------")
        print("%s%s" % (indent, self._dump()))
        for part in self.parts:
            part.dump(indent + "  ")
        print("ineq: ")
        for i in self.ineq:
            print(i)
        for type in self.types:
            print("type: ", type)
        print("------")

    def _dump(self):
        return self.__class__.__name__

    def contains(self, action):
        for part in self.parts:
            for con, eff in action.add_effects:
                if isinstance(eff, NegatedAtom):
                    if part.predicate == eff.predicate:
                        return True
            for cond, eff in action.del_effects:
                if isinstance(eff, Atom):
                    if part.predicate == eff.negate().predicate:
                        return True

    def get_variables(self):
        vars = set()
        for part in self.parts:
            vars |= set(part.args)
        for inequality in self.ineq:
            vars |= inequality
        return vars

