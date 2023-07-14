from pddl import  *
from typing import List

class InvariantCandidate:

    # part1 is X
    # part2 is l_1 or l_2 // l_1
    # X is empty of conjuction of inequalities 
    # l_1/l_2 are bool/schematic state variables
    # frozenset --> reihenfolge nicht beachten, hashbar im gegesatz zu set
    # types: set of TypedObject
    def __init__(self, parts: List[conditions.Literal], ineq, types):
        self.parts = frozenset(parts)
        self.ineq = frozenset(frozenset(i) for i in ineq)
        self.types = frozenset(types)
        self.hash = hash((self.__class__, self.parts, self.ineq, self.types))

    def __hash__(self):
        return self.hash

    def __ne__(self, other):
        return not self == other
    def __lt__(self, other):
        raise NotImplemented
        # return self.hash < other.hash
    def __le__(self, other):
        raise NotImplemented
        # return self.hash <= other.hash

    def __eq__(self, other):
        # Compare hash first for speed reasons.
        return (self.hash == other.hash and
                self.parts == other.parts and
                self.ineq == other.ineq and
                self.types == other.types)

    def dump(self, indent="  "):
        self.dump_gabi()
        return

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

    def dump_gabi(self):
        def part_str(part):
            neg = "¬" if part.negated else ""
            return "%s%s(%s)" % (neg, part.predicate, ", ".join(map(str, part.args)))
        ineq = ",".join(f"{x1}≠{x2}" for x1,x2 in self.ineq)
        if self.ineq:
            ineq += " → "
        disc = " ∨ ".join(part_str(part) for part in self.parts)
        var_types = ", ".join(str(typed_obj) for typed_obj in self.types)
        print(f"INVARIANT CANDIDATE: {ineq}{disc} [{var_types}]")


    def _dump(self):
        return self.__class__.__name__

    def contains(self, action):
        """
        True if the action can potentially invalidate the candidates.

        Returns true iff the action has a delete effect on a predcate that
        occurs positively in the invariant or an add effect on a predicate
        occurring negatively.
        """   
        for part in self.parts:
            if part.negated:
                for _, eff in action.add_effects:
                    if part.predicate == eff.predicate:
                        return True
            else:
                for _, eff in action.del_effects:
                    if part.predicate == eff.predicate:
                        return True
        return False

    def get_variables(self):
        """returns the set of all variables occuring in the invariant candidate"""
        vars = set()
        for part in self.parts:
            vars |= set(part.args)
        for inequality in self.ineq:
            vars |= inequality
        return vars

