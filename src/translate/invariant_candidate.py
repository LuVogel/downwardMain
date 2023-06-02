from pddl import  *
from typing import List


def get_form_from_parts(parts):
    if isinstance(parts, Atom):
        if parts.predicate == "handempty":
            return Atom(predicate=parts.predicate, args=["noargs"])
        elif len(parts.args) == 1:
            return Atom(predicate=parts.predicate, args=["?x"])
        elif len(parts.args) == 2:
            return Atom(predicate=parts.predicate, args=["?x", "?y"])
        return parts

    elif isinstance(parts, NegatedAtom):
        if parts.predicate == "handempty":
            return NegatedAtom(predicate=parts.predicate, args=["noargs"])
        elif len(parts.args) == 1:
            return NegatedAtom(predicate=parts.predicate, args=["?x"])
        elif len(parts.args) == 2:
            return NegatedAtom(predicate=parts.predicate, args=["?x", "?y"])
        return parts
    else:
        setlist = set()
        for part in parts.parts:
            setlist.add(get_form_from_parts(part))
        if isinstance(parts, Disjunction):
            return Disjunction(setlist)
        else:
            return Conjunction(setlist)

class InvariantCandidate:

    # part1 is X
    # part2 is l_1 or l_2 // l_1
    # X is empty of conjuction of inequalities
    # l_1/l_2 are bool/schematic state variables
    def __init__(self, parts: conditions.Condition):
        self.part = get_form_from_parts(parts)
        self.hash = hash((self.__class__, self.part))

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
                self.part == other.part)

    def dump(self, indent="  "):
        print("%s%s" % (indent, self._dump()))
        self.part.dump(indent + "  ")
    def _dump(self):
        return self.__class__.__name__
    def contains(self, condition, action):
        if isinstance(condition, Atom) or isinstance(condition, NegatedAtom):
            for cond, eff in action.add_effects:
                if isinstance(eff, NegatedAtom):
                    if condition.predicate == eff.predicate:
                        return True
            # add all del_effects as negated effect
            for cond, eff in action.del_effects:
                if isinstance(eff, Atom):
                    if condition.predicate == eff.negate().predicate:
                        return True
        elif isinstance(condition, Conjunction) or isinstance(condition, Disjunction):
            for parts in condition.parts:
                return self.contains(parts, action)

