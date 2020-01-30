"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""

import datetime


class ArithmeticMultiply(object):
    def __init__(self, v):
        self._v = v

    def __repr__(self):
        return "*%i" % self._v


class ArithmeticAdd(object):
    def __init__(self, v):
        self._v = v

    def __repr__(self):
        return "+%i" % self._v


class ArithmeticTrueDivide(object):
    def __init__(self, v):
        self._v = v

    def __repr__(self):
        return "/%i" % self._v


class ArithmeticSubtract(object):
    def __init__(self, v):
        self._v = v

    def __repr__(self):
        return "-%i" % self._v


def apply_arithmetic_stack(stack, observation):
    """
    Given a list of lambda functions, iteratively apply them to the observation
    to yield a final value.
    """
    current_value = observation
    for f in stack:
        if f.__class__.__name__ == ArithmeticMultiply.__name__:
            current_value *= f._v
        elif f.__class__.__name__ == ArithmeticAdd.__name__:
            current_value += f._v
        elif f.__class__.__name__ == ArithmeticTrueDivide.__name__:
            current_value /= f._v
        elif f.__class__.__name__ == ArithmeticSubtract.__name__:
            current_value -= f._v
    return current_value


"""
Classes for atoms specific to this logic.
"""


class Atom(object):
    """
    This class is the parent class of all classes that model types of atoms in the logic.
    """

    def __init__(self):
        pass

    def _and(self, *conjuncts):
        return land(self, *conjuncts)


class StateValueInInterval(Atom):
    """
    This class models the atom (s(x) in I).
    """

    def __init__(self, state, name, interval):
        self._state = state
        self._name = name
        self._interval = interval
        self.verdict = None

    def __repr__(self):
        return "(%s)(%s) in %s" % (self._state, self._name, self._interval)

    def __eq__(self, other_atom):
        if type(other_atom) is StateValueInInterval:
            return (self._state == other_atom._state and self._name == other_atom._name \
                    and self._interval == other_atom._interval)
        else:
            return False

    def __hash__(self):
        return id(self)

    def check(self, value):
        """
        Mandatory check method used by formula trees to compute truth values.
        """
        return self._interval[0] <= value[0][0][self._name] <= self._interval[1]


class StateValueInOpenInterval(Atom):
    """
    This class models the atom (s(x) in I), where I is open.
    We model openness by strict inequality checks in the check method.
    """

    def __init__(self, state, name, interval):
        self._state = state
        self._name = name
        self._interval = interval
        self.verdict = None

    def __repr__(self):
        return "(%s)(%s) in %s" % (self._state, self._name, self._interval)

    def __eq__(self, other_atom):
        if type(other_atom) is StateValueInInterval:
            return self._state == other_atom._state and self._name == other_atom._name and self._interval == other_atom._interval
        else:
            return False

    def check(self, value):
        """
        Mandatory check method used by formula trees to compute truth values.
        """
        return self._interval[0] < value[0][0][self._name] < self._interval[1]


class StateValueEqualTo(Atom):
    """
    This class models the atom (s(x) = X).
    """

    def __init__(self, state, name, value):
        self._state = state
        self._name = name
        self._value = value
        self.verdict = None

    def __repr__(self):
        return "(%s)(%s) = %s" % (self._state, self._name, self._value)

    def __eq__(self, other_atom):
        if type(other_atom) is StateValueEqualTo:
            return (self._state == other_atom._state and self._name == other_atom._name \
                    and self._value == other_atom._value)
        else:
            return False

    def check(self, value):
        return self._value == value[0][0][self._name]


class StateValueTypeEqualTo(Atom):
    """
    This class models the atom (type(s(x)) = T).
    """

    def __init__(self, state, name, value):
        self._state = state
        self._name = name
        self._value = value
        self.verdict = None

    def __repr__(self):
        return "type((%s)(%s)) = %s" % (self._state, self._name, self._value)

    def __eq__(self, other_atom):
        if type(other_atom) is StateValueTypeEqualTo:
            return (self._state == other_atom._state and self._name == other_atom._name \
                    and self._value == other_atom._value)
        else:
            return False

    def check(self, value):
        return value[0][0][self._name] == self._value.__name__


class StateValueEqualToMixed(Atom):
    """
    This class models the atom (s1(x) = s2(y)).
    """

    def __init__(self, lhs, lhs_name, rhs, rhs_name):
        self._lhs = lhs
        self._rhs = rhs
        self._lhs_name = lhs_name
        self._rhs_name = rhs_name
        self.verdict = None

    def __repr__(self):
        return "(%s)(%s) = (%s)(%s)" % (self._lhs, self._lhs_name, self._rhs, self._rhs_name)

    def __eq__(self, other_atom):
        if type(other_atom) is StateValueEqualToMixed:
            return (self._lhs == other_atom._lhs
                    and self._lhs_name == self._rhs_name)
        else:
            return False

    def check(self, cummulative_state):
        """
        If either the RHS or LHS are None, we don't try to reach a truth value.
        But if they are both not equal to None, we check for equality.
        """
        if cummulative_state.get(0) is None or cummulative_state.get(1) is None:
            return None
        else:
            lhs_with_arithmetic = apply_arithmetic_stack(
                self._lhs.arithmetic_stack,
                cummulative_state[0][0]
            )
            rhs_with_arithmetic = apply_arithmetic_stack(
                self._rhs.arithmetic_stack,
                cummulative_state[1][0]
            )
            return lhs_with_arithmetic == rhs_with_arithmetic


class StateValueLengthInInterval(Atom):
    """
    This class models the atom (len(s(x)) in I).
    """

    def __init__(self, state, name, interval):
        self._state = state
        self._name = name
        self._interval = interval
        self.verdict = None

    def __repr__(self):
        return "(%s(%s)).length() in %s" % (self._state, self._name, self._interval)

    def __eq__(self, other_atom):
        if type(other_atom) is StateValueLengthInInterval:
            return (self._state == other_atom._state and self._name == other_atom._name \
                    and self._interval == other_atom._interval)
        else:
            return False

    def check(self, value):
        """
        Mandatory check method used by formula trees to compute truth values.
        """
        return self._interval[0] <= value[0][0][self._name] <= self._interval[1]


class TransitionDurationInInterval(Atom):
    """
    This class models the atom (d(delta t) in I).
    """

    def __init__(self, transition, interval):
        self._transition = transition
        self._interval = interval
        self.verdict = None

    def __repr__(self):
        return "d(%s) in %s" % (self._transition, self._interval)

    def __eq__(self, other_atom):
        if type(other_atom) is TransitionDurationInInterval:
            return (self._transition == other_atom._transition and self._interval == other_atom._interval)
        else:
            return False

    def check(self, value):
        return self._interval[0] <= value[0][0].total_seconds() <= self._interval[1]


class TransitionDurationLessThanTransitionDurationMixed(Atom):
    """
    This class models the atom (duration(t1) < duration(t2))
    for v the duration of another transition.
    """

    def __init__(self, lhs_transition, rhs_transition):
        self._lhs = lhs_transition
        self._rhs = rhs_transition
        self.verdict = None

    def __repr__(self):
        return "d(%s) < d(%s)" % (self._lhs, self._rhs)

    def __eq__(self, other_atom):
        if type(other_atom) is TransitionDurationLessThanTransitionDurationMixed:
            return (self._lhs == other_atom._lhs and
                    self._rhs == other_atom._rhs)
        else:
            return False

    def check(self, cummulative_state):
        """
        If either the RHS or LHS are None, we don't try to reach a truth value.
        But if they are both not equal to None, we check for equality.
        """
        if cummulative_state.get(0) is None or cummulative_state.get(1) is None:
            return None
        else:
            return cummulative_state[0][0] < cummulative_state[1][0]


class TransitionDurationLessThanStateValueMixed(Atom):
    """
    This class models the atom (duration(t) < v)
    for v a value given by a state.
    """

    def __init__(self, transition, state, name):
        self._lhs = transition
        self._rhs = state
        self._rhs_name = name
        self.verdict = None

    def __repr__(self):
        return "d(%s) < (%s)(%s)" % (self._lhs, self._rhs, self._rhs_name)

    def __eq__(self, other_atom):
        if type(other_atom) is TransitionDurationLessThanStateValueMixed:
            return (self._lhs == other_atom._lhs and
                    self._rhs == other_atom._rhs and
                    self._rhs_name == other_atom._rhs_name)
        else:
            return False

    def check(self, cummulative_state):
        """
        If either the RHS or LHS are None, we don't try to reach a truth value.
        But if they are both not equal to None, we check for equality.
        """
        if cummulative_state.get(0) is None or cummulative_state.get(1) is None:
            return None
        else:
            rhs_with_arithmetic = apply_arithmetic_stack(
                self._rhs._arithmetic_stack,
                cummulative_state[1][0][self._rhs_name]
            )
            return cummulative_state[0][0].total_seconds() < rhs_with_arithmetic


class TransitionDurationLessThanStateValueLengthMixed(Atom):
    """
    This class models the atom (duration(t) < v.length())
    for v a value given by a state.
    """

    def __init__(self, transition, state, name):
        self._lhs = transition
        self._rhs = state
        self._rhs_name = name
        self.verdict = None

    def __repr__(self):
        return "d(%s) < (%s)(%s).length()" % (self._lhs, self._rhs, self._rhs_name)

    def __eq__(self, other_atom):
        if type(other_atom) is TransitionDurationLessThanStateValueLengthMixed:
            return (self._lhs == other_atom._lhs and
                    self._rhs == other_atom._rhs and
                    self._rhs_name == other_atom._rhs_name)
        else:
            return False

    def check(self, cummulative_state):
        """
        If either the RHS or LHS are None, we don't try to reach a truth value.
        But if they are both not equal to None, we check for equality.
        """
        if cummulative_state.get(0) is None or cummulative_state.get(1) is None:
            return None
        else:
            rhs_with_arithmetic = apply_arithmetic_stack(
                self._rhs._arithmetic_stack,
                cummulative_state[1][0][self._rhs_name]
            )
            return cummulative_state[0][0].total_seconds() < rhs_with_arithmetic


class TimeBetweenInInterval(Atom):
    """
    This class models the atom (timeBetween(q1, q2)._in([n, m]))
    for q1, q2 states and n, m constants.
    """

    def __init__(self, lhs, rhs, interval):
        self._lhs = lhs
        self._rhs = rhs
        self._interval = interval
        self.verdict = None

    def __repr__(self):
        return "timeBetween(%s, %s) in %s" % (self._lhs, self._rhs, self._interval)

    def __eq__(self, other_atom):
        if type(other_atom) is TimeBetweenInInterval:
            return (self._lhs == other_atom._lhs and
                    self._rhs == other_atom._rhs and
                    self._interval == other_atom._interval)

    def check(self, cummulative_state):
        """
        If either the RHS or LHS are None, we don't try to reach a truth value.
        But if they are both not equal to None, we check the values.
        """
        if cummulative_state.get(0) is None or cummulative_state.get(1) is None:
            return None
        else:
            # measure the time difference and check for containment in the interval
            return self._interval[0] <= (
                    cummulative_state[1][0]["time"] - cummulative_state[0][0]["time"]).total_seconds() <= \
                   self._interval[1]


class TimeBetweenInOpenInterval(Atom):
    """
    This class models the atom (timeBetween(q1, q2)._in((n, m))
    for q1, q2 states and n, m constants.
    """

    def __init__(self, lhs, rhs, interval):
        self._lhs = lhs
        self._rhs = rhs
        self._interval = interval
        self.verdict = None

    def __repr__(self):
        return "timeBetween(%s, %s) in %s" % (self._lhs, self._rhs, str(self._interval))

    def __eq__(self, other_atom):
        if type(other_atom) is TimeBetweenInOpenInterval:
            return (self._lhs == other_atom._lhs and
                    self._rhs == other_atom._rhs and
                    self._interval == other_atom._interval)

    def check(self, cummulative_state):
        """
        If either the RHS or LHS are None, we don't try to reach a truth value.
        But if they are both not equal to None, we check the values.
        """
        if cummulative_state.get(0) is None or cummulative_state.get(1) is None:
            return None
        else:
            # measure the time difference and check for containment in the interval
            duration = (cummulative_state[1][0]["time"] - cummulative_state[0][0]["time"]).total_seconds()
            result = self._interval[0] < duration < self._interval[1]
            return result


"""
Classes for propositional logical connectives.
"""


class LogicalOr(object):
    def __init__(self, *sub_formulas):
        """
        Given a tuple of sub formulas, sub_formulas, store it as a list in this instance.
        """
        self.operands = list(sub_formulas)
        self.true_clauses = 0
        self.parent_formula = None
        self.index_in_parent = None
        self.verdict = None

    def __repr__(self):
        return "(%s)" % (" or ".join(map(str, self.operands)))

    def __eq__(self, formula2):
        if not (type(formula2) is LogicalOr):
            return False
        if len(self.operands) != len(formula2.operands):
            return False
        for (n, operand) in enumerate(self.operands):
            if operand != formula2.operands[n]:
                return False
        return True

    def contains_formula(self, formula):
        """
        Given a formula, check whether it is contained within this formula.
        """
        for operand in self.operands:
            if operand == formula:
                return True
            elif not (formula_is_derived_from_atom(operand)) and operand.contains_formula(formula):
                return True
        return False


def lor(*sub_formulas):
    formula = LogicalOr(*sub_formulas)
    for (n, sub_formula) in enumerate(sub_formulas):
        if type(sub_formula) is LogicalAnd or type(sub_formula) is LogicalOr:
            sub_formula.parent_formula = formula
            sub_formula.index_in_parent = n
    return formula


def ifthen(formula1, formula2):
    return lor(lnot(formula1), formula2)


class LogicalAnd(object):
    def __init__(self, *sub_formulas):
        """
        Given a tuple of sub formulas, sub_formulas, store it as a list in this instance.
        """
        self.operands = list(sub_formulas)
        self.true_clauses = 0
        self.parent_formula = None
        self.index_in_parent = None
        self.verdict = None

    def __repr__(self):
        return "(%s)" % (" and ".join(map(str, self.operands)))

    def __eq__(self, formula2):
        if not (type(formula2) is LogicalAnd):
            return False
        if len(self.operands) != len(formula2.operands):
            return False
        for (n, operand) in enumerate(self.operands):
            if operand != formula2.operands[n]:
                return False
        return True

    def contains_formula(self, formula):
        """
        Given a formula, check whether it is contained within this formula.
        """
        for operand in self.operands:
            if operand == formula:
                return True
            elif not (formula_is_derived_from_atom(operand)) and operand.contains_formula(formula):
                return True
        return False


def land(*sub_formulas):
    formula = LogicalAnd(*sub_formulas)
    for (n, sub_formula) in enumerate(sub_formulas):
        if type(sub_formula) is LogicalAnd or type(sub_formula) is LogicalOr:
            sub_formula.parent_formula = formula
            sub_formula.index_in_parent = n
    return formula


class LogicalNot(object):
    def __init__(self, sub_formula):
        self.operand = sub_formula

    def __repr__(self):
        return "not(%s)" % str(self.operand)

    def __eq__(self, b):
        if type(b) is LogicalNot:
            return self.operand == b.operand
        else:
            return False

    def __hash__(self):
        return id(self)

    def contains_formula(self, formula):
        """
        Given a formula, check whether it is contained within this formula.
        """
        if self.operand == formula:
            return not (formula_is_derived_from_atom(self.operand))
        elif not (formula_is_derived_from_atom(self.operand)) and self.operand.contains_formula(formula):
            return True
        else:
            return False


def lnot(sub_formula):
    if type(sub_formula) is LogicalOr:
        or_sub_formulas = sub_formula.operands
        return land(*map(lnot, or_sub_formulas))
    elif type(sub_formula) is LogicalAnd:
        and_sub_formulas = sub_formula.operands
        return lor(*map(lnot, and_sub_formulas))
    if type(sub_formula) is LogicalNot:  # double negation
        return sub_formula.operand
    else:
        return LogicalNot(sub_formula)


def formula_is_atom(formula):
    return formula_is_derived_from_atom(formula) or (
            type(formula) is LogicalNot and formula_is_derived_from_atom(formula.operand))


def formula_is_derived_from_atom(formula):
    return Atom in type(formula).__bases__


def atom_is_positive(atom):
    return not (type(atom) is LogicalNot)


def collapsed_formula(formula):
    if type(formula) is LogicalOr:
        # we can collapse if there is at least one true clause, or if all are true or false
        if 'T' in formula.operands:
            return 'T'
    elif type(formula) is LogicalAnd:
        # we can collapse if there is a false clause, or if all are true or false
        if 'F' in formula.operands:
            return 'F'
    # check for every operand being a truth value
    if len(set(formula.operands)) == 1:
        if formula.operands[0] == 'T':
            return 'T'
        elif formula.operands[0] == 'F':
            return 'F'
    # if we've reached this point, we can't collapse the formula
    return None


def get_formula_alphabet(formula):
    """
    Given a formula, recurse through it to find the alphabet over which it is written.
    Note: the final alphabet includes positive and negative instances of every symbol
    in the alphabet.  For example, a and b is written over the alphabet {a, not a, b, not b}.
    """
    if formula_is_derived_from_atom(formula):
        # base case - the formula is an atom
        # just return the atom, and not its negative, for now
        return [formula]
    elif type(formula) is LogicalOr:
        tmp = map(lambda ops: get_formula_alphabet(ops), formula.operands)
        final = []
        for tmp_element in tmp:
            final += tmp_element
        return final
    elif type(formula) is LogicalAnd:
        tmp = map(lambda ops: get_formula_alphabet(ops), formula.operands)
        final = []
        for tmp_element in tmp:
            final += tmp_element
        return final
    elif type(formula) is LogicalNot:
        if formula_is_derived_from_atom(formula.operand):
            # if the operand is an atom, the alphabet includes the negation of this atom
            return [formula]
        else:
            return get_formula_alphabet(formula.operand)


def get_positive_formula_alphabet(formula):
    """
    If an atom is negated, include the atom and not its negative form.
    """
    alphabet = get_formula_alphabet(formula)
    for n in range(len(alphabet)):
        if type(alphabet[n]) is LogicalNot:
            alphabet[n] = alphabet[n].operand

    return alphabet


class CheckerState(object):
    """
    Wraps the dictionary that represents a monitor's state.
    The methods in this take into account the weird Python hashing behaviour
    when comparing keys.
    """

    def __init__(self, atoms):
        # initial state is None or "unobserved" for every atom
        self._state = {}
        self._atoms = atoms
        for (n, atom) in enumerate(atoms):
            self._state[n] = None

    def set_state(self, symbol):
        """
        Given an atom, set this to true in the state
        and set its negative to false
        """
        if not (symbol in self._state.keys()):
            atom_index = self._atoms.index(symbol)

        if formula_is_derived_from_atom(symbol):
            self._state[atom_index] = True
        elif type(symbol) is LogicalNot and formula_is_derived_from_atom(symbol.operand):
            self._state[atom_index] = False

    def __repr__(self):
        return str(self._state)

    def __eq__(self, other):
        if type(other) is CheckerState:
            other = other._state
        else:
            return False

        keys = self._state.keys()
        for key in keys:
            if not (key in other.keys()):
                return False
            else:
                key_index = list(other.keys()).index(key)
                value_in_other = other[list(other.keys())[key_index]]
                if value_in_other != self._state[key]:
                    return False

        # nothing has returned false, so return true
        return True


class Checker(object):

    def __init__(self, formula, optimised=False):
        """
        For now in Python 3 we use a non-optimised monitor
        because the optimisations for realistic monitors don't do much.
        """
        self._formula = formula
        self._original_formula = str(formula)
        self.observed_atoms = []
        self.atom_to_occurrence_map = {}
        self._formula_alphabet = get_formula_alphabet(formula)
        self._optimised = optimised
        self.atom_to_observation = {}
        self.atom_to_program_path = {}
        self.atom_to_state_dict = {}
        self.collapsing_atom = None
        self.collapsing_atom_sub_index = None
        self.sub_formulas = []
        # we use a tuple to record the instantiation time for each encountered bind variable
        self._monitor_instantiation_time = (datetime.datetime.now(),)

        # we now build a map from atoms in the formula to the value that the formula has for them
        # initially every atom has no observed value
        self._state = CheckerState(self._formula_alphabet)

    def get_unresolved_atoms(self, formula=None):
        """
        Recurse on the formula used by this checker to find the list of atoms that haven't been replaced by string-based truth values.
        """
        if formula is None:
            formula = self._formula

        if type(formula) is str:
            # do nothing - we don't care about strings since they are resolved atoms
            return []
        elif formula_is_derived_from_atom(formula):
            # base case - the formula is an atom
            # just return the atom, and not its negative, for now
            return [formula]
        elif type(formula) is LogicalOr:
            tmp = map(lambda ops: self.get_unresolved_atoms(ops), formula.operands)
            final = []
            for tmp_element in tmp:
                final += tmp_element
            return final
        elif type(formula) is LogicalAnd:
            tmp = map(lambda ops: self.get_unresolved_atoms(ops), formula.operands)
            final = []
            for tmp_element in tmp:
                final += tmp_element
            return final
        elif type(formula) is LogicalNot:
            if formula_is_derived_from_atom(formula.operand):
                # if the operand is an atom, the alphabet includes the negation of this atom
                return [formula]
            else:
                return self.get_unresolved_atoms(formula.operand)

    def construct_atom_formula_occurrence_map(self, formula):

        """
        Starting from the top level formula, recurse down.
        Whenever an operand is an atom (positive or negative),
        add the containing formula to the set of occurrences we have for that atom.
        """
        if type(formula) is LogicalAnd or type(formula) is LogicalOr:
            for n in range(len(formula.operands)):
                # will add formulas regardless of whether the atom is positive or negative
                if formula_is_atom(formula.operands[n]):
                    if self.atom_to_occurrence_map.get(formula.operands[n]):
                        self.atom_to_occurrence_map[formula.operands[n]].append(formula)
                    else:
                        self.atom_to_occurrence_map[formula.operands[n]] = [formula]
                else:
                    self.construct_atom_formula_occurrence_map(formula.operands[n])
        elif formula_is_atom(formula):
            if not(formula in self.sub_formulas):
              self.sub_formulas.append(formula)
              formula_index_in_sub_formulas = len(self.sub_formulas)-1
            else:
              formula_index_in_sub_formulas = self.sub_formulas.index(formula)

            if formula in self.atom_to_occurrence_map.keys():
                self.atom_to_occurrence_map[formula_index_in_sub_formulas].append(formula)
            else:
                self.atom_to_occurrence_map[formula_index_in_sub_formulas] = [formula]

    def __repr__(self):
        return "Monitor for formula %s:\n  timestamps: %s\n state: %s\n  verdict: %s" % (
            self._original_formula, str(self._monitor_instantiation_time), str(self._formula), self._formula.verdict)

    def check_atom_truth_value(self, atom, value):
        """
        Given an atom, an observation and, if the atom is mixed,
        an indication of whether the observation is for the lhs or rhs
        """
        check_value = atom.check(value)
        if check_value == True:
            result = self.check(self._formula, atom)
        elif check_value == False:
            result = self.check(self._formula, lnot(atom))
        elif check_value == None:
            # mixed atoms can still be unconclusive if only part of them has been given an observation
            # in this case, the atom maintains state so no changes are required to the formula tree
            result = None
        return result

    def process_atom_and_value(self, atom, observation_time, observation_end_time, value, atom_index, atom_sub_index,
                               force_monitor_update=False, inst_point_id=None,
                               program_path=None, state_dict=None):
        """
        Given an atom and a value, update this monitor.
        """
        # record the observation, path and state
        # we have to use lists to be able to capture  multiple observations required for mixed atoms
        if not (self.atom_to_observation.get(atom_index)):
            self.atom_to_observation[atom_index] = {}
            self.atom_to_program_path[atom_index] = {}
            self.atom_to_state_dict[atom_index] = {}

        if not (self.atom_to_observation[atom_index].get(atom_sub_index)):
            self.atom_to_observation[atom_index][atom_sub_index] =\
                (value, inst_point_id, observation_time, observation_end_time)
            # self.atom_to_program_path[atom_index][atom_sub_index] = [v for v in program_path]
            # we deal with integer indices now, so no need to copy a list
            self.atom_to_program_path[atom_index][atom_sub_index] = program_path
            self.atom_to_state_dict[atom_index][atom_sub_index] = state_dict
        else:
            # the observation has already been processed - no need to do anything
            return

        initial_verdict = self._formula.verdict

        result = self.check_atom_truth_value(atom, self.atom_to_observation[atom_index])

        final_verdict = self._formula.verdict

        if initial_verdict != final_verdict:
            # for each monitor, this branch can only ever be traversed once
            self.collapsing_atom = atom
            self.collapsing_atom_sub_index = atom_sub_index

        return result

    def check_optimised(self, symbol, force_monitor_update=False):
        """
        Given a symbol, find the formula occurrences that contain this symbol.
        For each of the occurrences, replace the atom with the appropriate value (T or F).
        Then loop up through the parents while each successive parent can be collapsed to a truth value.
        """

        if not (force_monitor_update) and not (self._formula.verdict is None):
            return self._formula.verdict

        if symbol in self.observed_atoms or lnot(symbol) in self.observed_atoms:
            return
        else:
            self.observed_atoms.append(symbol)

        # NOTE: BE AWARE THAT THE ALPHABET USED TO INITIALLY POPULATE _STATE DOES NOT INCLUDE NEGATIVES
        # OF EVERY ATOM

        # update state for the monitoring algorithm to use
        self._state.set_state(symbol)

        # temporary fix for Python 3 - the long term solution needs to be more robust
        index_of_symbol_in_sub_formulas = self.sub_formulas.index(symbol)
        if index_of_symbol_in_sub_formulas in self.atom_to_occurrence_map.keys():
            positives = self.atom_to_occurrence_map.get(index_of_symbol_in_sub_formulas)
        else:
            positives = []

        negatives = []

        all_occurences = positives + negatives

        for occurrence in all_occurences:
            # find the position of the atom in the subformula
            index_in_formula = 0
            # if the formula to which this atom belongs is an atom,
            # this can only happen when a formula consists of only an atom
            if formula_is_atom(occurrence):
                if formula_is_derived_from_atom(symbol):
                    if formula_is_derived_from_atom(occurrence):
                        self._formula.verdict = True
                        return True
                    else:
                        self._formula.verdict = False
                        return False
                else:
                    if formula_is_derived_from_atom(occurrence):
                        self._formula.verdict = False
                        return False
                    else:
                        self._formula.verdict = True
                        return True
            else:
                for n in range(len(occurrence.operands)):
                    if occurrence.operands[n] in [symbol, lnot(symbol)]:
                        index_in_formula = n

                # replace the atom we've observed accordingly
                if formula_is_derived_from_atom(symbol):
                    if formula_is_derived_from_atom(occurrence.operands[index_in_formula]):
                        occurrence.operands[index_in_formula] = 'T'
                    else:
                        occurrence.operands[index_in_formula] = 'F'
                else:
                    if formula_is_derived_from_atom(occurrence.operands[index_in_formula]):
                        occurrence.operands[index_in_formula] = 'F'
                    else:
                        occurrence.operands[index_in_formula] = 'T'

                # iterate up through the tree, collapsing sub-formulas to truth values as far as we can
                current_formula = occurrence
                current_collapsed_value = collapsed_formula(current_formula)
                # iterate while the current formula is collapsible to a truth value
                while not (current_collapsed_value is None):
                    if not (current_formula.parent_formula is None):
                        current_formula.parent_formula.operands[
                            current_formula.index_in_parent] = current_collapsed_value
                        current_formula = current_formula.parent_formula
                        current_collapsed_value = collapsed_formula(current_formula)
                    else:
                        # we have collapsed the root to a truth value
                        truth_value_to_boolean = {'T': True, 'F': False, '?': None}
                        self._formula.verdict = truth_value_to_boolean[current_collapsed_value]
                        return self._formula.verdict

        return None

    def check(self, formula, symbol, level=0):
        """
        Given a formula and a symbol that is true,
        for each operand of the current formula, if the operand corresponds to the symbol,
        replace it with true or false.
        If replaced by true and the formula is a conjunction, remove the atom from the conjunction,
            then check for the length of the removing list of operands.
            If the length is zero, return true
        If replaced by false and the formula is a conjunction, return false.
        If replaced by true and the formula is a disjunction, return true.
        If replaced by false and the formula is a disjunction, remove this atom from the list of operands.

        If not an atom, recurse on the sub-formula.
        """

        if not (self._formula.verdict is None):
            return self._formula.verdict

        self.observed_atoms.append(symbol)

        sub_verdict = None

        indent = "    " * level

        if type(formula) is LogicalAnd or type(formula) is LogicalOr:
            # first check if the disjunction or conjunction can be immediately
            # collapsed to a truth value
            if type(formula) is LogicalAnd:
                if 'F' in formula.operands:
                    if level == 0:
                        self._formula.verdict = False
                    return False
            elif type(formula) is LogicalOr:
                if 'T' in formula.operands:
                    if level == 0:
                        self._formula.verdict = True
                    return True

            if len(set(formula.operands)) == 1:
                if formula.operands[0] == 'T':
                    if level == 0:
                        self._formula.verdict = True
                    return True
                elif formula.operands[0] == 'F':
                    if level == 0:
                        self._formula.verdict = False
                    return False

            # if not, iterate through the operands
            for n in range(len(formula.operands)):
                if not (formula.operands[n] in ['T', 'F']):
                    if formula_is_atom(formula.operands[n]):
                        if ((formula_is_derived_from_atom(formula.operands[n]) and formula_is_derived_from_atom(
                                symbol) and formula.operands[n] == symbol)
                                or (type(formula.operands[n]) is LogicalNot and type(symbol) is LogicalNot and
                                    formula.operands[n] == symbol)):
                            formula.operands[n] = 'T'
                            if type(formula) is LogicalOr:
                                formula = 'T'
                                if level == 0:
                                    self._formula.verdict = True
                                return True
                            elif type(formula) is LogicalAnd:
                                formula.true_clauses += 1
                                if formula.true_clauses == len(formula.operands):
                                    formula = 'T'
                                    if level == 0:
                                        self._formula.verdict = True
                                    return True
                        elif ((formula_is_derived_from_atom(formula.operands[n]) and type(symbol) is LogicalNot and
                               formula.operands[n] == symbol.operand)
                              or (type(formula.operands[n]) is LogicalNot and formula.operands[n].operand == symbol)):
                            formula.operands[n] = 'F'
                            if type(formula) is LogicalAnd:
                                formula = 'F'
                                if level == 0:
                                    self._formula.verdict = False
                                return False
                    else:
                        sub_verdict = self.check(formula.operands[n], symbol, level + 1)
                        if sub_verdict:
                            formula.operands[n] = 'T'
                            if type(formula) is LogicalOr:
                                formula = 'T'
                                if level == 0:
                                    self._formula.verdict = True
                                return True
                            elif type(formula) is LogicalAnd:
                                formula.true_clauses += 1
                                if formula.true_clauses == len(formula.operands):
                                    formula = 'T'
                                    if level == 0:
                                        self._formula.verdict = True
                                    return True
                        elif sub_verdict == False:  # explicitly not including None
                            formula.operands[n] = 'F'
                            if type(formula) is LogicalAnd:
                                formula = 'F'
                                if level == 0:
                                    self._formula.verdict = False
                                return False
            return sub_verdict
        elif type(formula) is LogicalNot:
            if formula_is_derived_from_atom(formula.operand) and formula.operand == symbol:
                if level == 0:
                    self._formula.verdict = False
                return False
            elif type(formula.operand) is LogicalNot and formula.operand.operand == symbol:
                if level == 0:
                    self._formula.verdict = True
                return True
        elif formula_is_derived_from_atom(formula):
            if formula == symbol:
                if level == 0:
                    self._formula.verdict = True
                return True
            else:
                if level == 0:
                    self._formula.verdict = False
                return False


def new_monitor(formula, optimised=False):
    return Checker(formula, optimised)
