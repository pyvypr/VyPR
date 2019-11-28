from __future__ import print_function

"""def print(*s):
    pass"""
"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""
"""

Each possible atom has its own class, ie:

StateValueInInterval - models the atom (s(x) in I) for some state s, a name x and an interval (list) I.
TransitionDurationInInterval - models the atom (d(delta t) in I) for some transition delta t and an interval (list) I.

Atoms are generated once states or transitions have been described by calling 

"""

import inspect
# be careful with versions here...
from collections import OrderedDict

from VyPR.monitor_synthesis import formula_tree

"""
General structure-building classes and methods.
"""


class If(object):
    """
    Upon instantiation, this models an incomplete formula - calling then() returns a complete formula tree.
    This is basically syntactic sugar.
    """

    def __init__(self, formula):
        self._test = formula

    def then(self, formula):
        return formula_tree.ifthen(self._test, formula)

    def __repr__(self):
        return "Incomplete formula: %s" % self._test


class Forall(object):
    """
    Models a single instance of forall quantification.
    Defines a method called Forall that can be used multiple times to construct
    a sequence of quantifiers.
    This class should always hold the current quantification structure.
    """

    def __init__(self, is_first=True, bind_variables=None, **bind_variable):
        """
        Given a bind variable (bind_variable_name is the variable name,
        and bind_variable_value is either StaticState or StaticTransition),
        check that, if is_first is true, the bind variable is independent.
        """

        bind_variable_name = bind_variable.keys()[0]
        bind_variable_obj = bind_variable.values()[0]

        self.bind_variables = bind_variables

        """
        resolve the bind variable on which this one depends
        this consists of using the current bind variable name
        to reference the actual bind variable value in the bind_variables dictionary
        """
        if not (is_first):
            bind_variable_obj._required_binding = \
                self.bind_variables[bind_variable_obj._required_binding]

        bind_variable_final = bind_variable_obj.complete_instantiation(bind_variable_name)
        if self.bind_variables is None:
            self.bind_variables = OrderedDict({bind_variable_name: bind_variable_final})
        else:
            self.bind_variables.update({bind_variable_name: bind_variable_final})

        self._bind_variables = self.bind_variables.values()

        # defined by calling Formula
        self._formula = None

        # this is set to True when self.Formula() is called
        # it's used to decide whether arithmetic operations should be
        # added to atoms' stacks or not, to prevent double evaluation
        self._instantiation_complete = False

    def __repr__(self):
        if self._formula is None:
            return "Forall(%s)" % self.bind_variables
        else:
            return "Forall(%s).Formula(%s)" % \
                   (self.bind_variables, self.get_formula_instance())

    def Forall(self, **bind_variable):
        # return an instance
        return Forall(
            is_first=False,
            bind_variables=self.bind_variables,
            **bind_variable
        )

    def get(self, key):
        return self.bind_variables[key]

    # syntactic sugar
    def Check(self, formula_lambda):
        return self.Formula(formula_lambda)

    def Formula(self, formula_lambda):
        """
        Store the formula lambda, which itself returns a formula when given
        bind variables, for later use.
        """
        self._formula = formula_lambda
        # generate instantiated formula to compute its atoms
        self._formula_atoms = \
            formula_tree.get_positive_formula_alphabet(self.get_formula_instance(
                first_time=True
            ))
        self._instantiation_complete = True
        return self

    def get_formula_instance(self, first_time=False):
        """
        Instantiate the formula using the lambda stored.
        """
        # use the arguments of the lambda function
        argument_names = inspect.getargspec(self._formula).args
        bind_variables = map(
            lambda arg_name: self.bind_variables[arg_name],
            argument_names
        )
        if first_time:
            # enable "_arithmetic_build" flag in bind variables
            # so arithmetic operations are added
            for bind_variable in bind_variables:
                bind_variable._arithmetic_build = True
        formula = self._formula(*bind_variables)
        # switch off arithmetic build flags
        if first_time:
            for bind_variable in bind_variables:
                bind_variable._arithmetic_build = False
        return formula


class changes(object):
    """
    Syntactic sugar for specifications.
    """

    def __init__(self, name_changed, after=None, treat_as_ref=False):
        self._name = None
        self._name_changed = name_changed
        self._required_binding = after
        self._treat_as_ref = treat_as_ref

    def complete_instantiation(self, bind_variable_name):
        return StaticState(
            bind_variable_name,
            self._name_changed,
            None,
            self._required_binding,
            self._treat_as_ref
        )


class calls(object):
    """
    Syntactic sugar for specifications.
    """

    def __init__(self, operates_on, after=None, record=None):
        self._operates_on = operates_on
        self._required_binding = after
        self._record = record

    def complete_instantiation(self, bind_variable_name):
        return StaticTransition(
            bind_variable_name,
            self._operates_on,
            None,
            self._required_binding,
            self._record
        )


class state_after_line(object):
    """
    Syntactic sugar for specifications.
    """

    def __init__(self, coordinates, after=None):
        self._instruction_coordinates = coordinates
        self._required_binding = after

    def complete_instantiation(self, bind_variable_name):
        return StaticState(
            bind_variable_name,
            None,
            self._instruction_coordinates,
            self._required_binding,
            None
        )


"""
Classes and methods for describing states and transitions.
Methods labelled with "Generates an atom." takes the state
or transition so far and builds a predicate over it to generate an atom.
"""


def requires_state_or_transition(obj):
    """
    Used to determine whether a value for the RHS of an atom
    is a primitive type that we don't need to observe anything for,
    or derived from a state or transition
    """
    return type(obj) in [StateValue, StaticStateLength]


class StaticState(object):
    """
    Models a state attained by the monitored program at runtime.
    """

    def __init__(self, bind_variable_name, name_changed, instruction_coordinates, uses=None, treat_as_ref=False):
        self._bind_variable_name = bind_variable_name
        self._name = None
        self._name_changed = name_changed
        self._instruction_coordinates = instruction_coordinates
        self._required_binding = uses
        self._treat_as_ref = treat_as_ref
        # this will be added to if a function is applied
        # to the measurement in the PyCFTL specification.
        self._arithmetic_stack = []
        self._arithmetic_build = False

    def __call__(self, name):
        return StateValue(self, name)

    def next_call(self, function, record=None):
        """
        record will only matter for the final instrumentation
        points if there is nesting.  It is a list of variable
        values to record at the start of the next call to function.
        """
        return NextStaticTransition(self, function, record=record)

    def __repr__(self):
        if self._required_binding:
            return "%s = StaticState(changes=%s, uses=%s)" % \
                   (self._bind_variable_name, self._name_changed,
                    self._required_binding)
        else:
            return "%s = StaticState(changes=%s)" % \
                   (self._bind_variable_name, self._name_changed)

    def __eq__(self, other):
        return (type(other) is StaticState and
                self._bind_variable_name == other._bind_variable_name and
                self._name == other._name and
                self._name_changed == other._name_changed and
                self._required_binding == other._required_binding)


class SourceStaticState(StaticState):
    """
    Models the source state of a transition.
    """

    def __init__(self, outgoing_transition):
        self._outgoing_transition = outgoing_transition

    def __repr__(self):
        return "(%s).input()" % self._outgoing_transition

    def __eq__(self, other):
        return (type(other) is SourceStaticState and
                self._outgoing_transition == other._outgoing_transition)


class DestinationStaticState(StaticState):
    """
    Models the destination state of a transition.
    """

    def __init__(self, incoming_transition):
        self._incoming_transition = incoming_transition

    def __repr__(self):
        return "(%s).result()" % self._incoming_transition

    def __eq__(self, other):
        return (type(other) is DestinationStaticState and
                self._incoming_transition == other._incoming_transition)


class StateValue(object):
    """
    Models the value to which some state maps a program variable.
    """

    def __init__(self, state, name):
        self._state = state
        self._name = name

    def _in(self, interval):
        """
        Generates an atom.
        """
        return formula_tree.StateValueInInterval(
            self._state,
            self._name,
            interval
        )

    def equals(self, value):
        """
        Generates an atom.
        """
        if requires_state_or_transition(value):
            # the RHS of the comparison requires observation of another state or transition
            # so we use a different class to deal with this
            return formula_tree.StateValueEqualToMixed(
                self._state,
                self._name,
                value._state,
                value._name
            )
        else:
            # the RHS of the comparison is just a constant
            return formula_tree.StateValueEqualTo(
                self._state,
                self._name,
                value
            )

    def length(self):
        return StateValueLength(self._state, self._name)

    def type(self):
        return StateValueType(self._state, self._name)

    """
    Arithmetic overloading is useful for mixed atoms
    when observed quantities are being compared to each other.
    """

    def __mul__(self, value):
        """
        Given a constant (we assume this for now),
        add an object to the arithmetic stack so it can be applied
        later when values are checked.
        """
        if self._state._arithmetic_build:
            print("EVALUATING MULTIPLICATION OF STATE VALUE")
            self._state._arithmetic_stack.append(formula_tree.ArithmeticMultiply(value))
        return self

    def __add__(self, value):
        if self._state._arithmetic_build:
            self._state._arithmetic_stack.append(formula_tree.ArithmeticAdd(value))
        return self

    def __sub__(self, value):
        if self._state._arithmetic_build:
            self._state._arithmetic_stack.append(formula_tree.ArithmeticSubtract(value))
        return self

    def __truediv__(self, value):
        if self._state._arithmetic_build:
            self._state._arithmetic_stack.append(formula_tree.ArithmeticTrueDivide(value))
        return self


class StateValueLength(object):
    """
    Models the length being measured of a value given by a state.
    """

    def __init__(self, state, name):
        self._state = state
        self._name = name

    def _in(self, interval):
        """
        Generates an atom.
        """
        return formula_tree.StateValueLengthInInterval(
            self._state,
            self._name,
            interval
        )

    """
    Arithmetic overloading is useful for mixed atoms
    when observed quantities are being compared to each other.
    """

    def __mul__(self, value):
        """
        Given a constant (we assume this for now),
        add an object to the arithmetic stack so it can be applied
        later when values are checked.
        """
        if self._state._arithmetic_build:
            print("EVALUATING MULTIPLICATION OF STATE VALUE")
            self._state._arithmetic_stack.append(formula_tree.ArithmeticMultiply(value))
        return self

    def __add__(self, value):
        if self._state._arithmetic_build:
            self._state._arithmetic_stack.append(formula_tree.ArithmeticAdd(value))
        return self

    def __sub__(self, value):
        if self._state._arithmetic_build:
            self._state._arithmetic_stack.append(formula_tree.ArithmeticSubtract(value))
        return self

    def __truediv__(self, value):
        if self._state._arithmetic_build:
            self._state._arithmetic_stack.append(formula_tree.ArithmeticTrueDivide(value))
        return self


class StateValueType(object):
    """
    Models the length being measured of a value given by a state.
    """

    def __init__(self, state, name):
        self._state = state
        self._name = name

    def equals(self, value):
        """
        Generates an atom.
        """
        return formula_tree.StateValueTypeEqualTo(
            self._state,
            self._name,
            value
        )


class StaticTransition(object):
    """
    Models transition that occurs during a program's runtime.
    """

    def __init__(self, bind_variable_name, operates_on, instruction_coordinates, uses=None, record=None):
        self._bind_variable_name = bind_variable_name
        self._operates_on = operates_on
        self._instruction_coordinates = instruction_coordinates
        self._required_binding = uses
        self._record = record

    def duration(self):
        return Duration(self)

    def next_call(self, function, record=None):
        """
        record will only matter for the final instrumentation points if there is nesting.
        It is a list of variable values to record at the start of the next call to function.
        """
        return NextStaticTransition(self, function, record=record)

    def input(self):
        return SourceStaticState(self)

    def result(self):
        return DestinationStaticState(self)

    def __repr__(self):
        if self._required_binding:
            if self._record:
                return "%s = StaticTransition(operates_on=%s, uses=%s, record=%s)" % \
                       (self._bind_variable_name, self._operates_on,
                        self._required_binding, str(self._record))
            else:
                return "%s = StaticTransition(operates_on=%s, uses=%s)" % \
                       (self._bind_variable_name, self._operates_on,
                        self._required_binding)
        else:
            if self._record:
                return "%s = StaticTransition(operates_on=%s, record=%s)" % \
                       (self._bind_variable_name, self._operates_on, str(self._record))
            else:
                return "%s = StaticTransition(operates_on=%s)" % \
                       (self._bind_variable_name, self._operates_on)

    def __eq__(self, other):
        return (type(other) is StaticTransition and
                self._bind_variable_name == other._bind_variable_name and
                self._operates_on == other._operates_on and
                self._required_binding == other._required_binding)


class NextStaticTransition(StaticTransition):
    """
    Models a next transition obtained from another static object.
    """

    def __init__(self, static_object, operates_on, record=None):
        self._centre = static_object
        self._operates_on = operates_on
        self._record = record

    def __repr__(self):
        if self._record:
            return "(%s).next_call(%s, record=%s)" % \
                   (str(self._centre), self._operates_on, str(self._record))
        else:
            return "(%s).next_call(%s)" % (str(self._centre), self._operates_on)

    def __eq__(self, other):
        return (type(other) is NextStaticTransition and
                self._centre == other._centre and
                self._operates_on == other._operates_on)


class Duration(object):
    """
    Models the duration of a transition.
    """

    def __init__(self, transition):
        self._transition = transition

    def _in(self, interval):
        """
        Generates an atom.
        """
        if type(interval) is list:
            return formula_tree.TransitionDurationInInterval(
                self._transition,
                interval
            )
        elif type(interval) is tuple:
            return formula_tree.TransitionDurationInOpenInterval(
                self._transition,
                interval
            )
        else:
            raise Exception("Duration predicate wasn't defined properly.")

    def __lt__(self, value):
        """
        Generates an atom.
        This is, for now, reserved for comparison of duration to other measurable quantities.
        """
        if type(value) is StateValue:
            return formula_tree.TransitionDurationLessThanStateValueMixed(
                self._transition,
                value._state,
                value._name
            )
        elif type(value) is StateValueLength:
            return formula_tree.TransitionDurationLessThanStateValueLengthMixed(
                self._transition,
                value._state,
                value._name
            )
        elif type(value) is Duration:
            return formula_tree.TransitionDurationLessThanTransitionDurationMixed(
                self._transition,
                value._transition,
            )


"""
Syntactic sugar for time between states.
"""


def timeBetween(state1, state2):
    return TimeBetweenStates(state1, state2)


class TimeBetweenStates(object):
    """
    Models the time between two states.
    """

    def __init__(self, lhs, rhs):
        self._lhs = lhs
        self._rhs = rhs

    def _in(self, interval):
        """
        Generates an atom.
        """
        if type(interval) is list:
            return formula_tree.TimeBetweenInInterval(
                self._lhs,
                self._rhs,
                interval
            )
        elif type(interval) is tuple:
            return formula_tree.TimeBetweenInOpenInterval(
                self._lhs,
                self._rhs,
                interval
            )
        else:
            raise Exception("TimeBetween predicate wasn't defined properly.")


def composition_sequence_from_value(sequence, current_operator):
    while not (type(current_operator) in [StaticState, StaticTransition]):
        sequence.append(current_operator)
        if type(current_operator) is SourceStaticState:
            current_operator = current_operator._outgoing_transition
        elif type(current_operator) is DestinationStaticState:
            current_operator = current_operator._incoming_transition
        elif type(current_operator) is NextStaticTransition:
            current_operator = current_operator._centre

    # add the input bind variable to the composition sequence
    sequence.append(current_operator)
    return sequence


def derive_composition_sequence(atom):
    """
    Given an atom, derive the sequence of operator compositions.
    """

    print("deriving composition sequence for atom %s" % atom)

    # if the atom has an LHS and an RHS, there must be two composition sequences

    sequence = [atom]
    if type(atom) == formula_tree.LogicalNot:
        print("detected negation - removing")
        current_operator = atom.operand
    else:
        current_operator = atom

    if type(atom) in [formula_tree.StateValueEqualToMixed,
                      formula_tree.TransitionDurationLessThanTransitionDurationMixed,
                      formula_tree.TransitionDurationLessThanStateValueMixed,
                      formula_tree.TransitionDurationLessThanStateValueLengthMixed,
                      formula_tree.TimeBetweenInInterval,
                      formula_tree.TimeBetweenInOpenInterval]:

        # atom is mixed - two composition sequences

        lhs = atom._lhs
        print(lhs)
        rhs = atom._rhs
        print(rhs)

        lhs_sequence = [atom]
        rhs_sequence = [atom]

        comp_sequence_lhs = composition_sequence_from_value(lhs_sequence, lhs)
        comp_sequence_rhs = composition_sequence_from_value(rhs_sequence, rhs)

        print("final composition sequence for lhs is %s" % str(comp_sequence_lhs))
        print("final composition sequence for rhs is %s" % str(comp_sequence_rhs))

        return {"lhs": comp_sequence_lhs, "rhs": comp_sequence_rhs}

    else:

        # atom is simple - just one composition sequence

        if type(current_operator) == formula_tree.TransitionDurationInInterval:
            current_operator = current_operator._transition
        elif type(current_operator) == formula_tree.StateValueEqualTo:
            current_operator = current_operator._state
        elif type(current_operator) == formula_tree.StateValueLengthInInterval:
            current_operator = current_operator._state
        elif type(current_operator) == formula_tree.StateValueInInterval:
            current_operator = current_operator._state
        elif type(current_operator) == formula_tree.StateValueTypeEqualTo:
            current_operator = current_operator._state

        sequence = composition_sequence_from_value(sequence, current_operator)

        print("final composition sequence is %s" % str(sequence))

        return sequence


def get_base_variable(atom):
    """
    Given an atom, find the StaticState or StaticTransition from which it is derived.
    """

    composition_sequence = derive_composition_sequence(atom)
    # if the atom was mixed, we may have two base variables
    # otherwise we just have one
    if type(composition_sequence) is dict:
        return [composition_sequence["lhs"][-1], composition_sequence["rhs"][-1]]
    else:
        return composition_sequence[-1]
