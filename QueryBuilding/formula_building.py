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

"""

import inspect
# be careful with versions here...
from collections import OrderedDict
import ast

from VyPR.monitor_synthesis import formula_tree

"""
Function selection.
"""


class Module(object):
    """
    Used to point to a module/function in specifications.
    """

    def __init__(self, module_name):
        self._module_name = module_name

    def Function(self, function_name):
        self._function_name = function_name
        return self


class Functions(object):
    """
    Given as keys in the initial specification config file dictionary by the developer.
    """

    def __init__(self, **parameter_dictionary):
        """
        Parameters given here, with their values, act as criteria to select a set of functions in a project.
        Multiple parameter values will be used in conjunction.
        """
        # set the parameters given as object parameters that can be used in the search performed by instrumentation
        self.criteria_dict = parameter_dictionary

    def is_satisfied_by(self, function_ast, scfg):
        """
        Given a Function AST, decide whether the criteria defined by this instance are satisfied.
        :param function_ast:
        :param scfg:
        :return: True or False
        """
        for criterion_name in self.criteria_dict:
            if criterion_name == "containing_call_of":
                edges = scfg.edges
                call_found = False
                for edge in edges:
                    if edge._operates_on and self.criteria_dict[criterion_name] in edge._operates_on:
                        call_found = True
                # if no call was found, this criterion has not been met,
                # so return False because the conjunction is broken
                if not call_found:
                    return False
            elif criterion_name == "containing_change_of":
                vertices = scfg.vertices
                change_found = False
                for vertex in vertices:
                    if self.criteria_dict[criterion_name] in vertex._name_changed:
                        change_found = True
                    elif hasattr(vertex, "_structure_obj"):
                        if type(vertex._structure_obj) is ast.For:
                            if type(vertex._structure_obj.target) is ast.Tuple:
                                if (self.criteria_dict[criterion_name] in
                                        map(lambda item: item.id, vertex._structure_obj.target)):
                                    change_found = True
                            else:
                                if self.criteria_dict[criterion_name] == vertex._structure_obj.target.id:
                                    change_found = True
                # if no change was found, this criterion has not been met,
                # so return False because the conjunction is broken
                if not (change_found):
                    return False
        # we found no evidence against satisfaction, so return True
        return True

    def __repr__(self):
        return "<%s>" % str(self.criteria_dict)


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

        # note: this is a quick fix, but needs to be modified
        # since dictionaries don't guarantee order
        bind_variable_name = list(bind_variable.keys())[0]
        #bind_variable_obj = bind_variable.values()[0]
        bind_variable_obj = bind_variable[bind_variable_name]

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
            return "Forall(%s).Check(%s)" % \
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
        bind_variables = list(map(
            lambda arg_name: self.bind_variables[arg_name],
            argument_names
        ))
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
    return type(obj) in [StateValue, StateValueLength]


class PossiblyNumeric(object):
    """
    Models a quantity that one can perform arithmetic on.
    Should be inherited by any class that wants a user to be able to perform arithmetic with it.
    """

    def __mul__(self, value):
        """
        Given a constant (we assume this for now),
        add an object to the arithmetic stack so it can be applied
        later when values are checked.
        """
        if type(value) in [int, float]:
            base_variable = composition_sequence_from_value([self._state], self._state)[-1]
            if base_variable._arithmetic_build:
                self._state._arithmetic_stack.append(formula_tree.ArithmeticMultiply(value))
            return self
        else:
            raise Exception("Value used to multiply quantity %s must be of type int or float." % self)

    def __add__(self, value):
        if type(value) in [int, float]:
            base_variable = composition_sequence_from_value([self._state], self._state)[-1]
            if base_variable._arithmetic_build:
                self._state._arithmetic_stack.append(formula_tree.ArithmeticAdd(value))
            return self
        else:
            raise Exception("Value added to quantity %s must be of type int or float." % self)

    def __sub__(self, value):
        if type(value) in [int, float]:
            base_variable = composition_sequence_from_value([self._state], self._state)[-1]
            if base_variable._arithmetic_build:
                self._state._arithmetic_stack.append(formula_tree.ArithmeticSubtract(value))
            return self
        else:
            raise Exception("Value subtracted from quantity %s must be of type int or float." % self)

    def __truediv__(self, value):
        if type(value) in [int, float] and value != 0:
            base_variable = composition_sequence_from_value([self._state], self._state)[-1]
            if base_variable._arithmetic_build:
                self._state._arithmetic_stack.append(formula_tree.ArithmeticTrueDivide(value))
            return self
        else:
            raise Exception("Value used to divide quantity %s must be non-zero and of type int or float." % self)


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
        if type(name) is str:
            return StateValue(self, name)
        else:
            raise Exception("Value given to state '%s' must be of type str, not %s." % (self, name.__class__.__name__))

    def next_call(self, function, record=None):
        """
        record will only matter for the final instrumentation
        points if there is nesting.  It is a list of variable
        values to record at the start of the next call to function.
        """
        if type(function) is str:
            return NextStaticTransition(self, function, record=record)
        else:
            raise Exception("Value given to (%s).next_call must be of type str, not %s." %
                            (self, function.__class__.__name__))

    def __repr__(self):
        if self._required_binding:
            return "%s = changes('%s', uses=%s)" % \
                   (self._bind_variable_name, self._name_changed,
                    self._required_binding)
        else:
            return "%s = changes('%s')" % \
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
        self._arithmetic_stack = []
        self._arithmetic_build = False

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
        self._arithmetic_stack = []
        self._arithmetic_build = False

    def __repr__(self):
        return "(%s).result()" % self._incoming_transition

    def __eq__(self, other):
        return (type(other) is DestinationStaticState and
                self._incoming_transition == other._incoming_transition)


class StateValue(PossiblyNumeric):
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
        if type(interval) is list and len(interval) == 2:
            return formula_tree.StateValueInInterval(
                self._state,
                self._name,
                interval
            )
        elif type(interval) is tuple and len(interval) == 2:
            return formula_tree.StateValueInOpenInterval(
                self._state,
                self._name,
                interval
            )
        else:
            raise Exception("Value of type %s given to _in operator with %s('%s') is not supported." %
                            (interval.__class__.__name__, self._state, self._name))

    def __lt__(self, value):
        """
        Generates an atom.
        """
        if type(value) is int:
            return formula_tree.StateValueInOpenInterval(
                self._state,
                self._name,
                [0, value]
            )
        elif type(value) is StateValue:
            return formula_tree.StateValueLessThanEqualStateValueMixed(
                self._state,
                self._name,
                value._state,
                value._name
            )
        else:
            raise Exception("Value of type %s given to < comparison with %s('%s') is not supported." %
                            (value.__class__.__name__, self._state, self._name))

    def __le__(self, value):
        """
        Generates an atom.
        """
        if type(value) is int:
            return formula_tree.StateValueInInterval(
                self._state,
                self._name,
                [0, value]
            )
        elif type(value) is StateValue:
            return formula_tree.StateValueLessThanStateValueMixed(
                self._state,
                self._name,
                value._state,
                value._name
            )
        else:
            raise Exception("Value of type %s given to < comparison with %s('%s') is not supported." %
                            (value.__class__.__name__, self._state, self._name))

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


class StateValueLength(PossiblyNumeric):
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
        if type(interval) is list and len(interval) == 2:
            return formula_tree.StateValueLengthInInterval(
                self._state,
                self._name,
                interval
            )
        elif type(interval) is tuple and len(interval) == 2:
            return formula_tree.StateValueLengthInOpenInterval(
                self._state,
                self._name,
                interval
            )
        else:
            raise Exception("Value of type %s given to _in comparison with %s('%s').length() is not supported." %
                            (interval.__class__.__name__, self._state, self._name))

    """
    Overload comparison operators.
    """

    def __lt__(self, value):
        """
        Generates an atom.
        """
        if type(value) is int:
            return formula_tree.StateValueLengthInOpenInterval(
                self._state,
                self._name,
                [0, value]
            )
        elif type(value) is StateValueLength:
            return formula_tree.StateValueLengthLessThanStateValueLengthMixed(
                self._state,
                self._name,
                value._state,
                value._name
            )
        else:
            raise Exception("Value of type %s given to _in comparison with %s('%s').length() is not supported." %
                            (value.__class__.__name__, self._state, self._name))

    def __le__(self, value):
        """
        Generates an atom.
        """
        if type(value) is int:
            return formula_tree.StateValueLengthInInterval(
                self._state,
                self._name,
                [0, value]
            )
        elif type(value) is StateValueLength:
            return formula_tree.StateValueLengthLessThanEqualStateValueLengthMixed(
                self._state,
                self._name,
                value._state,
                value._name
            )
        else:
            raise Exception("Value of type %s given to _in comparison with %s('%s').length() is not supported." %
                            (value.__class__.__name__, self._state, self._name))


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
        if type(function) is str:
            return NextStaticTransition(self, function, record=record)
        else:
            raise Exception("Value given to state '%s' must be of type str, not %s." %
                            (self, function.__class__.__name__))

    def input(self):
        return SourceStaticState(self)

    def result(self):
        return DestinationStaticState(self)

    def __repr__(self):
        if self._required_binding:
            if self._record:
                return "%s = calls('%s', uses=%s, record=%s)" % \
                       (self._bind_variable_name, self._operates_on,
                        self._required_binding, str(self._record))
            else:
                return "%s = calls('%s', uses=%s)" % \
                       (self._bind_variable_name, self._operates_on,
                        self._required_binding)
        else:
            if self._record:
                return "%s = calls('%s', record=%s)" % \
                       (self._bind_variable_name, self._operates_on, str(self._record))
            else:
                return "%s = calls('%s')" % \
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
            return "(%s).next_call('%s', record=%s)" % \
                   (str(self._centre), self._operates_on, str(self._record))
        else:
            return "(%s).next_call('%s')" % (str(self._centre), self._operates_on)

    def __eq__(self, other):
        return (type(other) is NextStaticTransition and
                self._centre == other._centre and
                self._operates_on == other._operates_on)


class Duration(PossiblyNumeric):
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
            raise Exception("Value of type %s given to _in comparison on %s is not supported." %
                            (interval.__class__.__name__, self._transition))

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
        elif type(value) is int:
            return formula_tree.TransitionDurationInOpenInterval(
                self._transition,
                [0, value]
            )
        else:
            raise Exception("Value of type %s given to < comparison on %s is not supported." %
                            (value.__class__.__name__, self._transition))

    def __le__(self, value):
        """
        Generates an atom.
        """
        if type(value) is StateValue:
            return formula_tree.TransitionDurationLessThanEqualStateValueMixed(
                self._transition,
                value._state,
                value._name
            )
        elif type(value) is StateValueLength:
            return formula_tree.TransitionDurationLessThanEqualStateValueLengthMixed(
                self._transition,
                value._state,
                value._name
            )
        elif type(value) is Duration:
            return formula_tree.TransitionDurationLessThanEqualTransitionDurationMixed(
                self._transition,
                value._transition,
            )
        elif type(value) is int:
            return formula_tree.TransitionDurationInInterval(
                self._transition,
                [0, value]
            )
        else:
            raise Exception("Value of type %s given to <= comparison on %s is not supported." %
                            (value.__class__.__name__, self._transition))


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
            raise Exception("Value of type %s given to _in comparison on %s is not supported." %
                            (interval.__class__.__name__, self))

    def __lt__(self, value):
        """
        Generates an atom.
        """
        if type(value) in [int, float]:
            return formula_tree.TimeBetweenInOpenInterval(
                self._lhs,
                self._rhs,
                [0, value]
            )
        else:
            raise Exception("Value of type %s given to < comparison on %s is not supported." %
                            (value.__class__.__name__, self))

    def __le__(self, value):
        """
        Generates an atom.
        """
        if type(value) in [int, float]:
            return formula_tree.TimeBetweenInInterval(
                self._lhs,
                self._rhs,
                [0, value]
            )
        else:
            raise Exception("Value of type %s given to <= comparison on %s is not supported." %
                            (value.__class__.__name__, self))


"""
Utility functions to extract information from formulas.
"""


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

    # if the atom has an LHS and an RHS, there must be two composition sequences

    sequence = [atom]
    if type(atom) == formula_tree.LogicalNot:
        current_operator = atom.operand
    else:
        current_operator = atom

    if formula_tree.is_mixed_atom(atom):

        # atom is mixed - two composition sequences

        lhs = atom._lhs
        rhs = atom._rhs

        lhs_sequence = [atom]
        rhs_sequence = [atom]

        comp_sequence_lhs = composition_sequence_from_value(lhs_sequence, lhs)
        comp_sequence_rhs = composition_sequence_from_value(rhs_sequence, rhs)

        return {"lhs": comp_sequence_lhs, "rhs": comp_sequence_rhs}

    else:

        # atom is simple - just one composition sequence

        if type(current_operator) == formula_tree.TransitionDurationInInterval:
            current_operator = current_operator._transition
        if type(current_operator) == formula_tree.TransitionDurationInOpenInterval:
            current_operator = current_operator._transition
        elif type(current_operator) == formula_tree.StateValueEqualTo:
            current_operator = current_operator._state
        elif type(current_operator) == formula_tree.StateValueLengthInInterval:
            current_operator = current_operator._state
        elif type(current_operator) == formula_tree.StateValueLengthInOpenInterval:
            current_operator = current_operator._state
        elif type(current_operator) == formula_tree.StateValueInInterval:
            current_operator = current_operator._state
        elif type(current_operator) == formula_tree.StateValueInOpenInterval:
            current_operator = current_operator._state
        elif type(current_operator) == formula_tree.StateValueTypeEqualTo:
            current_operator = current_operator._state

        sequence = composition_sequence_from_value(sequence, current_operator)

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
