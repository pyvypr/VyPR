from __future__ import print_function
"""def print(*s):
	pass"""
"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""

import datetime


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
			return (self._state == other_atom._state and self._name == other_atom._name\
				and self._interval == other_atom._interval)
		else:
			return False

	def check(self, value):
		"""
		Mandatory check method used by formula trees to compute truth values.
		"""
		return self._interval[0] <= value[self._name] <= self._interval[1]

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
			return (self._state == other_atom._state and self._name == other_atom._name\
				and self._interval == other_atom._interval)
		else:
			return False

	def check(self, value):
		"""
		Mandatory check method used by formula trees to compute truth values.
		"""
		return self._interval[0] < value[self._name] < self._interval[1]

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
			return (self._state == other_atom._state and self._name == other_atom._name\
				and self._value == other_atom._value)
		else:
			return False

	def check(self, value):
		return self._value == value[self._name]

class StateValueEqualToMixed(Atom):
	"""
	This class models the atom (s1(x) = s2(y)).
	"""

	def __init__(self, lhs, lhs_name, rhs, rhs_name):
		self._lhs = lhs
		self._rhs = rhs
		self._lhs_name = lhs_name
		self._rhs_name = rhs_name
		self._lhs_value = None
		self._rhs_value = None

	def __repr__(self):
		return "(%s)(%s) = (%s)(%s)" % (self._lhs, self._lhs_name, self._rhs, self._rhs_name)

	def __eq__(self, other_atom):
		if type(other_atom) is StateValueEqualToMixed:
			return (self._lhs == other_atom._lhs
				and self._lhs_name == self._rhs_name)
		else:
			return False

	"""
	Mixed comparison atoms require values from multiple points at runtime.
	Hence, we store the LHS and RHS when we receive them, each time
	checking whether we have equality yet.
	"""

	def update(self, observation, index):
		"""
		For a given observation and index (0 for LHS and 1 for RHS),
		update the atom.
		"""
		if index == 0:
			self.check_lhs_value(observation)
		elif index == 1:
			self.check_rhs_value(observation)

	def check_lhs_value(self, value):
		self.lhs_value = value
		return self.check()

	def check_rhs_value(self, value):
		self.rhs_value = value
		return self.check()

	def check(self):
		"""
		If either the RHS or LHS are None, we don't try to reach a truth value.
		But if they are both not equal to None, we check for equality.
		"""
		if self.lhs_value is None or self.rhs_value is None:
			return None
		else:
			return self.lhs_value == self.rhs_value

class StateValueLengthInInterval(Atom):
	"""
	This class models the atom (len(s(x)) in I).
	"""

	def __init__(self, state, name, interval):
		self._state = state
		self._name = name
		self._interval = interval

	def __repr__(self):
		return "len(%s(%s)) in %s" % (self._state, self._name, self._interval)

	def __eq__(self, other_atom):
		if type(other_atom) is StateValueLengthInInterval:
			return (self._state == other_atom._state and self._name == other_atom._name\
				and self._interval == other_atom._interval)
		else:
			return False

	def check(self, value):
		"""
		Mandatory check method used by formula trees to compute truth values.
		"""
		return self._interval[0] <= len(value[self._name]) <= self._interval[1]

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

	def check(self, duration):
		return self._interval[0] <= duration <= self._interval[1]

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
		if not(type(formula2) is LogicalOr):
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
			elif not(formula_is_derived_from_atom(operand)) and operand.contains_formula(formula):
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
		if not(type(formula2) is LogicalAnd):
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
			elif not(formula_is_derived_from_atom(operand)) and operand.contains_formula(formula):
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

	def contains_formula(self, formula):
		"""
		Given a formula, check whether it is contained within this formula.
		"""
		if self.operand == formula:
			return not(formula_is_derived_from_atom(self.operand))
		elif not(formula_is_derived_from_atom(self.operand)) and self.operand.contains_formula(formula):
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
	if type(sub_formula) is LogicalNot:# double negation
		return sub_formula.operand
	else:
		return LogicalNot(sub_formula)

def formula_is_atom(formula):
	return formula_is_derived_from_atom(formula) or (type(formula) is LogicalNot and formula_is_derived_from_atom(formula.operand))

def formula_is_derived_from_atom(formula):
	return (Atom in type(formula).__bases__)

def atom_is_positive(atom):
	return not(type(atom) is LogicalNot)

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
		tmp = map(lambda ops : get_formula_alphabet(ops), formula.operands)
		final = []
		for tmp_element in tmp:
			final += tmp_element
		return final
	elif type(formula) is LogicalAnd:
		tmp = map(lambda ops : get_formula_alphabet(ops), formula.operands)
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
		for atom in atoms:
			self._state[atom] = None

	def set_state(self, symbol):
		"""
		Given an atom, set this to true in the state
		and set its negative to false
		"""
		if not(symbol in self._state.keys()):
			self._state[symbol] = None
		if not(lnot(symbol) in self._state.keys()):
			self._state[lnot(symbol)] = None
		positive_key_index = self._state.keys().index(symbol)
		negative_key_index = self._state.keys().index(lnot(symbol))
		positive_key = self._state.keys()[positive_key_index]
		negative_key = self._state.keys()[negative_key_index]

		if formula_is_derived_from_atom(symbol):
			self._state[positive_key] = True
			self._state[negative_key] = False
		elif type(symbol) is LogicalNot and formula_is_derived_from_atom(symbol.operand):
			self._state[positive_key] = False
			self._state[negative_key] = True

	def __repr__(self):
		return str(self._state)

	def __eq__(self, other):
		print("CHECKING EQUALITY OF MONITOR STATES")
		if type(other) is CheckerState:
			other = other._state
		else:
			return False

		print(self._state)
		print(other)

		keys = self._state.keys()
		for key in keys:
			print("CHECKING KEY %s" % key)
			if not(key in other.keys()):
				print("key %s not in other %s" % (key, other))
				return False
			else:
				key_index = other.keys().index(key)
				value_in_other = other[other.keys()[key_index]]
				if value_in_other != self._state[key]:
					print("%s : %s != %s" % (key, value_in_other, self._state[key]))
					return False
				else:
					print("%s : %s = %s" % (key, value_in_other, self._state[key]))

		# nothing has returned false, so return true
		return True

class Checker(object):

	def __init__(self, formula, optimised=True):
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
		# we use a tuple to record the instantiation time for each encountered bind variable
		self._monitor_instantiation_time = (datetime.datetime.now(),)

		if self._optimised:
			self.construct_atom_formula_occurrence_map(self._formula)
			print("="*100)
			print("INSTANTIATING OPTIMISED MONITOR")
			print("="*100)
		else:
			print("="*100)
			print("INSTANTIATING NON-OPTIMISED MONITOR")
			print("="*100)

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
			tmp = map(lambda ops : self.get_unresolved_atoms(ops), formula.operands)
			final = []
			for tmp_element in tmp:
				final += tmp_element
			return final
		elif type(formula) is LogicalAnd:
			tmp = map(lambda ops : self.get_unresolved_atoms(ops), formula.operands)
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
					print("formula %s has parent %s" % (formula.operands[n], formula.operands[n].parent_formula))
					self.construct_atom_formula_occurrence_map(formula.operands[n])
		elif formula_is_atom(formula):
			if self.atom_to_occurrence_map.get(formula):
				self.atom_to_occurrence_map[formula].append(formula)
			else:
				self.atom_to_occurrence_map[formula] = [formula]

	def __repr__(self):
		return "Monitor for formula %s:\n  timestamps: %s\n state: %s\n  verdict: %s" % (self._original_formula, str(self._monitor_instantiation_time), str(self._formula), self._formula.verdict)

	def process_atom_and_value(self, atom, value, atom_index,
							force_monitor_update=False, inst_point_id=None,
							program_path=None, state_dict=None):
		"""
		Given an atom and a value, update this monitor.
		"""
		print("processing observation with program path %s" % program_path)
		# record the observation and path
		if not(self.atom_to_observation.get(atom_index)):
			self.atom_to_observation[atom_index] = (value, inst_point_id)
		# we always overwrite this
		self.atom_to_program_path[atom_index] = [v for v in program_path]
		self.atom_to_state_dict[atom_index] = state_dict

		initial_verdict = self._formula.verdict
		
		print("PROCESSING ATOM %s" % atom)
		if type(atom) is StateValueInInterval:
			print("processing binding %s wrt interval %s" % (value, atom._interval))
			if atom.check(value):
				result = self.check_optimised(atom, force_monitor_update=force_monitor_update)
			else:
				result = self.check_optimised(lnot(atom), force_monitor_update=force_monitor_update)
		elif type(atom) is TransitionDurationInInterval:
			time_taken = value.total_seconds()
			print("processing time taken %s wrt interval %s" % (time_taken, atom._interval))
			if atom.check(time_taken):
				result = self.check_optimised(atom, force_monitor_update=force_monitor_update)
			else:
				result = self.check_optimised(lnot(atom), force_monitor_update=force_monitor_update)
		elif type(atom) is StateValueEqualTo:
			print("processing state value equality for observed valued %s wrt %s" % (str(value), str(atom._value)))
			if atom.check(value):
				result = self.check_optimised(atom, force_monitor_update=force_monitor_update)
			else:
				result = self.check_optimised(lnot(atom), force_monitor_update=force_monitor_update)
		elif type(atom) is StateValueInOpenInterval:
			time_taken = value.total_seconds()
			print("processing time taken %s wrt open interval %s" % (time_taken, atom._interval))
			if atom.check(time_taken):
				result = self.check_optimised(atom, force_monitor_update=force_monitor_update)
			else:
				result = self.check_optimised(lnot(atom), force_monitor_update=force_monitor_update)

		final_verdict = self._formula.verdict

		if initial_verdict != final_verdict:
			# for each monitor, this branch can only ever be traversed once
			self.collapsing_atom = atom

		return result

	def check_optimised(self, symbol, force_monitor_update=False):
		"""
		Given a symbol, find the formula occurrences that contain this symbol.
		For each of the occurrences, replace the atom with the appropriate value (T or F).
		Then loop up through the parents while each successive parent can be collapsed to a truth value.
		"""

		if not(force_monitor_update) and not(self._formula.verdict is None):
			return self._formula.verdict

		if symbol in self.observed_atoms or lnot(symbol) in self.observed_atoms:
			return
		else:
			self.observed_atoms.append(symbol)

		# NOTE: BE AWARE THAT THE ALPHABET USED TO INITIALLY POPULATE _STATE DOES NOT INCLUDE NEGATIVES
		# OF EVERY ATOM

		# update state for the monitoring algorithm to use
		self._state.set_state(symbol)

		print("checking symbol %s" % symbol)
		print("against map %s" % self.atom_to_occurrence_map)
		if symbol in self.atom_to_occurrence_map.keys():
			positive_key_index = self.atom_to_occurrence_map.keys().index(symbol)
			positive_key = self.atom_to_occurrence_map.keys()[positive_key_index]
			positives = self.atom_to_occurrence_map.get(positive_key)
		else:
			positives = []

		if lnot(symbol) in self.atom_to_occurrence_map.keys():
			negative_key_index = self.atom_to_occurrence_map.keys().index(lnot(symbol))
			negative_key = self.atom_to_occurrence_map.keys()[negative_key_index]
			negatives = self.atom_to_occurrence_map.get(negative_key)
		else:
			negatives = []

		all_occurences = positives + negatives

		print("Occurrences for symbol %s are %s" % (symbol, all_occurences))

		for occurrence in all_occurences:
			print("Processing occurrence %s" % occurrence)
			# find the position of the atom in the subformula
			index_in_formula = 0
			# if the formula to which this atom belongs is an atom,
			# this can only happen when a formula consists of only an atom
			if formula_is_atom(occurrence):
				print("occurrence %s is an atom" % occurrence)
				if formula_is_derived_from_atom(symbol):
					print("Symbol %s is positive" % symbol)
					if formula_is_derived_from_atom(occurrence):
						print("Occurrence contains positive symbol - replacing with T")
						self._formula.verdict = True
						return True
					else:
						print("Occurrence contains negative symbol - replacing with F")
						self._formula.verdict = False
						return False
				else:
					print("Symbol %s is negative" % symbol)
					if formula_is_derived_from_atom(occurrence):
						print("Occurrence contains positive symbol - replacing with F")
						self._formula.verdict = False
						return False
					else:
						print("Occurrence contains negative symbol - replacing with T")
						self._formula.verdict = True
						return True
			else:
				for n in range(len(occurrence.operands)):
					if occurrence.operands[n] in [symbol, lnot(symbol)]:
						index_in_formula = n

				print("Symbol is at index %d in parent" % index_in_formula)
				# replace the atom we've observed accordingly
				if formula_is_derived_from_atom(symbol):
					print("Symbol %s is positive" % symbol)
					if formula_is_derived_from_atom(occurrence.operands[index_in_formula]):
						print("Occurrence contains positive symbol - replacing with T")
						occurrence.operands[index_in_formula] = 'T'
					else:
						print("Occurrence contains negative symbol - replacing with F")
						occurrence.operands[index_in_formula] = 'F'
				else:
					print("Symbol %s is negative" % symbol)
					if formula_is_derived_from_atom(occurrence.operands[index_in_formula]):
						print("Occurrence contains positive symbol - replacing with F")
						occurrence.operands[index_in_formula] = 'F'
					else:
						print("Occurrence contains negative symbol - replacing with T")
						occurrence.operands[index_in_formula] = 'T'

				print("Top level formula is now %s" % self._formula)
				print("Traversing upwards to collapse subtrees")

				# iterate up through the tree, collapsing sub-formulas to truth values as far as we can
				current_formula = occurrence
				current_collapsed_value = collapsed_formula(current_formula)
				# iterate while the current formula is collapsible to a truth value
				while not(current_collapsed_value is None):
					print("Processing %s with collapsed value %s and parent %s" % (current_formula, current_collapsed_value, current_formula.parent_formula))
					if not(current_formula.parent_formula is None):
						current_formula.parent_formula.operands[current_formula.index_in_parent] = current_collapsed_value
						current_formula = current_formula.parent_formula
						current_collapsed_value = collapsed_formula(current_formula)
						print("Collapsed formula is %s" % current_formula)
					else:
						# we have collapsed the root to a truth value
						print("Collapsed to root, %s" % current_collapsed_value)
						truth_value_to_boolean = {'T' : True, 'F' : False, '?' : None}
						self._formula.verdict = truth_value_to_boolean[current_collapsed_value]
						return self._formula.verdict

				print("After collapse, formula is %s" % self._formula)

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

		if not(self._formula.verdict is None):
			print("a verdict has been arrived at - no observations can change it")
			return self._formula.verdict

		self.observed_atoms.append(symbol)

		sub_verdict = None

		indent = "    "*level

		print(indent + "checking formula %s" % formula)

		if type(formula) is LogicalAnd or type(formula) is LogicalOr:
			# first check if the disjunction or conjunction can be immediately
			# collapsed to a truth value
			if type(formula) is LogicalAnd:
				if 'F' in formula.operands:
					return False
			elif type(formula) is LogicalOr:
				if 'T' in formula.operands:
					return True

			if len(set(formula.operands)) == 1:
				if formula.operands[0] == 'T':
					return True
				elif formula.operands[0] == 'F':
					return False

			# if not, iterate through the operands
			for n in range(len(formula.operands)):
				print(indent + "processing operand %s of %s" % (formula.operands[n], formula))
				if not(formula.operands[n] in ['T', 'F']):
					if formula_is_atom(formula.operands[n]):
						print(indent + "operand %s is atomic" % formula.operands[n])
						if ((formula_is_derived_from_atom(formula.operands[n]) and formula_is_derived_from_atom(symbol) and formula.operands[n] == symbol)
							or (type(formula.operands[n]) is LogicalNot and type(symbol) is LogicalNot and formula.operands[n] == symbol)):
							print(indent + "setting %s to T" % formula.operands[n])
							formula.operands[n] = 'T'
							if type(formula) is LogicalOr:
								print(indent + "true atom in disjunction %s - setting disjunction to true" % formula)
								formula = 'T'
								return True
							elif type(formula) is LogicalAnd:
								formula.true_clauses += 1
								if formula.true_clauses == len(formula.operands):
									formula = 'T'
									print(indent + "all clauses of conjunction true")
									return True
						elif ((formula_is_derived_from_atom(formula.operands[n]) and type(symbol) is LogicalNot and formula.operands[n] == symbol.operand)
							or (type(formula.operands[n]) is LogicalNot and formula.operands[n].operand == symbol)):
							print("setting %s to F" % formula.operands[n])
							formula.operands[n] = 'F'
							if type(formula) is LogicalAnd:
								print(indent + "false atom in conjunction %s - setting conjunction to false" % formula)
								formula = 'F'
								return False
					else:
						sub_verdict = self.check(formula.operands[n], symbol, level+1)
						if sub_verdict:
							print(indent + "collapsing %s to T" % formula.operands[n])
							formula.operands[n] = 'T'
							if type(formula) is LogicalOr:
								print("adsf")
								print(indent + "true atom in disjunction %s - setting disjunction to true" % formula)
								formula = 'T'
								return True
							elif type(formula) is LogicalAnd:
								formula.true_clauses += 1
								if formula.true_clauses == len(formula.operands):
									formula = 'T'
									print(indent + "all clauses of conjunction true")
									return True
						elif sub_verdict == False:# explicitly not including None
							formula.operands[n] = 'F'
							if type(formula) is LogicalAnd:
								print(indent + "false atom in conjunction %s - setting conjunction to false" % formula)
								formula = 'F'
								return False
			return sub_verdict
		elif type(formula) is LogicalNot:
			if formula_is_derived_from_atom(formula.operand) and formula.operand == symbol:
				return False
			elif type(formula.operand) is LogicalNot and formula.operand.operand == symbol:
				return True

def new_monitor(formula, optimised=True):
	print(formula)
	return Checker(formula, optimised)
