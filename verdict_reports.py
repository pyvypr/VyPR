"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""

from threading import Lock
import datetime

class VerdictReport(object):
	"""
	Maintains a map from binding space indices to sets of verdicts reached at runtime.
	"""

	def __init__(self):
		self._bind_space_to_verdicts = {}
		self.map_lock = Lock()

	def add_verdict(
				self, bind_space_index, verdict, atom_to_value_map,
				atom_to_program_path_map, collapsing_atom_index,
				atom_to_state_dict_map
		):
		self.map_lock.acquire()
		#print("ADDING VERDICT FOR QD INDEX %i" % bind_space_index)
		if not(self._bind_space_to_verdicts.get(bind_space_index)):
			self._bind_space_to_verdicts[bind_space_index] =\
				[(
					verdict,
					datetime.datetime.now(),
					atom_to_value_map,
					atom_to_program_path_map,
					collapsing_atom_index,
					atom_to_state_dict_map
				)]
		else:
			self._bind_space_to_verdicts[bind_space_index].append(
				(
					verdict,
					datetime.datetime.now(),
					atom_to_value_map,
					atom_to_program_path_map,
					collapsing_atom_index,
					atom_to_state_dict_map
				)
			)
		self.map_lock.release()

	def get_final_verdict_report(self):
		return self._bind_space_to_verdicts

	def reset(self):
		# reset the map and the lock
		self._bind_space_to_verdicts = {}
		self.map_lock = Lock()