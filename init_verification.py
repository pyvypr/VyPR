"""
Module containing functions to be called inside the verified service.
This provides a function to set up the consumption thread (initialising verification) and a function to insert events into the consumption queue.
"""

import threading
import Queue
import time
import pickle
import os
import sys
from pprint import pprint
import datetime
import requests
import json

sys.path.append("VyPR/")

from monitor_synthesis import formula_tree
from monitor_synthesis.formula_tree import lnot
from formula_building.formula_building import *
from verdict_reports import VerdictReport
from control_flow_graph.construction import CFGEdge, CFGVertex

VERDICT_SERVER_URL = None

# thank you to the CMS Conditions Browser team for this
def to_timestamp(obj):
    return obj.total_seconds() if isinstance(obj, datetime.timedelta) else obj

def send_verdict_report(function_name, time_of_call, verdict_report, binding_to_line_numbers, http_request_time, property_hash):
	"""
	Send verdict data for a given function call (function name + time of call).
	"""
	global VERDICT_SERVER_URL
	verdicts = verdict_report.get_final_verdict_report()
	print("Sending verdicts %s to server" % verdicts)
	for bind_space_index in verdicts.keys():
		verdict_list = verdicts[bind_space_index]
		for verdict in verdict_list:
			print("verdict - ", verdict)
			# remember to deal with datetime objects in json serialisation
			request_body_dict = {
				"function_name" : function_name,
				"time_of_call" : time_of_call.isoformat(),
				"bind_space_index" : bind_space_index,
				"verdict" : json.dumps([verdict[0], verdict[1].isoformat(), verdict[2], verdict[3], verdict[4]], default=to_timestamp),
				"line_numbers" : json.dumps(binding_to_line_numbers[bind_space_index]),
				"http_request_time" : http_request_time.isoformat(),
				"property_hash" : property_hash
			}
			try:
				response = requests.post(os.path.join(VERDICT_SERVER_URL, "register_verdict/"), data=json.dumps(request_body_dict))
				print(response)
			except Exception as e:
				print("Something went wrong when sending verdict information to the verdict server.  The verdict information we tried to send is now lost.")
				import traceback
				traceback.print_exc()

	print("SENT VERDICT TO SERVER")

def consumption_thread_function(verification_obj):
	# the web service has to be considered as running forever, so the monitoring loop for now should also run forever
	# this needs to be changed for a clean exit
	while True:

		# take top element from the queue
		try:
			top_pair = verification_obj.consumption_queue.get(timeout=1)
		except:
			continue

		print("="*100)

		print("CONSUMING ", top_pair[0:5])

		property_hash = top_pair[0]

		# remove the property hash and just deal with the rest of the data
		top_pair = top_pair[1:]

		instrument_type = top_pair[0]
		function_name = top_pair[1]

		# get the maps we need for this function
		maps = verification_obj.function_to_maps[function_name][property_hash]
		static_bindings_to_trigger_points = maps.static_bindings_to_trigger_points
		static_bindings_to_monitor_states = maps.static_bindings_to_monitor_states
		static_qd_to_point_map = maps.static_qd_to_point_map
		static_qd_to_monitors = maps.static_qd_to_monitors
		formula_structure = maps.formula_structure
		bindings = maps.binding_space
		program_path = maps.program_path

		verdict_report = maps.verdict_report

		atoms = formula_structure._formula_atoms

		if instrument_type == "function":
			# we've received a point telling us that a function has started or ended
			# for now, we can just process "end" - we reset the contents of the maps
			# that are updated at runtime
			scope_event = top_pair[2]
			if scope_event == "end":
				# everything not here is static data that we need, and should be left
				maps.static_bindings_to_trigger_points = {}
				maps.static_bindings_to_monitor_states = {}
				maps.static_qd_to_monitors = {}

				# generate the verdict report, then reset it

				report_map = verdict_report.get_final_verdict_report()

				binding_to_line_numbers = {}

				for bind_space_index in report_map.keys():

					print("Binding")
					binding = bindings[bind_space_index]

					binding_to_line_numbers[bind_space_index] = []

					print("[")

					# for each element of the binding, print the appropriate representation
					for bind_var in binding:

						if type(bind_var) is CFGVertex:
							binding_to_line_numbers[bind_space_index].append(bind_var._previous_edge._instruction.lineno)
						elif type(bind_var) is CFGEdge:
							binding_to_line_numbers[bind_space_index].append(bind_var._instruction.lineno)

					print("]")

					print("gave verdicts %s" % (", ".join(map(str, report_map[bind_space_index]))))

				# send the verdict
				# we send the function name, the time of the function call, the verdict report object,
				# the map of bindings to their line numbers and the date/time of the request the identify it (single threaded...)
				send_verdict_report(function_name, maps.latest_time_of_call, verdict_report, binding_to_line_numbers, top_pair[3], top_pair[4])

				# reset the verdict report
				maps.verdict_report.reset()

				# reset the function start time for the next time
				maps.latest_time_of_call = None

				# reset the program path
				maps.program_path = []

			elif scope_event == "start":
				print("*"*50)
				print("FUNCTION HAS STARTED")
				print("*"*50)

				print(static_bindings_to_trigger_points)
				print(static_bindings_to_monitor_states)
				print(static_qd_to_monitors)

				# remember when the function call started
				maps.latest_time_of_call = datetime.datetime.now()

				print("*"*50)

			continue

		if instrument_type == "trigger":
			# we've received a trigger instrument

			static_qd_index = top_pair[2]
			bind_variable_index = top_pair[3]

			if not(static_bindings_to_trigger_points.get(static_qd_index)):
				static_bindings_to_trigger_points[static_qd_index] = {}

			# reset the trigger, but to a value distinct from this trigger point never being encountered
			#if static_bindings_to_trigger_points[static_qd_index].get(bind_variable_index):
			static_bindings_to_trigger_points[static_qd_index][bind_variable_index] = "triggered"

			print("Set partition set trigger for static qd %i and bind variable index %i to None" % (static_qd_index, bind_variable_index))

			# continue onto the next iteration of the consumption loop
			# trigger instrumentation points don't contribute to the monitor state
			continue

		if instrument_type == "path":
			# we've received a path recording instrument
			# append the branching condition to the program path encountered so far for this function.
			program_path.append(top_pair[2])
			continue

		static_qd_index = top_pair[2]
		bind_variable_index = top_pair[3]
		atom_index = top_pair[4]
		print("atom index", atom_index)
		instrumentation_set_index = top_pair[5]
		observed_value = top_pair[6]# this may be redundant now
		print("observed value", observed_value)
		associated_atom = atoms[atom_index]

		instrumentation_point_db_id = top_pair[-2]
		global_atom_index = top_pair[-1]


		# use the atom with the observed value and the object in the static cfg to decide
		# on the value of the atom and update the corresponding monitor

		# NOTE: THIS ASSUMES THAT EACH INSTRUMENT IS FOR ONE BINDING - THIS WILL PROBABLY
		# CHANGE AT SOME POINT SINCE THERE IS INTERSECTION IN INSTRUMENTATION SETS
		# BETWEEN BINDINGS.

		instrumentation_set = static_qd_to_point_map[static_qd_index][bind_variable_index][atom_index]

		instrumentation_point = instrumentation_set[0][instrumentation_set_index]
		#instrumentation_atom = instrumentation_set[1]
		instrumentation_atom = atoms[global_atom_index]

		# decide what instrumentation_point can trigger (monitor update, new monitor, or nothing at all)
		# for now the criteria is whether it is the first element in the list
		# this is a temporarily primitive implementation of the partial order-based condition

		if static_bindings_to_trigger_points.get(static_qd_index):
			if static_bindings_to_trigger_points.get(static_qd_index).get(bind_variable_index) in ["triggered", None]:
				# the trigger point has either 1) been changed by a trigger instrument, so branch minimality is attained
				# or 2) the qd has been encountered, but nothing has been encountered for this specific bind variable
				# I don't see how we could ever find None here - a trigger point is always placed before any instruments,
				# this could only ever be "triggered"
				branch_minimal = True
				static_bindings_to_trigger_points[static_qd_index][bind_variable_index] = instrumentation_point
			else:
				# the trigger point is not None, so branch minimality is not attained
				branch_minimal = False
		else:
			# nothing has been observed for this qd, and no trigger has been observed
			# since, if it had, the value of the trigger would be "triggered"
			branch_minimal = False
			static_bindings_to_trigger_points[static_qd_index] = {}
			static_bindings_to_trigger_points[static_qd_index][bind_variable_index] = instrumentation_point

		print(branch_minimal)

		if branch_minimal:

			print("branch minimal")

			# branch minimal, so if the bind variable is the first,
			# we always instantiate a new monitor, and if not, there are some checks to do

			if bind_variable_index == 0:
				print("bind variable 0")
				new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())
				try:
					static_qd_to_monitors[static_qd_index].append(new_monitor)
				except:
					static_qd_to_monitors[static_qd_index] = [new_monitor]

				# update the monitor with the newly observed data
				sub_verdict = new_monitor.process_atom_and_value(instrumentation_atom, observed_value, global_atom_index,
					inst_point_id=instrumentation_point_db_id, program_path=program_path)
				print(sub_verdict)
				if sub_verdict == True or sub_verdict == False:

					# record the monitor state with the binding
					if static_bindings_to_monitor_states.get(static_qd_index) is None:
						static_bindings_to_monitor_states[static_qd_index] = {}

					if not(static_bindings_to_monitor_states[static_qd_index].get(new_monitor._state._monitor_instantiation_time)):
						static_bindings_to_monitor_states[static_qd_index][new_monitor._state._monitor_instantiation_time] = new_monitor._state
					# an else clause isn't needed here - I think it's impossible for the first bind variable to duplicate a timestamp...

					# set the monitor to None
					atom_to_value_map = new_monitor.atom_to_observation
					atom_to_program_path_map = new_monitor.atom_to_program_path
					del new_monitor

					print("registering verdict")

					verdict_report.add_verdict(static_qd_index, sub_verdict, atom_to_value_map, associated_atom, atom_to_program_path_map, global_atom_index)
				else:
					pass
			else:
				print("bind variable > 0")

				if static_bindings_to_monitor_states.get(static_qd_index):
					print("Processing %i previous configurations" % len(static_bindings_to_monitor_states.get(static_qd_index)))
					print("\twith timestamp sequences %s" % static_bindings_to_monitor_states.get(static_qd_index).keys())

					# TODO: should find a more efficient way to do this - we remove duplicates from consideration
					# wrt the prefix of the timestamp sequence up to the bind variable
					subsequences_processed = []

					for timestamp in static_bindings_to_monitor_states.get(static_qd_index).keys():
						if timestamp[0:bind_variable_index] in subsequences_processed:
							# don't process a configuration from the same subsequence of events
							continue
						else:
							subsequences_processed.append(timestamp[0:bind_variable_index])
							print("using configuration with timestamp sequence %s" % [timestamp])

						configuration = static_bindings_to_monitor_states.get(static_qd_index)[timestamp]

						associated_atom_index = configuration._state.keys().index(instrumentation_atom)
						associated_atom_key = configuration._state.keys()[associated_atom_index]

						new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())

						if not(configuration._state.get(associated_atom_key) is None):
							# we only keep the new monitor if the configuration already observed the atom
							# otherwise we're just using a monitor as a way to resolve the truth value
							# to update the existing configuration without generating a new verdict
							try:
								static_qd_to_monitors[static_qd_index].append(new_monitor)
							except:
								static_qd_to_monitors[static_qd_index] = [new_monitor]
						else:
							pass

						# update the new monitor for this configuration with all the atoms apart from the one we've
						# just observed

						for key in configuration._state.keys():
							if not(key == instrumentation_atom) and not(key == formula_tree.lnot(instrumentation_atom)):
								if configuration._state[key] == True:
									new_monitor.check_optimised(key)
								elif configuration._state[key] == False:
									new_monitor.check_optimised(formula_tree.lnot(key))
								else:
									# the value is None - it wasn't observed in this configuration
									pass
							else:
								pass

						# update the monitor with the newly observed data

						if not(configuration._state.get(associated_atom_key) is None):
							sub_verdict = new_monitor.process_atom_and_value(instrumentation_atom, observed_value, global_atom_index,
								inst_point_id=instrumentation_point_db_id, program_path=program_path)

							# we need to copy the instantiation time of the configuration to the monitor's state
							new_monitor._state._monitor_instantiation_time = list(configuration._monitor_instantiation_time)
							try:
								new_monitor._state._monitor_instantiation_time[bind_variable_index] = datetime.datetime.now()
							except:
								new_monitor._state._monitor_instantiation_time += (datetime.datetime.now(),)
							new_monitor._state._monitor_instantiation_time = tuple(new_monitor._state._monitor_instantiation_time)

							# this configuration has already observed this atom,
							# so it's from an old monitor and we use it to instantiate a new monitor
							if sub_verdict == True or sub_verdict == False:
								print("instantiation time of verdict is ", new_monitor._state._monitor_instantiation_time)

								if static_bindings_to_monitor_states.get(static_qd_index) is None:
									static_bindings_to_monitor_states[static_qd_index] = {}

								if not(static_bindings_to_monitor_states[static_qd_index].get(new_monitor._state._monitor_instantiation_time)):
									static_bindings_to_monitor_states[static_qd_index][new_monitor._state._monitor_instantiation_time] = new_monitor._state

								# set the monitor to None
								static_qd_to_monitors[static_qd_index][-1] = None
								atom_to_value_map = new_monitor.atom_to_observation
								atom_to_program_path_map = new_monitor.atom_to_program_path
								del new_monitor
								verdict_report.add_verdict(static_qd_index, sub_verdict, atom_to_value_map, associated_atom, atom_to_program_path_map, global_atom_index)
								#send_verdict_report(function_name, maps.latest_time_of_call, verdict_report, binding_to_line_numbers, top_pair[4], top_pair[5])
							else:
								pass

						else:
							# this configuration hasn't observed this atom,
							# so must have been collapsed
							# so we just update the configuration (without instantiating a new monitor
							# or generating a new verdict)
							# when we send the observed value to the monitor, we have to force update since monitors' default behaviour
							# is to reject new observations if a verdict has already been reached
							print("updating a configuration that hasn't observed this atom")
							new_monitor.process_atom_and_value(instrumentation_atom, observed_value, global_atom_index,
								force_monitor_update=True, inst_point_id=instrumentation_point_db_id, program_path=program_path)
							static_bindings_to_monitor_states[static_qd_index][timestamp]._state = new_monitor._state._state
				else:
					print("No previous configurations")

				# update existing monitors or use existing ones to instantiate new monitors
				monitors = static_qd_to_monitors.get(static_qd_index)
				print("Monitors:", monitors)
				# we maintain a list of the timestamps we've handled so we don't instantiate multiple
				# new monitors based no existing monitors created at the same time
				# this is not the most efficient way - we could build a tree whose paths are sequences of timestamps
				# with monitors as leaves.
				timestamps_handled = []
				if not(monitors is None or list(set(monitors)) == [None]):
					for n in range(len(monitors)):
						# skip monitors that have reached verdicts
						if monitors[n] is None:
							continue

						# a trick to handle objects being used as keys in dictionaries
						associated_atom_index = monitors[n]._state._state.keys().index(instrumentation_atom)
						associated_atom_key = monitors[n]._state._state.keys()[associated_atom_index]

						# if this monitor hasn't observed this instrument yet, then simply update it
						if not(monitors[n]._state._state.get(associated_atom_key)):
							sub_verdict = monitors[n].process_atom_and_value(instrumentation_atom, observed_value, global_atom_index,
								inst_point_id=instrumentation_point_db_id, program_path=program_path)
							print(atom_index, monitors[n].atom_to_observation)
							if sub_verdict == True or sub_verdict == False:
								# update monitor instantiation timestamp sequence
								monitors[n]._state._monitor_instantiation_time = list(monitors[n]._state._monitor_instantiation_time)
								try:
									monitors[n]._state._monitor_instantiation_time[bind_variable_index] = datetime.datetime.now()
								except:
									monitors[n]._state._monitor_instantiation_time += (datetime.datetime.now(),)
								monitors[n]._state._monitor_instantiation_time = tuple(monitors[n]._state._monitor_instantiation_time)
								print("collapsed monitor timestamp:", monitors[n]._state._monitor_instantiation_time)

								# record the monitor state with the binding
								if static_bindings_to_monitor_states.get(static_qd_index) is None:
									static_bindings_to_monitor_states[static_qd_index] = {}

								if not(static_bindings_to_monitor_states[static_qd_index].get(monitors[n]._state._monitor_instantiation_time)):
									static_bindings_to_monitor_states[static_qd_index][monitors[n]._state._monitor_instantiation_time] = monitors[n]._state
								# set the monitor to None
								atom_to_value_map = monitors[n].atom_to_observation
								atom_to_program_path_map = monitors[n].atom_to_program_path
								# set the monitor to None
								monitors[n] = None

								verdict_report.add_verdict(static_qd_index, sub_verdict, atom_to_value_map, associated_atom, atom_to_program_path_map, global_atom_index)
							else:
								pass
						elif not(monitors[n]._state._monitor_instantiation_time in timestamps_handled):
							# this monitor has observed this atom, 
							print("This monitor has already observed this point - instantiating a new monitor")
							# this monitor has observed this atom - since this observation is branch minimal,
							# we copy the state (at some point, only up to the current bind variable)
							# and then update the new monitor with the new observation
							new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())

							try:
								static_qd_to_monitors[static_qd_index].append(new_monitor)
							except:
								static_qd_to_monitors[static_qd_index] = [new_monitor]

							for key in monitors[n]._state._state.keys():
								if not(key == instrumentation_atom) and not(key == formula_tree.lnot(instrumentation_atom)):
									if monitors[n]._state._state[key] == True:
										new_monitor.check_optimised(key)
									elif monitors[n]._state._state[key] == False:
										new_monitor.check_optimised(formula_tree.lnot(key))
									else:
										# the value is None - it wasn't observed in this configuration
										pass
								else:
									pass

							# update the monitor with the newly observed data
							sub_verdict = new_monitor.process_atom_and_value(instrumentation_atom, observed_value, global_atom_index,
								inst_point_id=instrumentation_point_db_id, program_path=program_path)

							# we need to copy the instantiation time of the configuration to the monitor's state
							new_monitor._state._monitor_instantiation_time = list(monitors[n]._state._monitor_instantiation_time)
							try:
								new_monitor._state._monitor_instantiation_time[bind_variable_index] = datetime.datetime.now()
							except:
								new_monitor._state._monitor_instantiation_time += (datetime.datetime.now(),)
							new_monitor._state._monitor_instantiation_time = tuple(new_monitor._state._monitor_instantiation_time)

							# this configuration has already observed this atom,
							# so it's from an old monitor and we use it to instantiate a new monitor
							if sub_verdict == True or sub_verdict == False:
								print(new_monitor._state._monitor_instantiation_time)

								# record the state
								if static_bindings_to_monitor_states.get(static_qd_index) is None:
									static_bindings_to_monitor_states[static_qd_index] = {}

								if not(static_bindings_to_monitor_states[static_qd_index].get(new_monitor._state._monitor_instantiation_time)):
									static_bindings_to_monitor_states[static_qd_index][new_monitor._state._monitor_instantiation_time] = new_monitor._state

								# set the monitor to None
								static_qd_to_monitors[static_qd_index][-1] = None
								atom_to_value_map = new_monitor.atom_to_observation
								atom_to_program_path_map = new_monitor.atom_to_program_path
								del new_monitor
								verdict_report.add_verdict(static_qd_index, sub_verdict, atom_to_value_map, associated_atom, atom_to_program_path_map, global_atom_index)
							else:
								pass

							print("Monitors for qd index %i are now %s" % (static_qd_index, str(static_qd_to_monitors[static_qd_index])))
							timestamps_handled.append(monitors[n]._state._monitor_instantiation_time)
				else:
					pass

		else:

			print("%s is not branch minimal" % str(top_pair))

			# this point can't trigger instantiation of a monitor for this element of the static qd
			# get all the monitors that are not None
			monitors = static_qd_to_monitors.get(static_qd_index)
			if monitors is None:
				# all previous monitors have been evaluated
				pass
			else:
				# update all the monitors
				for n in range(len(monitors)):
					# skip monitors that have reached verdicts
					if monitors[n] is None:
						continue

					sub_verdict = monitors[n].process_atom_and_value(instrumentation_atom, observed_value, global_atom_index,
						inst_point_id=instrumentation_point_db_id, program_path=program_path)
					if sub_verdict == True or sub_verdict == False:

						# record the monitor state with the binding
						if static_bindings_to_monitor_states.get(static_qd_index) is None:
							static_bindings_to_monitor_states[static_qd_index] = {}

						if not(static_bindings_to_monitor_states[static_qd_index].get(str(monitors[n]._state._monitor_instantiation_time))):
							static_bindings_to_monitor_states[static_qd_index][str(monitors[n]._state._monitor_instantiation_time)] = monitors[n]._state

						# set the monitor to None
						atom_to_value_map = monitors[n].atom_to_observation
						atom_to_program_path_map = monitors[n].atom_to_program_path
						# set the monitor to None
						monitors[n] = None

						verdict_report.add_verdict(static_qd_index, sub_verdict, atom_to_value_map, associated_atom, atom_to_program_path_map, global_atom_index)
					else:
						if check_monitor_size:
							add_monitor_size_point(static_qd_index, n, len(monitors[n].get_unresolved_atoms()), sub_verdict, "existing")

		# set the task as done
		verification_obj.consumption_queue.task_done()

		print("CONSUMPTION DONE")

		print("="*100)

class PropertyMapGroup(object):
	"""
	Groups together all the maps needed for verification of a single run of a single function, wrt a single property.
	"""

	def __init__(self, module_name, function_name, property_hash):

		self._function_name = function_name
		self._property_hash = property_hash

		# read in instrumentation map
		with open("instrumentation_maps/module-%s-function-%s-property-%s.dump" %\
				(module_name.replace(".", "-"), function_name.replace(":", "-"), property_hash), "rb") as h:
			instr_map_dump = h.read()

		# read in binding spaces
		with open("binding_spaces/module-%s-function-%s-property-%s.dump" %\
				(module_name.replace(".", "-"), function_name.replace(":", "-"), property_hash), "rb") as h:
			binding_space_dump = h.read()

		# read in index hash map
		with open("index_hash/module-%s-function-%s.dump" % (module_name.replace(".", "-"), function_name.replace(":", "-")), "rb") as h:
			index_to_hash_dump = h.read()

		# reconstruct formula structure
		# there's probably a better way to do this
		exec("".join(open("verification_conf.py", "r").readlines()))
		index_to_hash = pickle.loads(index_to_hash_dump)
		property_index = index_to_hash.index(property_hash)

		print(function_name, property_index)
		
		# might just change the syntax in the verification conf file at some point to use : instead of .
		self.formula_structure = verification_conf[module_name][function_name.replace(":", ".")][property_index]
		print(self.formula_structure)
		self.binding_space = pickle.loads(binding_space_dump)
		self.static_qd_to_point_map = pickle.loads(instr_map_dump)
		self.static_qd_to_monitors = {}
		self.static_bindings_to_monitor_states = {}
		self.static_bindings_to_trigger_points = {}
		self.verdict_report = VerdictReport()
		self.latest_time_of_call = None
		self.program_path = []

def read_configuration(file):
	"""
	Read in 'file', parse into an object and return.
	"""
	with open(file, "r") as h:
		contents = h.read()

	return json.loads(contents)

class Verification(object):

	def __init__(self, flask_object):
		"""
		Sets up the consumption thread for events from instruments.
		"""
		print("INSTANTIATING VERIFICATION OBJ")

		# read configuration file
		inst_configuration = read_configuration("vypr.config")
		global VERDICT_SERVER_URL
		VERDICT_SERVER_URL = inst_configuration.get("verdict_server_url") if inst_configuration.get("verdict_server_url") else "http://localhost:9001/"

		# set up the maps that the monitoring algorithm that the consumption thread runs

		# we need the list of functions that we have instrumentation data from, so read the instrumentation maps directory
		dump_files = filter(lambda filename : ".dump" in filename, os.listdir("instrumentation_maps"))
		functions_and_properties = map(lambda function_dump_file : function_dump_file.replace(".dump", ""), dump_files)
		tokens = map(lambda string : string.split("-"), functions_and_properties)

		self.function_to_maps = {}

		for token_chain in tokens:

			start_of_module = token_chain.index("module")+1
			start_of_function = token_chain.index("function")+1
			start_of_property = token_chain.index("property")+1

			module_string = ".".join(token_chain[start_of_module:start_of_function-1])
			# will need to be modified to support functions that are methods
			#function = ".".join(token_chain[start_of_function:start_of_property-1])
			function = ":".join(token_chain[start_of_function:start_of_property-1])

			property_hash = token_chain[start_of_property]

			print("Setting up monitoring state for module/function/property triple %s, %s, %s" % (module_string, function, property_hash))

			module_function_string = "%s.%s" % (module_string, function)

			if not(self.function_to_maps.get(module_function_string)):
				self.function_to_maps[module_function_string] = {}
			self.function_to_maps[module_function_string][property_hash] = PropertyMapGroup(module_string, function, property_hash)

		print(self.function_to_maps)

		print("Setting up monitoring thread that will deal all properties across all functions.")

		# setup consumption queue and store it globally across requests
		self.consumption_queue = Queue.Queue()
		# setup consumption thread
		self.consumption_thread = threading.Thread(
			target=consumption_thread_function,
			args=[self]
		)
		self.consumption_thread.start()

	def send_event(self, event_description):
		self.consumption_queue.put(event_description)
