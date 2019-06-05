"""
Module for performing instrumentation of the service based on the contents of the verification_config.py file.
"""

from __future__ import print_function

import sys
import importlib
import traceback
import ast
import marshal
import dis
import py_compile
import time
import pprint
import sqlite3
import pickle
from graphviz import Digraph
import hashlib
import requests
import inspect
import json
import argparse

# get the formula building functions before we evaluate the configuration code
from formula_building.formula_building import *
from monitor_synthesis.formula_tree import lnot
from control_flow_graph.construction import *

VERDICT_SERVER_URL = None
VERBOSE = False
EXPLANATION = False
DRAW_GRAPHS = False
VERIFICATION_HOME_MODULE = None

def print(*s):
	global VERBOSE
	if VERBOSE:
		__builtins__.print(*s)

def scfg_to_tree(root):
	"""
	Given a root vertex, compute the set of vertices and edges reachable from that
	vertex in the scfg.
	"""
	reachable_set = []
	traversal_stack = [root]
	traversed_edges = []
	while len(traversal_stack) > 0:
		top_vertex = traversal_stack.pop()
		for edge in top_vertex.edges:
			if not(edge in traversed_edges):
				reachable_set.append(edge)
				reachable_set.append(edge._target_state)
				traversed_edges.append(edge)
				traversal_stack.append(edge._target_state)
	return reachable_set

def construct_reachability_map(scfg):
	"""
	For each vertex in the scfg given, do a depth-first search
	"""

	vertex_to_reachable_set = {}

	for vertex in scfg.vertices:
		reachable_set = scfg_to_tree(vertex)
		vertex_to_reachable_set[vertex] = reachable_set

	return vertex_to_reachable_set

def compute_binding_space(quantifier_sequence, scfg, reachability_map, current_binding=[]):
	"""
	Given a sequence of quantifers over symbolic states/edges in the given scfg,
	compute the space of bindings that can be given to the formula to which this quantifier sequence is applied.
	The current_binding given may be partial, but represents the current point in the space of bindings upto which we have traversed.
	"""

	if len(current_binding) == 0:
		# we've just started - compute the static qd for the first quantifier,
		# then iterate over it and recurse into the list of quantifiers for each element
		if type(quantifier_sequence._bind_variables[0]) is StaticState:
			variable_changed = quantifier_sequence._bind_variables[0]._name_changed
			qd = filter(lambda symbolic_state : symbolic_state._name_changed == variable_changed\
				or variable_changed in symbolic_state._name_changed, scfg.vertices)
		elif type(quantifier_sequence._bind_variables[0]) is StaticTransition:
			variable_operated_on = quantifier_sequence._bind_variables[0]._operates_on
			relevant_target_vertices = filter(
				lambda symbolic_state : symbolic_state._name_changed == variable_operated_on\
					or variable_operated_on in symbolic_state._name_changed,
				scfg.vertices
			)
			qd = map(lambda symbolic_state : symbolic_state._previous_edge, relevant_target_vertices)

		print("computed independent qd: %s" % qd)
		binding_space = []
		# recurse with (possibly partial) bindings
		for element in qd:
			binding_space += compute_binding_space(quantifier_sequence, scfg, reachability_map, [element])

		print("computed whole binding space")
		return binding_space
	elif len(current_binding) < len(quantifier_sequence._bind_variables):
		# we have a partial binding
		# find the next quantifier
		next_index = len(current_binding)
		next_quantifier = quantifier_sequence._bind_variables[next_index]
		# find the position in the quantifier sequence on which the next quantifier depends
		index_in_quantifier_sequence = quantifier_sequence._bind_variables.index(next_quantifier._required_binding)
		# get the current value at that position in the binding we have
		current_binding_value = current_binding[index_in_quantifier_sequence]
		# use the type of the qd we need to traverse the scfg from this point
		if type(next_quantifier) is StaticState:
			print("computing unbounded future states according to %s" % next_quantifier)
		elif type(next_quantifier) is StaticTransition:
			print("computing unbounded future transitions according to %s using binding %s" % (next_quantifier, current_binding))
			# only works for vertex inputs
			# this has to cater for edges that are both assignments and function calls (assignments of function call return values)
			qd = filter(lambda edge : hasattr(edge, "_operates_on") and \
				(edge._operates_on == next_quantifier._operates_on or\
					next_quantifier._operates_on in edge._operates_on), reachability_map[current_binding_value])

			# compute the bindings from this new qd
			binding_space = []
			for element in qd:
				binding_space += compute_binding_space(quantifier_sequence, scfg, reachability_map, current_binding + [element])
			return binding_space
	else:
		# we now have a complete binding - return it
		return [current_binding]

def get_qualifier_subsequence(function_qualifier):
	"""
	Given a fully qualified function name, iterate over it and find the file
	in which the function is defined (this is the entry in the qualifier chain
	before the one that causes an import error)/
	"""

	# tokenise the qualifier string so we have names and symbols
	# the symbol used to separate two names tells us what the relationship is
	# a/b means a is a directory and b is contained within it
	# a.b means b is a member of a, so a is either a module or a class

	tokens = []
	last_position = 0
	for (n, character) in enumerate(list(function_qualifier)):
		if character in [".", "/"]:
			tokens.append(function_qualifier[last_position:n])
			tokens.append(function_qualifier[n])
			last_position = n + 1
		elif n == len(function_qualifier)-1:
			tokens.append(function_qualifier[last_position:])

	return tokens

def get_file_from_qualifier(qualifier_chain):
	"""
	Given a qualifier chain that points to a function/method, find the file name in which the function/module is found.
	"""
	# for now, just modify the string given and use that as the filename
	# the importlib method was accidentally starting the service's monitoring thread
	print("getting file from qualifier %s" % qualifier_chain)

	# get the subsequence of the qualifier chain that can be read in as a file
	# the remainder of the qualifier chain will be pointing to something in that file
	index_of_first_dot = qualifier_chain.index(".")
	filename = "".join(qualifier_chain[0:index_of_first_dot]) + ".py"

	return filename

def get_function_from_qualifier(qualifier_chain):
	index_of_first_dot = qualifier_chain.index(".")
	function_qualifier = qualifier_chain[index_of_first_dot+1:]
	return function_qualifier

def write_scfg_to_file(scfg, file_name):
	"""
	Given an scfg and a file name, write the scfg in dot format to the file.
	"""
	if DRAW_GRAPHS:
		graph = Digraph()
		graph.attr("graph", splines="true", fontsize="10")
		shape = "rectangle"
		for vertex in scfg.vertices:
			graph.node(str(id(vertex)), str(vertex._name_changed), shape=shape)
			for edge in vertex.edges:
				graph.edge(
					str(id(vertex)),
					str(id(edge._target_state)),
					"%s - %s - path length = %s" %\
						(str(edge._operates_on)\
							if not(type(edge._operates_on[0]) is ast.Print) else "print stmt",
						edge._condition,
						str(edge._target_state._path_length))
				)
		graph.render(file_name)
		print("Writing SCFG to file '%s'." % file_name)

def post_to_verdict_server(url, data):
	"""
	Given a url (extension of the base URL set by configuration) and some data, send a post request to the verdict server.
	"""
	global VERDICT_SERVER_URL
	response = requests.post(os.path.join(VERDICT_SERVER_URL, url), data).text
	return response

def read_configuration(file):
	"""
	Read in 'file', parse into an object and return.
	"""
	with open(file, "r") as h:
		contents = h.read()

	return json.loads(contents)

if __name__ == "__main__":

	parser = argparse.ArgumentParser(description='Instrumentation for VyPR.')
	parser.add_argument('--verbose', action='store_true',
		help='If given, output will be turned on for the instrumentation module.', required=False)
	parser.add_argument('--draw-graphs', action='store_true',
		help='If given, SCFGs derived from functions to be monitored will be written to GV files and compiled into PDFs.', required=False)

	args = parser.parse_args()

	VERBOSE = args.verbose
	DRAW_GRAPHS = args.draw_graphs

	inst_configuration = read_configuration("vypr.config")
	VERDICT_SERVER_URL = inst_configuration.get("verdict_server_url")\
		if inst_configuration.get("verdict_server_url") else "http://localhost:9001/"
	EXPLANATION = inst_configuration.get("explanation") == "on"
	VERIFICATION_HOME_MODULE = inst_configuration.get("verification_home_module")\
                if inst_configuration.get("verification_home_module") else "app"

	# reset code to non-instrumented
	for directory in os.walk("."):
		for file in directory[2]:
			if not("venv" in file):
				f = os.path.join(directory[0], file)
				if ".py.inst" in f:
					# rename to .py
					os.rename(f, f.replace(".py.inst", ".py"))
					# delete bytecode
					os.remove(f.replace(".py.inst", ".pyc"))
					print("reset file %s to uninstrumented version" % f)

	# load in verification config file
	verification_conf_file = inst_configuration.get("specification_file")\
		if inst_configuration.get("specification_file") else "verification_conf.py"
	verif_config_contents = "".join(open(verification_conf_file, "r").readlines())

	# execute contents so we have the configuration variable in the local scope
	exec(verif_config_contents)
	# we now have verification_conf and grouping_variable

	verified_modules = verification_conf.keys()

	# for each verified function, find the file in which it is defined

	verification_instruction = "verification.send_event"
	#verification_instruction = "print"

	for module in verified_modules:

		print("MODULE %s" % module)

		verified_functions = verification_conf[module].keys()

		file_name = module.replace(".", "/") + ".py"
		file_name_without_extension = module.replace(".", "/")

		# extract asts from the code in the file
		code = "".join(open(file_name, "r").readlines())
		asts = ast.parse(code)

		# THIS MUST BE MADE CONFIGURABLE
		# add necessary imports for instruments to work
		import_code = "from %s import verification; import flask" % VERIFICATION_HOME_MODULE
		import_asts = ast.parse(import_code)

		verification_import = import_asts.body[0]
		flask_import = import_asts.body[1]

		verification_import.lineno = asts.body[0].lineno
		verification_import.col_offset = asts.body[0].col_offset

		flask_import.lineno = asts.body[0].lineno
		flask_import.col_offset = asts.body[0].col_offset

		asts.body.insert(0, flask_import)
		asts.body.insert(0, verification_import)

		for function in verified_functions:

			print("FUNCTION %s" % function)

			# we replace . with : in function definitions to make sure we can distinguish between module
			# and class navigation later on
			instrument_function_qualifier = "%s.%s" % (module, function.replace(".", ":"))

			index_to_hash = []
			
			qualifier_subsequence = get_qualifier_subsequence(function)
			#qualifier_string = ".".join(qualifier_subsequence)
			function_name = function.split(".")

			# find the function definition
			print("finding function/method definition using qualifier chain %s" % function_name)

			actual_function_name = function_name[-1]
			hierarchy = function_name[:-1]

			print(actual_function_name, hierarchy)

			current_step = asts.body

			# traverse sub structures

			for step in hierarchy:
				current_step = filter(
					lambda entry : (type(entry) is ast.ClassDef and
						entry.name == step),
					current_step
				)[0]

			# find the final function definition

			function_def = filter(
				lambda entry : (type(entry) is ast.FunctionDef and
					entry.name == actual_function_name),
				current_step.body if type(current_step) is ast.ClassDef else current_step
			)[0]

			# construct the scfg of the code inside the function
			scfg = CFG()
			scfg_vertices = scfg.process_block(function_def.body)

			top_level_block = function_def.body

			print("scfg constructed for function body")

			# write scfg to file
			write_scfg_to_file(scfg, "%s-%s-%s.gv" %
				(file_name_without_extension.replace(".", ""), module.replace(".", "-"), function.replace(".", "-")))

			# for each property, instrument the function for that property

			for (formula_index, formula_structure) in enumerate(verification_conf[module][function]):

				print("-"*50)
				print("INSTRUMENTING FOR FORMULA %s" % formula_structure)

				# we should be able to use the same scfg for each stage of instrumentation,
				# since when we insert instruments we recompute the position of the instrumented instruction

				atoms = formula_structure._formula_atoms

				formula_hash = hashlib.sha1()
				serialised_bind_variables = pickle.dumps(formula_structure.bind_variables)
				formula_hash.update(serialised_bind_variables)
				serialised_formula_structure = pickle.dumps(formula_structure.get_formula_instance())
				formula_hash.update(serialised_formula_structure)
				formula_hash = formula_hash.hexdigest()
				serialised_atom_list = map(pickle.dumps, atoms)


				# update the index -> hash map
				index_to_hash.append(formula_hash)

				print("FORMULA HASH")
				print(formula_hash)


				# construct reachability of the SCFG
				# and derive the binding space based on the formula

				reachability_map = construct_reachability_map(scfg)
				bindings = compute_binding_space(formula_structure, scfg, reachability_map)

				print("binding space is ", bindings)

				# using these bindings, we now need to instrument the code
				# and then store the (bind space index, bind var index, atom index)
				# -> instrumentation set map in the intermediate relational database
				# so the instrumentation mappings can be recovered at runtime without recomputation

				potential_free_variables = {}
				static_qd_to_point_map = {}
				vertices_to_triple_list = {}

				# we attach indices to atoms because we need their index in the set of atoms
				# of the relevant formula
				initial_property_dict = {
					"formula_hash" : formula_hash,
					"function" : instrument_function_qualifier,
					"serialised_formula_structure" : serialised_formula_structure,
					"serialised_bind_variables" : serialised_bind_variables,
					"serialised_atom_list" : list(enumerate(serialised_atom_list))
				}

				# send instrumentation data to the verdict database
				try:
					print("SENDING PROPERTY %s FOR FUNCTION %s IN MODULE %s TO SERVER" % (formula_hash, function, module))
					response = post_to_verdict_server("store_property/", data=json.dumps(initial_property_dict))
					print("property sent to server")
					response = json.loads(response)
					atom_index_to_db_index = response["atom_index_to_db_index"]
					function_id = response["function_id"]
					print("atom index to db index map")
					print(atom_index_to_db_index)
				except:
					print("There was a problem with the verdict server at '%s'.  Instrumentation cannot be completed." % VERDICT_SERVER_URL)
					exit()

				for (m, element) in enumerate(bindings):

					print("PROCESSING BINDING %s" % element)

					# send the binding to the verdict server
					get_line_number = lambda el : el._previous_edge._instruction.lineno if type(el) is CFGVertex else el._instruction.lineno
					binding_dictionary = {
						"binding_space_index" : m,
						"function" : function_id,
						"binding_statement_lines" : map(get_line_number, element)
					}
					serialised_binding_dictionary = json.dumps(binding_dictionary)
					try:
						binding_db_id = int(post_to_verdict_server("store_binding/", data=serialised_binding_dictionary))
					except:
						print("There was a problem with the verdict server at '%s'.  Instrumentation cannot be completed." % VERDICT_SERVER_URL)
						exit()

					element_types = []

					static_qd_to_point_map[m] = {}

					print("setting up potential free variables for binding %i" % m)
					potential_free_variables[m] = {}

					for atom in atoms:

						composition_sequence = derive_composition_sequence(atom)

						print("COMPOSITION SEQUENCE FOR ATOM %s IS %s" % (atom, composition_sequence))

						input_bind_variable = composition_sequence[-1]

						position_in_quant_sequence = formula_structure._bind_variables.index(input_bind_variable)
						value_from_binding = element[position_in_quant_sequence]

						# the first element tells us how to instrument (variable value, function call duration, etc)
						# the final element tells us the bind variable to navigate from
						# the intermediate elements tell us what to look for in the control flow graph, starting from
						# the bind variable
						moves = list(reversed(composition_sequence[1:-1]))

						print(moves)

						# iterate through the moves we have to make,
						# using the type of the operator used in the move to compute the points we have to instrument
						# we set the default set to include just the current binding
						# for the case where no transformation happens
						instrumentation_points = [value_from_binding]
						# currently only works for a single move
						# for multiple moves we need to apply the transformation to each "previous" instrumentation point
						"""
						At the moment, this code is wrong - it's supposed to take as input the previous round of results,
						but always take the first round - needs to be changed.
						Will do when I consider nested future time operators.
						"""
						for move in moves:
							if type(move) is NextStaticTransition:
								calls = []
								if type(value_from_binding) is CFGVertex:
									scfg.next_calls(value_from_binding, move._operates_on, calls, marked_vertices=[])
								elif type(value_from_binding) is CFGEdge:
									scfg.next_calls(value_from_binding._target_state, move._operates_on, calls, marked_vertices=[])
								instrumentation_points = calls

						print(instrumentation_points)

						# add the pair consisting of the instrumentation points and the original atom
						#  to the point in the map identified by (static binding, index in static binding)
						if static_qd_to_point_map[m].get(position_in_quant_sequence):
							static_qd_to_point_map[m][position_in_quant_sequence].append((instrumentation_points, atom))
						else:
							static_qd_to_point_map[m][position_in_quant_sequence] = [(instrumentation_points, atom)]

						static_qd_to_point_map[m][position_in_quant_sequence].append(([value_from_binding], "trigger"))

					# now, perform the instrumentation
					# iterate through the bind variables - for each bind variable, instrument its points.

					for bind_variable_index in static_qd_to_point_map[m].keys():
						potential_free_variables[m][bind_variable_index] = {}
						for (atom_index, point_atom_pair) in enumerate(static_qd_to_point_map[m][bind_variable_index]):
							print("instrumenting for", atom_index, point_atom_pair)
							points = point_atom_pair[0]
							atom = point_atom_pair[1]
							# atom_index is wrt partitions based on variables,

							if atom == "trigger":
								# we must instrument this as a trigger point
								print("instrumenting a trigger point")
								point = points[0]

								# this instrument only needs to reset the minimality flag for the correct partition set
								# the binding space index combined with the bind variable index are enough for that
								instrument = "%s((\"%s\", \"trigger\", \"%s\", %i, %i))" %\
									(verification_instruction, formula_hash, instrument_function_qualifier, m, bind_variable_index)

								instrument_ast = ast.parse(instrument).body[0]
								if type(point) is CFGVertex:
									instruction = point._previous_edge._instruction
								else:
									instruction = point._instruction

								lineno = instruction.lineno
								col_offset = instruction.col_offset

								index_in_block = instruction._parent_body.index(instruction)

								instruction._parent_body.insert(index_in_block+1, instrument_ast)

							else:
								global_atom_index = atoms.index(atom)

								potential_free_variables[m][bind_variable_index][atom_index] = []

								for (n, point) in enumerate(points):

									# send the instrumentation point to the verdict server and get its ID in the database
									atom_index_in_db = atom_index_to_db_index[atom_index]
									instrumentation_point_dictionary = {
										"binding" : binding_db_id,
										"serialised_condition_sequence" : map(pickle.dumps, point._previous_edge._condition if type(point) is CFGVertex else point._condition),
										"reaching_path_length" : point._path_length if type(point) is CFGVertex else point._target_state._path_length,
										"atom" : atom_index_to_db_index[atom_index]
									}
									print(instrumentation_point_dictionary)
									serialised_dictionary = json.dumps(instrumentation_point_dictionary)
									try:
										instrumentation_point_db_id = int(post_to_verdict_server("store_instrumentation_point/", data=serialised_dictionary))
									except:
										print("There was a problem with the verdict server at '%s'.  Instrumentation cannot be completed." % VERDICT_SERVER_URL)
										exit()


									if type(atom) is formula_tree.TransitionDurationInInterval:

										coordinate_triple = "[%i][%i][%i]" % (m, bind_variable_index, atom_index)

										timer_start_statement = "__timer_s = datetime.datetime.now()"
										timer_end_statement = "__timer_e = datetime.datetime.now()"
										# we put a pair (index in static qd, index in instrumentation points)
										# this determines the point in the static cfg that will be executed
										print("point %s has path length %s" % (str(point), str(point._target_state._path_length)))
										time_difference_statement = ("__duration = __timer_e - __timer_s; %s((\"%s\", \"instrument\", \"%s\", %i, %i, %i, %i, __duration, %i, %i, %s, %i, %i, %i));") %\
											(verification_instruction, formula_hash, instrument_function_qualifier, m, bind_variable_index,
												atom_index, n, atoms.index(atom), point._instruction.lineno, map(pickle.dumps, point._condition),
												point._target_state._path_length, instrumentation_point_db_id, global_atom_index)

										print("Argument specification:")
										print(
											dict(
												[(key, getattr(point._instruction.value, key)) for key in dir(point._instruction.value)]
											)
										)

										start_ast = ast.parse(timer_start_statement).body[0]
										end_ast = ast.parse(timer_end_statement).body[0]
										difference_ast = ast.parse(time_difference_statement).body[0]
										queue_ast = ast.parse(time_difference_statement).body[1]

										start_ast.lineno = point._instruction.lineno
										start_ast.col_offset = point._instruction.col_offset
										end_ast.lineno = point._instruction.lineno
										end_ast.col_offset = point._instruction.col_offset
										difference_ast.lineno = point._instruction.lineno
										difference_ast.col_offset = point._instruction.col_offset
										queue_ast.lineno = point._instruction.lineno
										queue_ast.col_offset = point._instruction.col_offset
                                                                                

										index_in_block = point._instruction._parent_body.index(point._instruction)

										# insert instruments in reverse order

										point._instruction._parent_body.insert(index_in_block+1, queue_ast)
										# the split instruction should be between the difference computation, and before the queue insertion
										#point._instruction._parent_body.insert(index_in_block+1, split_ast)
										point._instruction._parent_body.insert(index_in_block+1, difference_ast)
										point._instruction._parent_body.insert(index_in_block+1, end_ast)
										point._instruction._parent_body.insert(index_in_block, start_ast)

									elif type(atom) in [formula_tree.StateValueInInterval, formula_tree.StateValueEqualTo, formula_tree.StateValueInOpenInterval]:

										# we are instrumenting a state, so store the value used in that state
										# in a new variable by accessing the existing variable
										# we place code in the edge leading to this vertex, since
										# that is the edge that contains the code that computes the state
										# this vertex models.

										incident_edge = point._previous_edge
										parent_block = incident_edge._instruction._parent_body

										# need to adjust this to record the entire state! <- possibly infeasible
										# we don't need to record the entire state since we record only what the atom needs to observe
										state_variable_alias = atom._name.replace(".", "_").replace("(", "__").replace(")", "__")
										record_state = ("record_state_%s = %s; %s((\"%s\", \"instrument\", \"%s\", %i, %i, %i, %i, {'%s' : record_state_%s}, %i, %i, %i, %i));") %\
											(state_variable_alias, atom._name, verification_instruction, formula_hash, instrument_function_qualifier, m,
												bind_variable_index, atom_index, n, atom._name, state_variable_alias, atoms.index(atom),
												incident_edge._instruction.lineno, instrumentation_point_db_id, global_atom_index)

										record_state_ast = ast.parse(record_state).body[0]
										queue_ast = ast.parse(record_state).body[1]

										record_state_ast.lineno = incident_edge._instruction.lineno
										record_state_ast.col_offset = incident_edge._instruction.col_offset
										queue_ast.lineno = incident_edge._instruction.lineno
										queue_ast.col_offset = incident_edge._instruction.col_offset

										index_in_block = parent_block.index(incident_edge._instruction)

										# insert instruments in reverse order

										parent_block.insert(index_in_block+1, queue_ast)
										parent_block.insert(index_in_block+1, record_state_ast)

				if EXPLANATION:
					# if explanation was turned on in the configuration file, insert path instruments.

					# insert path recording instruments - these don't depend on the formula being checked so
					# this is done independent of binding space computation
					for vertex_information in scfg.branch_initial_statements:
						if vertex_information[0] in ['conditional', 'try-catch']:
							if vertex_information[0] == 'conditional':
								print("Placing branch recording instrument for conditional with first instruction %s in block" % vertex_information[1])
								#instrument_code = "print(\"appending path condition %s inside conditional\")" % vertex_information[2]
								# send branching condition to verdict server, take the ID from the response and use it in the path recording instruments.
								condition_dict = {
									"serialised_condition" : pickle.dumps(vertex_information[2])
								}
							else:
								print("Placing branch recording instrument for try-catch with first instruction %s in block" % vertex_information[1])
								# send branching condition to verdict server, take the ID from the response and use it in the path recording instruments.
								condition_dict = {
									"serialised_condition" : vertex_information[2]
								}
							# if the condition already exists in the database, the verdict server will return the existing ID
							try:
								branching_condition_id = int(post_to_verdict_server("store_branching_condition/", data=json.dumps(condition_dict)))
							except:
								print("There was a problem with the verdict server at '%s'.  Instrumentation cannot be completed." % VERDICT_SERVER_URL)
								exit()
							instrument_code = "%s((\"%s\", \"path\", \"%s\", %i))" % (verification_instruction, formula_hash, instrument_function_qualifier, branching_condition_id)
							instrument_ast = ast.parse(instrument_code).body[0]
							instrument_ast.lineno = vertex_information[1]._parent_body[0].lineno
							instrument_ast.col_offset = vertex_information[1]._parent_body[0].col_offset
							index_in_parent = vertex_information[1]._parent_body.index(vertex_information[1])
							vertex_information[1]._parent_body.insert(index_in_parent, instrument_ast)
							print("Branch recording instrument placed")
						elif vertex_information[0] in ['post-conditional', 'post-try-catch']:
							if vertex_information[0] == 'post-conditional':
								print("processing post conditional path instrument")
								print(vertex_information)
								# need this to decide if we've left a conditional, since paths lengths reset after conditionals
								print("Placing branch recording instrument for end of conditional at %s - %i in parent block - line no %i" %\
									(vertex_information[1], vertex_information[1]._parent_body.index(vertex_information[1]), vertex_information[1].lineno))

								condition_dict = {
									"serialised_condition" : "conditional exited"
								}
							else:
								print("processing post try-catch path instrument")
								print(vertex_information)
								# need this to decide if we've left a conditional, since paths lengths reset after conditionals
								print("Placing branch recording instrument for end of try-catch at %s - %i in parent block - line no %i" %\
									(vertex_information[1], vertex_information[1]._parent_body.index(vertex_information[1]), vertex_information[1].lineno))

								condition_dict = {
									"serialised_condition" : "try-catch exited"
								}
							try:
								branching_condition_id = int(post_to_verdict_server("store_branching_condition/", data=json.dumps(condition_dict)))
							except:
								print("There was a problem with the verdict server at '%s'.  Instrumentation cannot be completed." % VERDICT_SERVER_URL)
								exit()
							instrument_code = "%s((\"%s\", \"path\", \"%s\", %i))" % (verification_instruction, formula_hash, instrument_function_qualifier, branching_condition_id)
							instrument_code_ast = ast.parse(instrument_code).body[0]
							instrument_code_ast.lineno = vertex_information[1].lineno+1
							instrument_code_ast.col_offset = vertex_information[1].col_offset

							index_in_parent = vertex_information[1]._parent_body.index(vertex_information[1])+1
							print(vertex_information[1]._parent_body)
							print(index_in_parent)
							vertex_information[1]._parent_body.insert(index_in_parent, instrument_code_ast)
							print(vertex_information[1]._parent_body)
						elif vertex_information[0] == 'loop':
							print("Placing branch recording instrument for loop with first instruction %s in body" % vertex_information[1])
							condition_dict = {
								"serialised_condition" : pickle.dumps(vertex_information[2])
							}
							# if the condition already exists in the database, the verdict server will return the existing ID
							try:
								branching_condition_id = int(post_to_verdict_server("store_branching_condition/", data=json.dumps(condition_dict)))
							except:
								print("There was a problem with the verdict server at '%s'.  Instrumentation cannot be completed." % VERDICT_SERVER_URL)
								exit()
							instrument_code_inside_loop = "%s((\"%s\", \"path\", \"%s\", %i))" % (verification_instruction, formula_hash, instrument_function_qualifier, branching_condition_id)
							instrument_inside_loop_ast = ast.parse(instrument_code_inside_loop).body[0]
							instrument_inside_loop_ast.lineno = vertex_information[1].lineno
							instrument_inside_loop_ast.col_offset = vertex_information[1].col_offset

							condition_dict = {
								"serialised_condition" : pickle.dumps(vertex_information[4])
							}
							# if the condition already exists in the database, the verdict server will return the existing ID
							try:
								branching_condition_id = int(post_to_verdict_server("store_branching_condition/", data=json.dumps(condition_dict)))
							except:
								print("There was a problem with the verdict server at '%s'.  Instrumentation cannot be completed." % VERDICT_SERVER_URL)
								exit()
							instrument_code_outside_loop = "%s((\"%s\", \"path\", \"%s\", %i))" % (verification_instruction, formula_hash, instrument_function_qualifier, branching_condition_id)
							instrument_outside_loop_ast = ast.parse(instrument_code_outside_loop).body[0]
							instrument_outside_loop_ast.lineno = vertex_information[3].lineno+1
							instrument_outside_loop_ast.col_offset = vertex_information[3].col_offset

							# insert at beginning of loop body
							inside_index_in_parent = vertex_information[1]._parent_body.index(vertex_information[1])
							# insert just after loop body
							outside_index_in_parent = vertex_information[3]._parent_body.index(vertex_information[3])+1

							vertex_information[1]._parent_body.insert(inside_index_in_parent, instrument_inside_loop_ast)
							vertex_information[3]._parent_body.insert(outside_index_in_parent, instrument_outside_loop_ast)
							print("Branch recording instrument for conditional placed")
			
				# finally, insert an instrument at the beginning to tell the monitoring thread that a new call of the function has started
				# and insert one at the end to signal a return
	
				# NOTE: only problem with this is that the "end" instrument is inserted before the return,
				# so a function call in the return statement maybe missed if it's part of verification...
				start_instrument = "%s((\"%s\", \"function\", \"%s\", \"start\", flask.g.request_time, \"%s\"))"\
							% (verification_instruction, formula_hash, instrument_function_qualifier, formula_hash)

				start_ast = ast.parse(start_instrument).body[0]
	
				start_ast.lineno = function_def.body[0].lineno
				start_ast.col_offset = function_def.body[0].col_offset
	
				function_def.body.insert(0, start_ast)
							
				# insert the end instrument before every return statement
				for end_vertex in scfg.return_statements:
					end_instrument = "%s((\"%s\", \"function\", \"%s\", \"end\", flask.g.request_time, \"%s\"))"\
										% (verification_instruction, formula_hash, instrument_function_qualifier, formula_hash)
					end_ast = ast.parse(end_instrument).body[0]

					end_ast.lineno = end_vertex._previous_edge._instruction.lineno
					end_ast.col_offset = end_vertex._previous_edge._instruction.col_offset

					print("inserting end instrument at line %i" % end_ast.lineno)

					insertion_position = len(end_vertex._previous_edge._instruction._parent_body)-1

					end_vertex._previous_edge._instruction._parent_body.insert(insertion_position, end_ast)

					print(end_vertex._previous_edge._instruction._parent_body)

				# if the last instruction in the ast is not a return statement, add an end instrument at the end
				if not(type(function_def.body[-1]) is ast.Return):
					end_instrument = "%s((\"%s\", \"function\", \"%s\", \"end\", flask.g.request_time, \"%s\"))"\
											% (verification_instruction, formula_hash, instrument_function_qualifier, formula_hash)
					end_ast = ast.parse(end_instrument).body[0]

					function_def.body.insert(len(function_def.body), end_ast)

				# write the instrumented scfg to a file
				instrumented_scfg = CFG()
				instrumented_scfg.process_block(top_level_block)
				write_scfg_to_file(instrumented_scfg, "%s-%s-%s-instrumented.gv" %
	                               	(file_name_without_extension.replace(".", ""), module.replace(".", "-"), function.replace(".", "-")))

				# write the instrumentation map to the intermediate dump file

				print(static_qd_to_point_map)

				# pickle the static qd map
				pickled_map = pickle.dumps(static_qd_to_point_map)

				# write to a file
				instrumentation_data_dump_file = "instrumentation_maps/module-%s-function-%s-property-%s.dump" %\
					(module.replace(".", "-"), function.replace(".", "-"), formula_hash)
				with open(instrumentation_data_dump_file, "wb") as h:
					h.write(pickled_map)

				# pickle binding space
				pickled_binding_space = pickle.dumps(bindings)

				# write to a file
				binding_space_dump_file = "binding_spaces/module-%s-function-%s-property-%s.dump" %\
					(module.replace(".", "-"), function.replace(".", "-"), formula_hash)
				with open(binding_space_dump_file, "wb") as h:
					h.write(pickled_binding_space)

				# write the index to hash mapping for properties
				pickled_index_hash = pickle.dumps(index_to_hash)
				index_to_hash_dump_file = "index_hash/module-%s-function-%s.dump" %\
					(module.replace(".", "-"), function.replace(".", "-"))
				with open(index_to_hash_dump_file, "wb") as h:
					h.write(pickled_index_hash)

				# now, load the map back in and reconstruct it to test
				instrumentation_map = pickle.loads(open(instrumentation_data_dump_file, "rb").read())

				print("reconstructed data:")

				print(instrumentation_map)

				print("-"*50)

		instrumented_code = compile(asts, "<ast>", "exec")

		# append an underscore to indicate that it's instrumented - removed for now
		instrumented_file_name = "%s.pyc" % file_name_without_extension

		print("writing instrumented code to %s" % instrumented_file_name)

		with open(instrumented_file_name, "wb") as h:
			h.write(py_compile.MAGIC)
			py_compile.wr_long(h, long(time.time()))
			marshal.dump(instrumented_code, h)

		# rename the original file so it doesn't overwrite bytecode at runtime with recompilation
		print("Renaming original file to .py.inst suffix")
		os.rename("%s.py" % file_name_without_extension, "%s.py.inst" % file_name_without_extension)
