"""
Module for performing instrumentation of the service based on the contents of the verification_config.py file.
"""

import sys
import traceback
import ast
import marshal
import pickle
import hashlib
import requests
import argparse
import os
import json
import base64
import datetime
import py_compile
import time
import pprint

# for now, we remove the final occurrence of VyPR from the first path to look in for modules
rindex = sys.path[0].rfind("/VyPR")
sys.path[0] = sys.path[0][:rindex] + sys.path[0][rindex + len("/VyPR"):]

# get the formula building functions before we evaluate the configuration code
from VyPR.QueryBuilding import *
from VyPR.SCFG.construction import *

VERDICT_SERVER_URL = None
VERBOSE = False
EXPLANATION = False
DRAW_GRAPHS = False
BYTECODE_EXTENSION = ".pyc"
vypr_module = "."
VERIFICATION_INSTRUCTION = "verification.send_event"
LOGS_TO_STDOUT = False

"""
Specification compilation.
"""


def get_function_asts_in_module(module_ast):
    """
    Given a Module AST object, traverse it and find all the functions.
    :param module_ast:
    :return: List of function names.
    """
    all_function_names = []
    # map elements of ast to pairs - left hand side is module path, right hand side is ast object
    stack = list(map(lambda item : ("", item), module_ast.body))
    while len(stack) > 0:
        top = stack.pop()
        module_path = top[0]
        ast_obj = top[1]
        if type(ast_obj) is ast.FunctionDef:
            all_function_names.append(("%s%s" % (top[0], top[1].name), top[1]))
        elif hasattr(ast_obj, "body"):
            if type(ast_obj) is ast.If:
                stack += map(
                    lambda item : (module_path, item),
                    ast_obj.body
                )
            elif type(ast_obj) is ast.ClassDef:
                stack += map(
                    lambda item: ("%s%s%s:" %
                                  (module_path, "." if (module_path != "" and module_path[-1] != ":") else "",
                                   ast_obj.name), item),
                    ast_obj.body
                )
    return all_function_names

def compile_queries(specification_file):
    """
    Given a specification file, complete the syntax and add imports, then inspect the objects
    used as keys to build the final dictionary structure.
    :param specification_file:
    :return: fully-expanded dictionary structure
    """
    logger.log("Compiling queries...")

    # load in verification config file
    # to do this, we read in the existing one, write a temporary one with imports added and import that one
    # this is to allow users to write specifications without caring about importing anything from QueryBuilding
    # when we read in the original specification code, we add verification_conf = {} to turn it into valid specification
    # syntax
    specification_code = "verification_conf = %s" % open(specification_file, "r").read()
    # replace empty lists with a fake property
    fake_property = "[Forall(q = changes('fake_vypr_var')).Check(lambda q : q('fake_vypr_var').equals(True))]"
    specification_code = specification_code.replace("[]", fake_property)
    with_imports = "from VyPR.QueryBuilding import *\n%s" % specification_code
    with open("VyPR_queries_with_imports.py", "w") as h:
        h.write(with_imports)

    # we now import the specification file
    from VyPR_queries_with_imports import verification_conf

    # this hierarchy will be populated as functions are found in the project that satisfy requirements
    compiled_hierarchy = {}

    # finally, we process the keys of the verification_conf dictionary
    # these keys are objects representing searches we should perform to generate the final expanded specification
    # with fully-qualified module names
    # we have this initial step to enable developers to write more sophisticated selection criteria the functions
    # to which they want to apply a query

    # we go through each function in the project we're instrumenting, check if there's a key in the initial
    # configuration file whose criteria are fulfilled by the function and, if so, add to the hierarchy
    for (root, directories, files) in os.walk("."):
        for file in files:
            # read in the file, traverse its AST structure to find all the functions and then determine
            # whether it satisfies a function selector
            # only consider Python files
            filename = os.path.join(root, file)
            module_name = "%s.%s" % (root[1:].replace("/", ""), file.replace(".py", ""))
            if (filename[-3:] == ".py"
                    and "VyPR" not in filename
                    and "venv" not in filename):
                # traverse the AST structure
                code = open(filename, "r").read()
                module_asts = ast.parse(code)
                function_asts = get_function_asts_in_module(module_asts)
                # process each function
                for (function_name, function_ast) in function_asts:
                    # construct the SCFG
                    scfg = CFG()
                    scfg.process_block(function_ast.body)
                    # process each function selector
                    for function_selector in verification_conf:
                        if type(function_selector) is Functions:
                            if function_selector.is_satisfied_by(function_ast, scfg):
                                print("adding '%s.%s'..." % (module_name, function_name))
                                # add to the compiled hierarchy
                                if not(compiled_hierarchy.get(module_name)):
                                    compiled_hierarchy[module_name] = {}
                                if not(compiled_hierarchy[module_name].get(function_name)):
                                    compiled_hierarchy[module_name][function_name] = verification_conf[function_selector]
                                else:
                                    compiled_hierarchy[module_name][function_name] += verification_conf[function_selector]
                        elif type(function_selector) is Module:
                            if (module_name == function_selector._module_name
                                    and function_name == function_selector._function_name):
                                # add to the final hierarchy
                                if not (compiled_hierarchy.get(module_name)):
                                    compiled_hierarchy[module_name] = {}
                                if not (compiled_hierarchy[module_name].get(function_name)):
                                    compiled_hierarchy[module_name][function_name] = verification_conf[function_selector]
                                else:
                                    compiled_hierarchy[module_name][function_name] += verification_conf[function_selector]

    # now merge the specifications written for specific functions with the compiled specifications
    for top_level in verification_conf:
        if type(top_level) is str:
            if compiled_hierarchy.get(top_level):
                for bottom_level in verification_conf[top_level]:
                    # if top_level was a string, for now bottom_level will be as well
                    # check whether the compiled part of the specification has already assigned a property here
                    if compiled_hierarchy.get(top_level) and compiled_hierarchy[top_level].get(bottom_level):
                        compiled_hierarchy[top_level][bottom_level] += verification_conf[top_level][bottom_level]
                    else:
                        compiled_hierarchy[top_level][bottom_level] = verification_conf[top_level][bottom_level]
            else:
                compiled_hierarchy[top_level] = {}
                for bottom_level in verification_conf[top_level]:
                    compiled_hierarchy[top_level][bottom_level] = verification_conf[top_level][bottom_level]

    return compiled_hierarchy


class InstrumentationLog(object):
    """
    Class to handle instrumentation logging.
    """

    def __init__(self, logs_to_stdout):
        self.logs_to_stdout = logs_to_stdout
        # check for log directory - create it if it doesn't exist
        if not (os.path.isdir("instrumentation_logs")):
            os.mkdir("instrumentation_logs")
        self.log_file_name = "instrumentation_logs/%s" \
                             % str(datetime.datetime.utcnow()). \
                                 replace(" ", "_").replace(":", "_").replace(".", "_").replace("-", "_")
        self.handle = None

    def start_logging(self):
        # open the log file in append mode
        self.handle = open(self.log_file_name, "a")

    def end_logging(self):
        self.handle.close()

    def log(self, message):
        if self.handle:
            message = "[VyPR instrumentation - %s] %s" % (str(datetime.datetime.utcnow()), message)
            self.handle.write("%s\n" % message)
            # flush the contents of the file to disk - this way we get a log even with an unhandled exception
            self.handle.flush()
            if self.logs_to_stdout:
                print(message)


"""
Bytecode writing functions - these depend on the Python version.
"""


def compile_bytecode_and_write(asts, file_name_without_extension):
    """Compile ASTs to bytecode then write to file.  The method we use depends on the Python version."""
    backup_file_name = "%s.py.inst" % file_name_without_extension

    instrumented_code = compile(asts, backup_file_name, "exec")

    # append an underscore to indicate that it's instrumented - removed for now
    instrumented_file_name = "%s%s" % (file_name_without_extension, BYTECODE_EXTENSION)

    logger.log("Writing instrumented bytecode to %s." % instrumented_file_name)

    import struct

    with open(instrumented_file_name, "wb") as h:
        h.write(py_compile.MAGIC)
        py_compile.wr_long(h, long(time.time()))
        # the write operation is the same regardless of Python version
        marshal.dump(instrumented_code, h)

    # rename the original file so it doesn't overwrite bytecode at runtime with recompilation
    logger.log("Renaming original file to .py.inst suffix")
    os.rename("%s.py" % file_name_without_extension, "%s.py.inst" % file_name_without_extension)


"""
End of bytecode writing functions.
"""


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
            if not (edge in traversed_edges):
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
    Given a sequence of quantifiers over symbolic states/edges in the given scfg, compute the space of bindings that
    can be given to the formula to which this quantifier sequence is applied. The current_binding given may be
    partial, but represents the current point in the space of bindings upto which we have traversed.
    """

    if len(current_binding) == 0:
        # we've just started - compute the static qd for the first quantifier,
        # then iterate over it and recurse into the list of quantifiers for each element
        if type(list(quantifier_sequence._bind_variables)[0]) is StaticState:
            if list(quantifier_sequence._bind_variables)[0]._name_changed:
                # a name was given as selection criteria
                variable_changed = list(quantifier_sequence._bind_variables)[0]._name_changed
                qd = list(filter(lambda symbolic_state: symbolic_state._name_changed == variable_changed \
                                                        or variable_changed in symbolic_state._name_changed,
                                 scfg.vertices))
                # we also check loop variables
                # when instruments are placed, if a loop vertex is processed instrumentation will change accordingly
                for vertex in scfg.vertices:
                    if vertex._name_changed == ["loop"]:
                        if (type(vertex._structure_obj.target) is ast.Name and
                                vertex._structure_obj.target.id == variable_changed):
                            # the variable we're looking for was found as a simple loop variable
                            qd.append(vertex)
                            print("adding loop vertex to static binding")
                        elif (type(vertex._structure_obj.target) is ast.Tuple and
                              variable_changed in list(map(lambda item: item.id, vertex._structure_obj.target))):
                            # the loop variable we're looking for was found inside a tuple
                            qd.append(vertex)
            else:
                qd = []
                # a list of coordinates were given
                if type(list(quantifier_sequence._bind_variables)[0]._instruction_coordinates) is list:
                    coordinates = list(quantifier_sequence._bind_variables)[0]._instruction_coordinates
                else:
                    coordinates = [list(quantifier_sequence._bind_variables)[0]._instruction_coordinates]
                for coordinate in coordinates:
                    # get all vertices whose previous edges have statements with matching lineno values,
                    # sort the col_offset values in ascending order, then get the vertex at the index
                    # specified by the coordinate
                    if type(coordinate) is int:
                        line_number = coordinate
                        offset = 0
                    else:
                        line_number = coordinate[0]
                        if len(coordinate) == 1:
                            offset = 0
                        else:
                            offset = coordinate[1]
                    relevant_vertices = list(filter(
                        lambda symbolic_state: not (symbolic_state._previous_edge is None) \
                                               and not (type(symbolic_state._previous_edge._instruction) is str) \
                                               and symbolic_state._previous_edge._instruction.lineno == line_number,
                        scfg.vertices
                    ))
                    relevant_vertices.sort(key=lambda vertex: vertex._previous_edge._instruction.col_offset)
                    relevant_vertex = relevant_vertices[offset]
                    qd.append(relevant_vertex)
        elif type(list(quantifier_sequence._bind_variables)[0]) is StaticTransition:
            variable_operated_on = list(quantifier_sequence._bind_variables)[0]._operates_on
            relevant_target_vertices = list(filter(
                lambda symbolic_state: symbolic_state._name_changed == variable_operated_on \
                                       or variable_operated_on in symbolic_state._name_changed,
                scfg.vertices
            ))
            qd = list(map(lambda symbolic_state: symbolic_state._previous_edge, relevant_target_vertices))

        binding_space = []
        # recurse with (possibly partial) bindings
        for element in qd:
            binding_space += compute_binding_space(quantifier_sequence, scfg, reachability_map, [element])

        logger.log("Computed whole binding space")
        logger.log(binding_space)
        return binding_space
    elif len(current_binding) < len(list(quantifier_sequence._bind_variables)):
        # we have a partial binding
        # find the next quantifier
        next_index = len(current_binding)
        next_quantifier = list(quantifier_sequence._bind_variables)[next_index]
        # find the position in the quantifier sequence on which the next quantifier depends
        index_in_quantifier_sequence = list(quantifier_sequence._bind_variables).index(
            next_quantifier._required_binding)
        # get the current value at that position in the binding we have
        current_binding_value = current_binding[index_in_quantifier_sequence]
        # use the type of the qd we need to traverse the scfg from this point
        if type(next_quantifier) is StaticState:
            logger.log("Computing unbounded future states according to %s" % next_quantifier)
            # TODO: implement state-based unbounded quantification, hasn't been needed yet
        elif type(next_quantifier) is StaticTransition:
            logger.log("Computing unbounded future transitions according to %s using binding %s" % (
                next_quantifier, current_binding))
            # only works for vertex inputs this has to cater for edges that are both assignments and function calls (
            # assignments of function call return values)
            qd = list(filter(lambda edge: hasattr(edge, "_operates_on") and \
                                          (edge._operates_on == next_quantifier._operates_on or \
                                           next_quantifier._operates_on in edge._operates_on),
                             reachability_map[current_binding_value]))

            # compute the bindings from this new qd
            binding_space = []
            for element in qd:
                binding_space += compute_binding_space(quantifier_sequence, scfg, reachability_map,
                                                       current_binding + [element])
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
        elif n == len(function_qualifier) - 1:
            tokens.append(function_qualifier[last_position:])

    return tokens


def get_file_from_qualifier(qualifier_chain):
    """
    Given a qualifier chain that points to a function/method, find the file name in which the function/module is found.
    """
    # for now, just modify the string given and use that as the filename
    # the importlib method was accidentally starting the service's monitoring thread
    logger.log("Getting file from qualifier %s" % qualifier_chain)

    # get the subsequence of the qualifier chain that can be read in as a file
    # the remainder of the qualifier chain will be pointing to something in that file
    index_of_first_dot = qualifier_chain.index(".")
    filename = "".join(qualifier_chain[0:index_of_first_dot]) + ".py"

    return filename


def get_function_from_qualifier(qualifier_chain):
    index_of_first_dot = qualifier_chain.index(".")
    function_qualifier = qualifier_chain[index_of_first_dot + 1:]
    return function_qualifier


def write_scfg_to_file(scfg, file_name):
    """
    Given an scfg and a file name, write the scfg in dot format to the file.
    """
    if DRAW_GRAPHS:
        from graphviz import Digraph
        graph = Digraph()
        graph.attr("graph", splines="true", fontsize="10")
        shape = "rectangle"
        for vertex in scfg.vertices:
            graph.node(str(id(vertex)), str(vertex._name_changed), shape=shape)
            for edge in vertex.edges:
                graph.edge(
                    str(id(vertex)),
                    str(id(edge._target_state)),
                    "%s - %s - path length = %s" % \
                    (str(edge._operates_on),
                     edge._condition,
                     str(edge._target_state._path_length))
                )
        graph.render(file_name)
        logger.log("Writing SCFG to file '%s'." % file_name)


def post_to_verdict_server(url, data):
    """
    Given a url (extension of the base URL set by configuration) and some data, send a post request to the verdict server.
    """
    global VERDICT_SERVER_URL
    response = requests.post(os.path.join(VERDICT_SERVER_URL, url), data).text
    return response


def is_verdict_server_reachable():
    """Try to query the index page of the verdict server."""
    global VERDICT_SERVER_URL
    try:
        requests.get(VERDICT_SERVER_URL)
        return True
    except:
        return False


def read_configuration(file):
    """
    Read in 'file', parse into an object and return.
    """
    with open(file, "r") as h:
        contents = h.read()

    return json.loads(contents)


def get_instrumentation_points_from_comp_sequence(value_from_binding, moves):
    """
    Given a starting point (value_from_binding) and a set of moves,
    traverse the SCFG and determine the set of instrumentation points.
    """

    # iterate through the moves we have to make,
    # using the type of the operator used in the move to compute the points we have to instrument
    # we set the default set to include just the current binding
    # for the case where no transformation happens
    instrumentation_points = [value_from_binding]
    # currently only works for a single move
    # for multiple moves we need to apply the transformation to each "previous" instrumentation point
    # TODO: this code needs to be changed to support nesting.
    for move in moves:
        if type(move) is NextStaticTransition:
            calls = []
            if type(value_from_binding) is CFGVertex:
                scfg.next_calls(value_from_binding, move._operates_on, calls, marked_vertices=[])
            elif type(value_from_binding) is CFGEdge:
                scfg.next_calls(value_from_binding._target_state, move._operates_on, calls, marked_vertices=[])
            instrumentation_points = calls
        elif type(move) in [SourceStaticState, DestinationStaticState]:
            # we don't need to do anything with these yet
            pass

    return instrumentation_points


def instrument_point_state(state, name, point, binding_space_indices,
                           atom_index, atom_sub_index, instrumentation_point_db_ids,
                           measure_attribute=None):
    """
    state is the PyCFTL object, and point is the part of the SCFG found by traversal.
    """
    global VERIFICATION_INSTRUCTION

    logger.log("Instrumenting point %s" % point)

    if measure_attribute == "length":
        state_variable_alias = name.replace(".", "_").replace("(", "__").replace(")", "__")
        state_recording_instrument = "record_state_%s = len(%s); " % (state_variable_alias, name)
        time_attained_instrument = "time_attained_%s = vypr.get_time('point instrument');" % state_variable_alias
        time_attained_variable = "time_attained_%s" % state_variable_alias
    elif measure_attribute == "type":
        state_variable_alias = name.replace(".", "_").replace("(", "__").replace(")", "__")
        state_recording_instrument = "record_state_%s = type(%s).__name__; " % (state_variable_alias, name)
        time_attained_instrument = "time_attained_%s = vypr.get_time('point instrument');" % state_variable_alias
        time_attained_variable = "time_attained_%s" % state_variable_alias
    elif measure_attribute == "time_attained":
        state_variable_alias = "time_attained_%i" % atom_sub_index
        state_recording_instrument = "record_state_%s = vypr.get_time('point instrument'); " % state_variable_alias
        time_attained_instrument = state_recording_instrument
        time_attained_variable = "record_state_%s" % state_variable_alias
        # the only purpose here is to match what is expected in the monitoring algorithm
        name = "time"
    else:
        state_variable_alias = name.replace(".", "_").replace("(", "__").replace(")", "__")
        state_recording_instrument = "record_state_%s = %s; " % (state_variable_alias, name)
        time_attained_instrument = "time_attained_%s = vypr.get_time('point instrument');" % state_variable_alias
        time_attained_variable = "time_attained_%s" % state_variable_alias

    # note that observed_value is used three times:
    # 1) to capture the time attained by the state for checking of a property - this is duplicated
    #    because we have the start and end time of the state, which is the same because states are instantaneous.
    # 3) to capture the time at which an observation was received - it makes sense that these times would
    #    be the same.
    instrument_tuple = ("'{formula_hash}', 'instrument', '{function_qualifier}', {binding_space_index}, "
                        "{atom_index}, {atom_sub_index}, {instrumentation_point_db_id}, {time_attained}, "
                        "{time_attained}, {{ '{atom_program_variable}' : {observed_value} }}, __thread_id") \
        .format(
        formula_hash=formula_hash,
        function_qualifier=instrument_function_qualifier,
        binding_space_index=binding_space_indices,
        atom_index=atom_index,
        atom_sub_index=atom_sub_index,
        instrumentation_point_db_id=instrumentation_point_db_ids,
        atom_program_variable=name,
        time_attained=time_attained_variable,
        observed_value=("record_state_%s" % state_variable_alias)
    )
    state_recording_instrument += "%s((%s))" % (VERIFICATION_INSTRUCTION, instrument_tuple)

    time_attained_ast = ast.parse(time_attained_instrument).body[0]
    record_state_ast = ast.parse(state_recording_instrument).body[0]
    queue_ast = ast.parse(state_recording_instrument).body[1]

    if type(state) is SourceStaticState or type(state) is DestinationStaticState:
        # if the state we're measuring a property of is derived from a source/destination operator,
        # then the instrumentation point we're given is an SCFG edge which contains
        # an instruction for us to place a state recording instrument before

        logger.log("Adding state recording instrument for source or target.")

        parent_block = point._instruction._parent_body

        record_state_ast.lineno = point._instruction.lineno
        record_state_ast.col_offset = point._instruction.col_offset
        queue_ast.lineno = point._instruction.lineno
        queue_ast.col_offset = point._instruction.col_offset

        index_in_block = parent_block.index(point._instruction)

        if type(state) is SourceStaticState:
            # for source state recording, we record the state, but only insert its value after
            # this is so triggers can be inserted before normal instruments without introducing
            # a special case for trigger insertion
            parent_block.insert(index_in_block, queue_ast)
            parent_block.insert(index_in_block, record_state_ast)
            parent_block.insert(index_in_block, time_attained_ast)
        elif type(state) is DestinationStaticState:
            parent_block.insert(index_in_block + 1, queue_ast)
            parent_block.insert(index_in_block + 1, record_state_ast)
            parent_block.insert(index_in_block + 1, time_attained_ast)

    else:

        if point._name_changed == ["loop"]:
            # we're instrumenting the change of a loop variable
            logger.log("Performing instrumentation for loop variable.")
            # determine the edge leading into the loop body
            for edge in point.edges:
                if edge._condition == ["enter-loop"]:
                    # place an instrument before the instruction on this edge
                    parent_block = edge._instruction._parent_body
                    record_state_ast.lineno = edge._instruction.lineno
                    record_state_ast.col_offset = edge._instruction.col_offset
                    queue_ast.lineno = edge._instruction.lineno
                    queue_ast.col_offset = edge._instruction.col_offset
                    index_in_block = parent_block.index(edge._instruction)
                    # insert instruments in reverse order
                    parent_block.insert(index_in_block + 1, queue_ast)
                    parent_block.insert(index_in_block + 1, record_state_ast)
                    parent_block.insert(index_in_block + 1, time_attained_ast)
        else:
            # we're instrumenting a normal vertex where there is an explicit instruction
            logger.log("Not source or destination state - performing normal instrumentation.")
            incident_edge = point._previous_edge
            parent_block = incident_edge._instruction._parent_body

            record_state_ast.lineno = incident_edge._instruction.lineno
            record_state_ast.col_offset = incident_edge._instruction.col_offset
            queue_ast.lineno = incident_edge._instruction.lineno
            queue_ast.col_offset = incident_edge._instruction.col_offset

            index_in_block = parent_block.index(incident_edge._instruction)

            # insert instruments in reverse order

            parent_block.insert(index_in_block + 1, queue_ast)
            parent_block.insert(index_in_block + 1, record_state_ast)
            parent_block.insert(index_in_block + 1, time_attained_ast)


def instrument_point_transition(atom, point, binding_space_indices, atom_index,
                                atom_sub_index, instrumentation_point_db_ids):
    composition_sequence = derive_composition_sequence(atom)

    # if the composition sequence was derived from a mixed atom,
    # we use the atom_sub_index we're given to decide which sequence to take
    if type(composition_sequence) is dict:
        if atom_sub_index == 0:
            composition_sequence = composition_sequence["lhs"]
        else:
            composition_sequence = composition_sequence["rhs"]

    composition_sequence = list(reversed(composition_sequence))[:-1]

    if hasattr(composition_sequence[-1], "_record") and composition_sequence[-1]._record:
        states = []
        for var in composition_sequence[-1]._record:
            states.append("'%s' : %s" % (var, var))
        state_string = ", ".join(states)
        state_dict = "{%s}" % state_string
    else:
        state_dict = "{}"

    timer_start_statement = "__timer_s = vypr.get_time('transition instrument')"
    timer_end_statement = "__timer_e = vypr.get_time('transition instrument')"

    time_difference_statement = "__duration = __timer_e - __timer_s; "
    instrument_tuple = ("'{formula_hash}', 'instrument', '{function_qualifier}', {binding_space_index}," +
                        "{atom_index}, {atom_sub_index}, {instrumentation_point_db_id}, {obs_time}, {obs_end_time}, "
                        "{observed_value}, __thread_id, {state_dict}") \
        .format(
        formula_hash=formula_hash,
        function_qualifier=instrument_function_qualifier,
        binding_space_index=binding_space_indices,
        atom_index=atom_index,
        atom_sub_index=atom_sub_index,
        instrumentation_point_db_id=instrumentation_point_db_ids,
        obs_time="__timer_s",
        obs_end_time="__timer_e",
        observed_value="__duration",
        state_dict=state_dict
    )
    time_difference_statement += "%s((%s))" % (VERIFICATION_INSTRUCTION, instrument_tuple)

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

    point._instruction._parent_body.insert(index_in_block + 1, queue_ast)
    point._instruction._parent_body.insert(index_in_block + 1, difference_ast)
    point._instruction._parent_body.insert(index_in_block + 1, end_ast)
    point._instruction._parent_body.insert(index_in_block, start_ast)


def place_path_recording_instruments(scfg, instrument_function_qualifier, formula_hash):
    # insert path recording instruments - these don't depend on the formula being checked so
    # this is done independent of binding space computation
    for vertex_information in scfg.branch_initial_statements:
        logger.log("-" * 100)
        if vertex_information[0] in ['conditional', 'try-catch']:
            if vertex_information[0] == 'conditional':
                logger.log(
                    "Placing branch recording instrument for conditional with first instruction %s in "
                    "block" %
                    vertex_information[1])
                # instrument_code = "logger.log(\"appending path condition %s inside conditional\")"
                # % vertex_information[2] send branching condition to verdict server, take the ID
                # from the response and use it in the path recording instruments.
                condition_dict = {
                    "serialised_condition": vertex_information[2]
                }
            else:
                logger.log(
                    "Placing branch recording instrument for try-catch with first instruction %s in "
                    "block" %
                    vertex_information[1])
                # send branching condition to verdict server, take the ID from the response and use
                # it in the path recording instruments.
                condition_dict = {
                    "serialised_condition": vertex_information[2]
                }
            # if the condition already exists in the database, the verdict server will return the
            # existing ID
            try:
                branching_condition_id = int(post_to_verdict_server("store_branching_condition/",
                                                                    data=json.dumps(condition_dict)))
            except:
                traceback.print_exc()
                logger.log(
                    "There was a problem with the verdict server at '%s'.  Instrumentation cannot be "
                    "completed." % VERDICT_SERVER_URL)
                exit()
            instrument_code = "%s((\"%s\", \"path\", \"%s\", %i))" % (
                VERIFICATION_INSTRUCTION, formula_hash, instrument_function_qualifier,
                branching_condition_id)
            instrument_ast = ast.parse(instrument_code).body[0]
            index_in_parent = vertex_information[1]._parent_body.index(vertex_information[1])
            vertex_information[1]._parent_body.insert(index_in_parent, instrument_ast)
            logger.log("Branch recording instrument placed")
        elif vertex_information[0] == "conditional-no-else":
            # no else was present in the conditional, so we add a path recording instrument
            # to the else block
            logger.log("Placing branch recording instrument for conditional with no else")
            # send branching condition to verdict server, take the ID from the response and use it in
            # the path recording instruments.
            condition_dict = {
                "serialised_condition": vertex_information[2]
            }
            # if the condition already exists in the database, the verdict server will return the
            # existing ID
            try:
                branching_condition_id = int(post_to_verdict_server("store_branching_condition/",
                                                                    data=json.dumps(condition_dict)))
            except:
                traceback.print_exc()
                logger.log(
                    "There was a problem with the verdict server at '%s'.  Instrumentation cannot be "
                    "completed." % VERDICT_SERVER_URL)
                exit()
            instrument_code = "%s((\"%s\", \"path\", \"%s\", %i))" % (
                VERIFICATION_INSTRUCTION, formula_hash, instrument_function_qualifier,
                branching_condition_id)
            instrument_ast = ast.parse(instrument_code).body[0]
            vertex_information[1].orelse.insert(0, instrument_ast)
            logger.log("Branch recording instrument placed")
        elif vertex_information[0] in ['post-conditional', 'post-try-catch']:
            if vertex_information[0] == 'post-conditional':
                logger.log("Processing post conditional path instrument")
                logger.log(vertex_information)
                # need this to decide if we've left a conditional, since paths lengths reset after
                # conditionals
                logger.log(
                    "Placing branch recording instrument for end of conditional at %s - %i in parent "
                    "block - line no %i" % \
                    (vertex_information[1],
                     vertex_information[1]._parent_body.index(vertex_information[1]),
                     vertex_information[1].lineno))

                condition_dict = {
                    "serialised_condition": "conditional exited"
                }
            else:
                logger.log("Processing post try-catch path instrument")
                logger.log(vertex_information)
                # need this to decide if we've left a conditional, since paths lengths reset after
                # conditionals
                logger.log(
                    "Placing branch recording instrument for end of try-catch at %s - %i in parent "
                    "block - line no %i" % \
                    (vertex_information[1],
                     vertex_information[1]._parent_body.index(vertex_information[1]),
                     vertex_information[1].lineno))

                condition_dict = {
                    "serialised_condition": "try-catch exited"
                }
            try:
                branching_condition_id = int(post_to_verdict_server("store_branching_condition/",
                                                                    data=json.dumps(condition_dict)))
            except:
                traceback.print_exc()
                logger.log(
                    "There was a problem with the verdict server at '%s'.  Instrumentation cannot be "
                    "completed." % VERDICT_SERVER_URL)
                exit()
            instrument_code = "%s((\"%s\", \"path\", \"%s\", %i))" % (
                VERIFICATION_INSTRUCTION, formula_hash, instrument_function_qualifier,
                branching_condition_id)
            instrument_code_ast = ast.parse(instrument_code).body[0]

            index_in_parent = vertex_information[1]._parent_body.index(vertex_information[1]) + 1
            logger.log(vertex_information[1]._parent_body)
            logger.log(index_in_parent)
            vertex_information[1]._parent_body.insert(index_in_parent, instrument_code_ast)
            logger.log(vertex_information[1]._parent_body)
        elif vertex_information[0] == 'loop':
            logger.log(
                "Placing branch recording instrument for loop with first instruction %s in body" %
                vertex_information[1])
            condition_dict = {
                "serialised_condition": vertex_information[2]
            }
            # if the condition already exists in the database, the verdict server will return the
            # existing ID
            try:
                branching_condition_id = int(post_to_verdict_server("store_branching_condition/",
                                                                    data=json.dumps(condition_dict)))
            except:
                traceback.print_exc()
                logger.log(
                    "There was a problem with the verdict server at '%s'.  Instrumentation cannot be "
                    "completed." % VERDICT_SERVER_URL)
                exit()
            instrument_code_inside_loop = "%s((\"%s\", \"path\", \"%s\", %i))" % (
                VERIFICATION_INSTRUCTION, formula_hash, instrument_function_qualifier,
                branching_condition_id)
            instrument_inside_loop_ast = ast.parse(instrument_code_inside_loop).body[0]

            condition_dict = {
                "serialised_condition": vertex_information[4]
            }
            # if the condition already exists in the database, the verdict server will return the
            # existing ID
            try:
                branching_condition_id = int(post_to_verdict_server("store_branching_condition/",
                                                                    data=json.dumps(condition_dict)))
            except:
                traceback.print_exc()
                logger.log(
                    "There was a problem with the verdict server at '%s'.  Instrumentation cannot be "
                    "completed." % VERDICT_SERVER_URL)
                exit()
            instrument_code_outside_loop = "%s((\"%s\", \"path\", \"%s\", %i))" % (
                VERIFICATION_INSTRUCTION, formula_hash, instrument_function_qualifier,
                branching_condition_id)
            instrument_outside_loop_ast = ast.parse(instrument_code_outside_loop).body[0]

            # insert at beginning of loop body
            inside_index_in_parent = vertex_information[1]._parent_body.index(vertex_information[1])
            # insert just after loop body
            outside_index_in_parent = vertex_information[3]._parent_body.index(
                vertex_information[3]) + 1

            vertex_information[1]._parent_body.insert(inside_index_in_parent,
                                                      instrument_inside_loop_ast)
            vertex_information[3]._parent_body.insert(outside_index_in_parent,
                                                      instrument_outside_loop_ast)
            logger.log("Branch recording instrument for conditional placed")

    logger.log("=" * 100)


def place_function_begin_instruments(function_def, formula_hash, instrument_function_qualifier):
    # NOTE: only problem with this is that the "end" instrument is inserted before the return,
    # so a function call in the return statement maybe missed if it's part of verification...
    thread_id_capture = "import threading; __thread_id = threading.current_thread().ident;"
    vypr_start_time_instrument = "vypr_start_time = vypr.get_time('begin instrument');"
    start_instrument = \
        "%s((\"%s\", \"function\", \"%s\", \"start\", vypr_start_time, \"%s\", __thread_id))" \
        % (VERIFICATION_INSTRUCTION, formula_hash, instrument_function_qualifier, formula_hash)

    threading_import_ast = ast.parse(thread_id_capture).body[0]
    thread_id_capture_ast = ast.parse(thread_id_capture).body[1]
    vypr_start_time_ast = ast.parse(vypr_start_time_instrument).body[0]
    start_ast = ast.parse(start_instrument).body[0]

    threading_import_ast.lineno = function_def.body[0].lineno
    thread_id_capture_ast.lineno = function_def.body[0].lineno
    vypr_start_time_ast.lineno = function_def.body[0].lineno
    start_ast.lineno = function_def.body[0].lineno

    function_def.body.insert(0, start_ast)
    function_def.body.insert(0, thread_id_capture_ast)
    function_def.body.insert(0, threading_import_ast)
    function_def.body.insert(0, vypr_start_time_ast)


def place_function_end_instruments(function_def, scfg, formula_hash, instrument_function_qualifier):
    # insert the end instrument before every return statement
    for end_vertex in scfg.return_statements:
        end_instrument = \
            "%s((\"%s\", \"function\", \"%s\", \"end\", flask.g.request_time, \"%s\", __thread_id, " \
            "vypr.get_time('end instrument')))" \
            % (VERIFICATION_INSTRUCTION, formula_hash, instrument_function_qualifier, formula_hash)
        end_ast = ast.parse(end_instrument).body[0]

        end_ast.lineno = end_vertex._previous_edge._instruction._parent_body[-1].lineno

        logger.log("Placing end instrument at line %i." % end_ast.lineno)

        insertion_position = len(end_vertex._previous_edge._instruction._parent_body) - 1

        end_vertex._previous_edge._instruction._parent_body.insert(insertion_position, end_ast)

        logger.log(end_vertex._previous_edge._instruction._parent_body)

    # if the last instruction in the ast is not a return statement, add an end instrument at the end
    if not (type(function_def.body[-1]) is ast.Return):
        end_instrument = "%s((\"%s\", \"function\", \"%s\", \"end\", flask.g.request_time, \"%s\", __thread_id, " \
                         "vypr.get_time('end instrument')))" \
                         % (VERIFICATION_INSTRUCTION, formula_hash, instrument_function_qualifier,
                            formula_hash)
        end_ast = ast.parse(end_instrument).body[0]

        logger.log("Placing end instrument at the end of the function body.")

        function_def.body.insert(len(function_def.body), end_ast)


if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Instrumentation for VyPR.')
    parser.add_argument('--verbose', action='store_true',
                        help='If given, output will be turned on for the instrumentation module.', required=False)
    parser.add_argument('--draw-graphs', action='store_true',
                        help='If given, SCFGs derived from functions to be monitored will be written to GV files and '
                             'compiled into PDFs.',
                        required=False)
    parser.add_argument('--std-output', action='store_true',
                        help='If given, every message written to the instrumentation log will also be written to '
                             'standard out.',
                        required=False)

    args = parser.parse_args()

    VERBOSE = args.verbose
    DRAW_GRAPHS = args.draw_graphs
    LOGS_TO_STDOUT = args.std_output

    inst_configuration = read_configuration("vypr.config")

    VERDICT_SERVER_URL = inst_configuration.get("verdict_server_url") \
        if inst_configuration.get("verdict_server_url") else "http://localhost:9001/"
    EXPLANATION = inst_configuration.get("explanation") == "on"
    BYTECODE_EXTENSION = inst_configuration.get("bytecode_extension") \
        if inst_configuration.get("bytecode_extension") else ".pyc"
    VYPR_MODULE = inst_configuration.get("vypr_module") \
        if inst_configuration.get("vypr_module") else ""
    VERIFICATION_INSTRUCTION = "vypr.send_event"
    # VERIFICATION_INSTRUCTION = "print"

    machine_id = ("%s-" % inst_configuration.get("machine_id")) if inst_configuration.get("machine_id") else ""

    # first, check that the verdict server is reachable
    if not (is_verdict_server_reachable()):
        print("Verdict server is not reachable.  Ending instrumentation - nothing has been done.")
        exit()

    # initialise instrumentation logger
    logger = InstrumentationLog(LOGS_TO_STDOUT)
    # set up the file handle
    logger.start_logging()

    # reset code to non-instrumented
    for directory in os.walk("."):
        for file in directory[2]:
            if not ("venv" in file):
                f = os.path.join(directory[0], file)
                if ".py.inst" in f:
                    # rename to .py
                    os.rename(f, f.replace(".py.inst", ".py"))
                    # delete bytecode
                    os.remove(f.replace(".py.inst", BYTECODE_EXTENSION))
                    logger.log("Reset file %s to uninstrumented version." % f)

    logger.log("Importing and compiling PyCFTL queries...")
    # load in verification config file
    # to do this, we read in the existing one, write a temporary one with imports added and import that one
    # this is to allow users to write specifications without caring about importing anything from QueryBuilding
    """specification_code = open("VyPR_queries.py", "r").read()
    # replace empty lists with a fake property
    fake_property = "[Forall(q = changes('fake_vypr_var')).Check(lambda q : q('fake_vypr_var').equals(True))]"
    specification_code = specification_code.replace("[]", fake_property)
    with_imports = "from VyPR.QueryBuilding import *\n%s" % specification_code
    with open("VyPR_queries_with_imports.py", "w") as h:
        h.write(with_imports)
    from VyPR_queries_with_imports import verification_conf"""

    # run specification compilation process
    print("This can take some time if your queries require static analysis over a lot of code.")
    verification_conf = compile_queries("VyPR_queries.py")

    verified_modules = verification_conf.keys()

    # for each verified function, find the file in which it is defined

    for module in verified_modules:

        logger.log("Processing module '%s'." % module)

        verified_functions = verification_conf[module].keys()

        file_name = module.replace(".", "/") + ".py"
        file_name_without_extension = module.replace(".", "/")

        # extract asts from the code in the file
        code = "".join(open(file_name, "r").readlines())
        asts = ast.parse(code)

        # add import for init_vypr module
        import_code = "from %s import vypr" % VYPR_MODULE
        import_ast = ast.parse(import_code).body[0]
        import_ast.lineno = asts.body[0].lineno
        import_ast.col_offset = asts.body[0].col_offset
        asts.body.insert(0, import_ast)

        # add vypr datetime import
        vypr_datetime_import = "from datetime import datetime as vypr_dt"
        datetime_import_ast = ast.parse(vypr_datetime_import).body[0]
        datetime_import_ast.lineno = asts.body[0].lineno
        datetime_import_ast.col_offset = asts.body[0].col_offset
        asts.body.insert(0, datetime_import_ast)

        # if we're using flask, we assume a certain architecture
        import_code = "import flask"
        import_asts = ast.parse(import_code)
        flask_import = import_asts.body[0]
        asts.body.insert(0, flask_import)

        for function in verified_functions:

            logger.log("Processing function '%s'." % function)

            # we replace . with : in function definitions to make sure we can distinguish between module
            # and class navigation later on
            instrument_function_qualifier = "%s%s.%s" % (machine_id, module, function.replace(".", ":"))

            index_to_hash = []

            qualifier_subsequence = get_qualifier_subsequence(function)
            function_name = function.split(".")

            # find the function definition

            actual_function_name = function_name[-1]
            hierarchy = function_name[:-1]

            current_step = asts.body

            # traverse sub structures

            for step in hierarchy:
                current_step = list(filter(
                    lambda entry: (type(entry) is ast.ClassDef and
                                   entry.name == step),
                    current_step
                ))[0]

            # find the final function definition

            function_def = list(filter(
                lambda entry: (type(entry) is ast.FunctionDef and
                               entry.name == actual_function_name),
                current_step.body if type(current_step) is ast.ClassDef else current_step
            ))[0]

            # get all reference variables
            reference_variables = []
            for (formula_index, formula_structure) in enumerate(verification_conf[module][function]):
                for var in formula_structure._bind_variables:
                    if hasattr(var, "_treat_as_ref") and var._treat_as_ref:
                        reference_variables.append(var._name_changed)

            # construct the scfg of the code inside the function

            scfg = CFG(reference_variables=reference_variables)
            scfg_vertices = scfg.process_block(function_def.body)

            top_level_block = function_def.body

            logger.log("SCFG constructed.")

            # write scfg to file
            write_scfg_to_file(scfg, "%s-%s-%s.gv" %
                               (file_name_without_extension.replace(".", ""), module.replace(".", "-"),
                                function.replace(".", "-")))

            # for each property, instrument the function for that property

            for (formula_index, formula_structure) in enumerate(verification_conf[module][function]):

                logger.log("Instrumenting for PyCFTL formula %s" % formula_structure)

                # we should be able to use the same scfg for each stage of instrumentation,
                # since when we insert instruments we recompute the position of the instrumented instruction

                atoms = formula_structure._formula_atoms

                formula_hash = hashlib.sha1()
                serialised_bind_variables = base64.encodestring(pickle.dumps(formula_structure.bind_variables))
                formula_hash.update(serialised_bind_variables)
                serialised_bind_variables = serialised_bind_variables.decode('ascii')
                serialised_formula_structure = base64.encodestring(
                    pickle.dumps(formula_structure.get_formula_instance())
                )
                formula_hash.update(serialised_formula_structure)
                serialised_formula_structure = serialised_formula_structure.decode('ascii')
                formula_hash = formula_hash.hexdigest()
                serialised_atom_list = list(
                    map(lambda item: base64.encodestring(pickle.dumps(item)).decode('ascii'), atoms)
                )

                # note that this also means giving an empty list [] will result in path instrumentation
                # without property instrumentation
                if EXPLANATION:
                    logger.log("=" * 100)
                    logger.log("Placing path recording instruments.")
                    place_path_recording_instruments(scfg, instrument_function_qualifier, formula_hash)

                # update the index -> hash map
                index_to_hash.append(formula_hash)

                logger.log("with formula hash '%s'" % formula_hash)

                # construct reachability of the SCFG
                # and derive the binding space based on the formula

                reachability_map = construct_reachability_map(scfg)
                bindings = compute_binding_space(formula_structure, scfg, reachability_map)
                print(bindings)

                logger.log("Set of static bindings computed is")
                logger.log(str(bindings))

                # using these bindings, we now need to instrument the code
                # and then store the (bind space index, bind var index, atom index)
                # so the instrumentation mappings can be recovered at runtime without recomputation

                static_qd_to_point_map = {}
                vertices_to_triple_list = {}

                # we attach indices to atoms because we need their index in the set of atoms
                # of the relevant formula
                initial_property_dict = {
                    "formula_hash": formula_hash,
                    "function": instrument_function_qualifier,
                    "serialised_formula_structure": serialised_formula_structure,
                    "serialised_bind_variables": serialised_bind_variables,
                    "serialised_atom_list": list(enumerate(serialised_atom_list))
                }

                # send instrumentation data to the verdict database
                try:
                    logger.log(
                        "Sending property with hash '%s' for function '%s' in module '%s' to server." %
                        (formula_hash, function, module))
                    response = str(post_to_verdict_server("store_property/", data=json.dumps(initial_property_dict)))
                    response = json.loads(response)
                    atom_index_to_db_index = response["atom_index_to_db_index"]
                    function_id = response["function_id"]
                except:
                    logger.log("Unforeseen exception when sending property to verdict server:")
                    logger.log(traceback.format_exc())
                    logger.log(
                        "There was a problem with the verdict server at '%s'.  Instrumentation cannot be completed."
                        % VERDICT_SERVER_URL)
                    exit()

                logger.log("Processing set of static bindings:")

                for (m, element) in enumerate(bindings):

                    logger.log("Processing binding %s" % element)

                    # send the binding to the verdict server

                    line_numbers = []
                    for el in element:
                        if type(el) is CFGVertex:
                            if el._name_changed != ["loop"]:
                                line_numbers.append(el._previous_edge._instruction.lineno)
                            else:
                                line_numbers.append(el._structure_obj.lineno)
                        else:
                            line_numbers.append(el._instruction.lineno)

                    binding_dictionary = {
                        "binding_space_index": m,
                        "function": function_id,
                        "binding_statement_lines": line_numbers
                    }
                    serialised_binding_dictionary = json.dumps(binding_dictionary)
                    try:
                        binding_db_id = int(
                            post_to_verdict_server("store_binding/", data=serialised_binding_dictionary))
                    except:
                        logger.log("Unforeseen exception when sending binding to verdict server:")
                        logger.log(traceback.format_exc())
                        logger.log(
                            "There was a problem with the verdict server at '%s'.  Instrumentation cannot be completed."
                            % VERDICT_SERVER_URL)
                        exit()

                    static_qd_to_point_map[m] = {}

                    for (atom_index, atom) in enumerate(atoms):

                        logger.log("Computing instrumentation points for atom %s." % atom)

                        static_qd_to_point_map[m][atom_index] = {}

                        if type(atom) in [formula_tree.StateValueEqualToMixed,
                                          formula_tree.StateValueLengthLessThanStateValueLengthMixed,
                                          formula_tree.TransitionDurationLessThanTransitionDurationMixed,
                                          formula_tree.TransitionDurationLessThanStateValueMixed,
                                          formula_tree.TransitionDurationLessThanStateValueLengthMixed,
                                          formula_tree.TimeBetweenInInterval,
                                          formula_tree.TimeBetweenInOpenInterval]:

                            # there may be multiple bind variables
                            composition_sequences = derive_composition_sequence(atom)

                            # get lhs and rhs bind variables
                            lhs_comp_sequence = composition_sequences["lhs"]
                            lhs_bind_variable = lhs_comp_sequence[-1]
                            lhs_bind_variable_index = list(formula_structure._bind_variables).index(lhs_bind_variable)
                            lhs_starting_point = element[lhs_bind_variable_index]

                            rhs_comp_sequence = composition_sequences["rhs"]
                            rhs_bind_variable = rhs_comp_sequence[-1]
                            rhs_bind_variable_index = list(formula_structure._bind_variables).index(rhs_bind_variable)
                            rhs_starting_point = element[rhs_bind_variable_index]

                            lhs_moves = list(reversed(lhs_comp_sequence[1:-1]))
                            rhs_moves = list(reversed(rhs_comp_sequence[1:-1]))

                            lhs_instrumentation_points = get_instrumentation_points_from_comp_sequence(
                                lhs_starting_point, lhs_moves)
                            rhs_instrumentation_points = get_instrumentation_points_from_comp_sequence(
                                rhs_starting_point, rhs_moves)

                            # 0 and 1 are for lhs and rhs respectively
                            static_qd_to_point_map[m][atom_index][0] = lhs_instrumentation_points
                            static_qd_to_point_map[m][atom_index][1] = rhs_instrumentation_points

                        else:

                            # just one composition sequence, so one set of instrumentation points

                            composition_sequence = derive_composition_sequence(atom)
                            bind_variable = composition_sequence[-1]
                            variable_index = list(formula_structure._bind_variables).index(bind_variable)
                            value_from_binding = element[variable_index]
                            moves = list(reversed(composition_sequence[1:-1]))
                            instrumentation_points = get_instrumentation_points_from_comp_sequence(value_from_binding,
                                                                                                   moves)

                            # for simple atoms, there is no lhs and rhs so we just use 0
                            static_qd_to_point_map[m][atom_index][0] = instrumentation_points

                logger.log("Finished computing instrumentation points.  Result is:")
                logger.log(static_qd_to_point_map)

                # now, perform the instrumentation

                # first step is to add triggers

                logger.log("Inserting triggers.")

                for (m, element) in enumerate(bindings):

                    for bind_variable_index in range(len(formula_structure.bind_variables.keys())):

                        logger.log("Adding trigger for static binding/bind variable %i/%i." % (m, bind_variable_index))

                        point = element[bind_variable_index]

                        instrument = "%s((\"%s\", \"trigger\", \"%s\", %i, %i))" % \
                                     (VERIFICATION_INSTRUCTION, formula_hash, instrument_function_qualifier, m,
                                      bind_variable_index)

                        instrument_ast = ast.parse(instrument).body[0]
                        if type(point) is CFGVertex:
                            if point._name_changed == ["loop"]:
                                # triggers for loop variables must be inserted inside the loop
                                # so we instantiate a new monitor for every iteration
                                for edge in point.edges:
                                    if edge._condition == ["enter-loop"]:
                                        instruction = edge._instruction
                            else:
                                instruction = point._previous_edge._instruction
                        else:
                            instruction = point._instruction

                        lineno = instruction.lineno
                        col_offset = instruction.col_offset

                        index_in_block = instruction._parent_body.index(instruction)

                        instrument_ast.lineno = instruction._parent_body[0].lineno

                        # insert triggers before the things that will be measured
                        instruction._parent_body.insert(index_in_block, instrument_ast)

                # we then invert the map we constructed from triples to instrumentation points so that we can avoid
                # overlap of instruments

                logger.log("Inverting instrumentation structure ready for optimisations.")

                point_to_triples = {}

                for (m, element) in enumerate(bindings):
                    for atom_index in static_qd_to_point_map[m].keys():
                        for sub_index in static_qd_to_point_map[m][atom_index].keys():
                            points = static_qd_to_point_map[m][atom_index][sub_index]
                            for (n, point) in enumerate(points):

                                if not (point_to_triples.get(point)):
                                    point_to_triples[point] = {}

                                atom_index_in_db = atom_index_to_db_index[atom_index]
                                # for now, we don't need serialised_condition_sequence so we just use a blank string
                                if type(point) is CFGVertex:
                                    if point._name_changed == ["loop"]:
                                        # find edge leading into loop body and use the path length for the destination
                                        # state
                                        for edge in point.edges:
                                            if edge._condition == ["enter-loop"]:
                                                reaching_path_length = edge._target_state._path_length
                                    else:
                                        reaching_path_length = point._path_length
                                else:
                                    reaching_path_length = point._target_state._path_length

                                instrumentation_point_dictionary = {
                                    "binding": binding_db_id,
                                    # "serialised_condition_sequence": list(
                                    #    map(pickle.dumps, point._previous_edge._condition
                                    #    if type(point) is CFGVertex else point._condition)
                                    # ),
                                    "serialised_condition_sequence": "",
                                    "reaching_path_length": reaching_path_length,
                                    "atom": atom_index_to_db_index[atom_index]
                                }
                                serialised_dictionary = json.dumps(instrumentation_point_dictionary)
                                try:
                                    instrumentation_point_db_id = int(
                                        post_to_verdict_server("store_instrumentation_point/",
                                                               data=serialised_dictionary))
                                except:
                                    logger.log("Unforeseen exception when sending instrumentation point to verdict "
                                               "server:")
                                    logger.log(traceback.format_exc())
                                    logger.log(
                                        "There was a problem with the verdict server at '%s'.  Instrumentation cannot "
                                        "be completed." % VERDICT_SERVER_URL)
                                    exit()

                                if not (point_to_triples[point].get(atom_index)):
                                    point_to_triples[point][atom_index] = {}
                                if not (point_to_triples[point][atom_index].get(sub_index)):
                                    point_to_triples[point][atom_index][sub_index] = []

                                point_to_triples[point][atom_index][sub_index].append([m, instrumentation_point_db_id])

                logger.log("Placing instruments based on inversion.")

                # we now insert the instruments

                for point in point_to_triples.keys():
                    logger.log("Placing instruments for point %s." % point)
                    for atom_index in point_to_triples[point].keys():
                        atom = atoms[atom_index]
                        for atom_sub_index in point_to_triples[point][atom_index].keys():
                            logger.log("Placing single instrument at %s for atom %s at index %i and sub index %i" % (
                                point, atom, atom_index, atom_sub_index))
                            list_of_lists = list(zip(*point_to_triples[point][atom_index][atom_sub_index]))

                            # extract the parameters for this instrumentation point
                            binding_space_indices = list_of_lists[0]
                            instrumentation_point_db_ids = list_of_lists[1]

                            if type(atom) is formula_tree.TransitionDurationInInterval:

                                instrument_point_transition(atom, point, binding_space_indices, atom_index,
                                                            atom_sub_index, instrumentation_point_db_ids)

                            elif type(atom) in [formula_tree.StateValueInInterval, formula_tree.StateValueEqualTo,
                                                formula_tree.StateValueInOpenInterval]:

                                instrument_point_state(atom._state, atom._name, point, binding_space_indices,
                                                       atom_index, atom_sub_index, instrumentation_point_db_ids)

                            elif type(atom) is formula_tree.StateValueTypeEqualTo:

                                instrument_point_state(atom._state, atom._name, point, binding_space_indices,
                                                       atom_index, atom_sub_index, instrumentation_point_db_ids,
                                                       measure_attribute="type")

                            elif type(atom) in [formula_tree.StateValueLengthInInterval]:
                                """
                                Instrumentation for the length of a value given is different
                                because we have to add len() to the instrument.
                                """

                                instrument_point_state(atom._state, atom._name, point, binding_space_indices,
                                                       atom_index, atom_sub_index, instrumentation_point_db_ids,
                                                       measure_attribute="length")

                            elif type(atom) in [formula_tree.StateValueEqualToMixed]:
                                """We're instrumenting multiple states, so we need to perform instrumentation on two 
                                separate points. """

                                # for each side of the atom (LHS and RHS), instrument the necessary points

                                logger.log(
                                    "instrumenting for a mixed atom %s with sub atom index %i" % (atom, atom_sub_index)
                                )

                                if atom_sub_index == 0:
                                    # we're instrumenting for the lhs
                                    logger.log("Placing left-hand-side instrument for SCFG object %s." % atom._lhs)
                                    instrument_point_state(atom._lhs, atom._lhs_name, point, binding_space_indices,
                                                           atom_index, atom_sub_index, instrumentation_point_db_ids)
                                else:
                                    # we're instrumenting for the rhs
                                    logger.log("Placing right-hand-side instrument for SCFG object %s." % atom._rhs)
                                    instrument_point_state(atom._rhs, atom._rhs_name, point, binding_space_indices,
                                                           atom_index, atom_sub_index, instrumentation_point_db_ids)

                            elif type(atom) in [formula_tree.StateValueLengthLessThanStateValueLengthMixed]:
                                """We're instrumenting multiple states, so we need to perform instrumentation on two 
                                separate points. """

                                # for each side of the atom (LHS and RHS), instrument the necessary points

                                logger.log(
                                    "instrumenting for a mixed atom %s with sub atom index %i" % (atom, atom_sub_index)
                                )

                                if atom_sub_index == 0:
                                    # we're instrumenting for the lhs
                                    logger.log("Placing left-hand-side instrument for SCFG object %s." % atom._lhs)
                                    instrument_point_state(atom._lhs, atom._lhs_name, point, binding_space_indices,
                                                           atom_index, atom_sub_index, instrumentation_point_db_ids,
                                                           measure_attribute="length")
                                else:
                                    # we're instrumenting for the rhs
                                    logger.log("Placing right-hand-side instrument for SCFG object %s." % atom._rhs)
                                    instrument_point_state(atom._rhs, atom._rhs_name, point, binding_space_indices,
                                                           atom_index, atom_sub_index, instrumentation_point_db_ids,
                                                           measure_attribute="length")

                            elif type(atom) is formula_tree.TransitionDurationLessThanTransitionDurationMixed:
                                """We're instrumenting multiple transitions, so we need to perform instrumentation on 
                                two separate points. """

                                # for each side of the atom (LHS and RHS), instrument the necessary points

                                logger.log(
                                    "Instrumenting for a mixed atom %s with sub atom index %i." % (atom, atom_sub_index)
                                )

                                if atom_sub_index == 0:
                                    # we're instrumenting for the lhs
                                    logger.log("placing lhs instrument for scfg object %s" % atom._lhs)
                                    instrument_point_transition(atom, point, binding_space_indices,
                                                                atom_index, atom_sub_index,
                                                                instrumentation_point_db_ids)
                                else:
                                    # we're instrumenting for the rhs
                                    logger.log("placing rhs instrument for scfg object %s" % atom._rhs)
                                    instrument_point_transition(atom, point, binding_space_indices,
                                                                atom_index, atom_sub_index,
                                                                instrumentation_point_db_ids)

                            elif type(atom) is formula_tree.TransitionDurationLessThanStateValueMixed:
                                """We're instrumenting multiple transitions, so we need to perform instrumentation on 
                                two separate points. """

                                # for each side of the atom (LHS and RHS), instrument the necessary points

                                logger.log(
                                    "Instrumenting for a mixed atom %s with sub atom index %i." % (atom, atom_sub_index)
                                )

                                if atom_sub_index == 0:
                                    # we're instrumenting for the lhs
                                    logger.log("Placing left-hand-side instrument for SCFG object %s." % atom._lhs)
                                    instrument_point_transition(atom, point, binding_space_indices,
                                                                atom_index, atom_sub_index,
                                                                instrumentation_point_db_ids)
                                else:
                                    # we're instrumenting for the rhs
                                    logger.log("Placing right-hand-side instrument for SCFG object %s." % atom._rhs)
                                    instrument_point_state(atom._rhs, atom._rhs_name, point, binding_space_indices,
                                                           atom_index, atom_sub_index, instrumentation_point_db_ids)

                            elif type(atom) is formula_tree.TransitionDurationLessThanStateValueLengthMixed:
                                """We're instrumenting multiple transitions, so we need to perform instrumentation on 
                                two separate points. """

                                # for each side of the atom (LHS and RHS), instrument the necessary points

                                logger.log(
                                    "Instrumenting for a mixed atom %s with sub atom index %i." % (atom, atom_sub_index)
                                )

                                if atom_sub_index == 0:
                                    # we're instrumenting for the lhs
                                    logger.log("Placing left-hand-side instrument for SCFG object %s." % atom._lhs)
                                    instrument_point_transition(atom, point, binding_space_indices,
                                                                atom_index, atom_sub_index,
                                                                instrumentation_point_db_ids)
                                else:
                                    # we're instrumenting for the rhs
                                    logger.log("Placing right-hand-side instrument for SCFG object %s." % atom._rhs)
                                    instrument_point_state(atom._rhs, atom._rhs_name, point, binding_space_indices,
                                                           atom_index, atom_sub_index, instrumentation_point_db_ids,
                                                           measure_attribute="length")

                            elif type(atom) in [formula_tree.TimeBetweenInInterval,
                                                formula_tree.TimeBetweenInOpenInterval]:
                                """We're instrumenting multiple transitions, so we need to perform instrumentation on 
                                two separate points. """

                                # for each side of the atom (LHS and RHS), instrument the necessary points

                                logger.log(
                                    "Instrumenting for a mixed atom %s with sub atom index %i." % (atom, atom_sub_index)
                                )

                                if atom_sub_index == 0:
                                    # we're instrumenting for the lhs
                                    logger.log("Placing left-hand-side instrument for SCFG object %s." % atom._lhs)
                                    instrument_point_state(atom._lhs, None, point, binding_space_indices,
                                                           atom_index, atom_sub_index, instrumentation_point_db_ids,
                                                           measure_attribute="time_attained")
                                else:
                                    # we're instrumenting for the rhs
                                    logger.log("Placing right-hand-side instrument for SCFG object %s." % atom._rhs)
                                    instrument_point_state(atom._rhs, None, point, binding_space_indices,
                                                           atom_index, atom_sub_index, instrumentation_point_db_ids,
                                                           measure_attribute="time_attained")

                # finally, insert an instrument at the beginning to tell the monitoring thread that a new call of the
                # function has started and insert one at the end to signal a return
                place_function_begin_instruments(function_def, formula_hash, instrument_function_qualifier)
                # also insert instruments at the end(s) of the function
                place_function_end_instruments(function_def, scfg, formula_hash, instrument_function_qualifier)

                # write the instrumented scfg to a file
                instrumented_scfg = CFG()
                instrumented_scfg.process_block(top_level_block)
                write_scfg_to_file(instrumented_scfg, "%s-%s-%s-instrumented.gv" %
                                   (file_name_without_extension.replace(".", ""), module.replace(".", "-"),
                                    function.replace(".", "-")))

                # check for existence of directories for intermediate data and create them if not found
                if not (os.path.isdir("binding_spaces")):
                    os.mkdir("binding_spaces")
                if not (os.path.isdir("index_hash")):
                    os.mkdir("index_hash")

                # pickle binding space
                pickled_binding_space = pickle.dumps(bindings)

                # write to a file
                binding_space_dump_file = "binding_spaces/module-%s-function-%s-property-%s.dump" % \
                                          (module.replace(".", "-"), function.replace(".", "-"), formula_hash)
                with open(binding_space_dump_file, "wb") as h:
                    h.write(pickled_binding_space)

                # write the index to hash mapping for properties
                pickled_index_hash = pickle.dumps(index_to_hash)
                index_to_hash_dump_file = "index_hash/module-%s-function-%s.dump" % \
                                          (module.replace(".", "-"), function.replace(".", "-"))
                with open(index_to_hash_dump_file, "wb") as h:
                    h.write(pickled_index_hash)

        compile_bytecode_and_write(asts, file_name_without_extension)

    logger.log("Instrumentation complete.  If VyPR is imported and activated, monitoring will now work.")

    # close instrumentation log
    logger.end_logging()
