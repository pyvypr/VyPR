"""
Module containing functions to be called inside the verified service.
This provides a function to set up the consumption thread (initialising verification) and a function to insert events into the consumption queue.
"""

import datetime
import json
import os
import pickle
import threading

import Queue
import flask
import requests
from VyPR.control_flow_graph.construction import CFGEdge, CFGVertex
from VyPR.formula_building.formula_building import *
from VyPR.monitor_synthesis import formula_tree
from VyPR.verdict_reports import VerdictReport

# sys.path.append("VyPR/")

VERDICT_SERVER_URL = None
VYPR_OUTPUT_VERBOSE = True
PROJECT_ROOT = None


# thank you to the CMS Conditions Browser team for this
def to_timestamp(obj):
    if type(obj) is datetime.datetime:
        return obj.isoformat()
    elif type(obj) is datetime.timedelta:
        return obj.total_seconds()
    else:
        return obj


def vypr_output(string, *args):
    if VYPR_OUTPUT_VERBOSE:
        if len(args) > 0:
            print(("[VyPR] - %s - %s" % (str(datetime.datetime.now()), string)), args)
        else:
            print("[VyPR] - %s - %s" % (str(datetime.datetime.now()), string))


def send_verdict_report(function_name, time_of_call, end_time_of_call, program_path, verdict_report,
                        binding_to_line_numbers, http_request_time, property_hash):
    """
    Send verdict data for a given function call (function name + time of call).
    """
    global VERDICT_SERVER_URL
    verdicts = verdict_report.get_final_verdict_report()
    vypr_output("Sending verdicts to server")

    # first, send function call data - this will also insert program path data

    call_data = {
        "http_request_time": http_request_time.isoformat(),
        "time_of_call": time_of_call.isoformat(),
        "end_time_of_call": end_time_of_call.isoformat(),
        "function_name": function_name,
        "property_hash": property_hash,
        "program_path": program_path
    }
    vypr_output("CALL DATA")
    vypr_output(call_data)
    insertion_result = json.loads(requests.post(
        os.path.join(VERDICT_SERVER_URL, "insert_function_call_data/"),
        data=json.dumps(call_data)
    ).text)

    # second, send verdict data - all data in one request
    # for this, we first build the structure
    # that we'll send over HTTP
    verdict_dict_list = []
    for bind_space_index in verdicts.keys():
        verdict_list = verdicts[bind_space_index]
        for verdict in verdict_list:
            # remember to deal with datetime objects in json serialisation
            verdict_dict = {
                "bind_space_index": bind_space_index,
                "verdict": [
                    verdict[0],
                    verdict[1].isoformat(),
                    verdict[2],
                    verdict[3],
                    verdict[4],
                    verdict[5],
                    verdict[6]
                ],
                "line_numbers": json.dumps(binding_to_line_numbers[bind_space_index]),
            }
            verdict_dict_list.append(verdict_dict)

    request_body_dict = {
        "function_call_id": insertion_result["function_call_id"],
        "function_id": insertion_result["function_id"],
        "verdicts": verdict_dict_list
    }

    print("VERDICT DATA")
    print(str(request_body_dict))

    # send request
    try:
        response = requests.post(os.path.join(VERDICT_SERVER_URL, "register_verdicts/"),
                                 data=json.dumps(request_body_dict, default=to_timestamp))
    except Exception as e:
        vypr_output(
            "Something went wrong when sending verdict information to the verdict server.  The verdict information we tried to send is now lost.")
        import traceback
        vypr_output(traceback.format_exc())

    vypr_output("Verdicts sent.")


def consumption_thread_function(verification_obj):
    # the web service has to be considered as running forever, so the monitoring loop for now should also run forever
    # this needs to be changed for a clean exit
    INACTIVE_MONITORING = False
    while True:

        # take top element from the queue
        try:
            top_pair = verification_obj.consumption_queue.get(timeout=1)
        except:
            continue

        if top_pair[0] == "end-monitoring":
            # return from the monitoring function to end the monitoring thread
            vypr_output("Returning from monitoring thread.")
            return

        # if monitoring is inactive, we do nothing with what we consume unless it's a resume message
        if INACTIVE_MONITORING:
            if top_pair[0] == "inactive-monitoring-stop":
                # return from the monitoring function to end the monitoring thread
                vypr_output("Restarting monitoring.  Monitoring thread will still be alive.")
                INACTIVE_MONITORING = False
            continue
        else:
            if top_pair[0] == "inactive-monitoring-start":
                # return from the monitoring function to end the monitoring thread
                vypr_output("Pausing monitoring.  Monitoring thread will still be alive.")
                # turn on inactive monitoring
                INACTIVE_MONITORING = True
                # skip to the next iteration of the consumption loop
                continue
        # if inactive monitoring is off (so monitoring is running), process what we consumed

        vypr_output("Consuming:")
        vypr_output(top_pair)

        property_hash = top_pair[0]

        # remove the property hash and just deal with the rest of the data
        top_pair = top_pair[1:]

        instrument_type = top_pair[0]
        function_name = top_pair[1]

        # get the maps we need for this function
        maps = verification_obj.function_to_maps[function_name][property_hash]
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

                # before resetting the qd -> monitor map, go through it to find monitors
                # that reached a verdict, and register those in the verdict report

                for static_qd_index in static_qd_to_monitors:
                    for monitor in static_qd_to_monitors[static_qd_index]:
                        # check if the monitor has a collapsing atom - only then do we register a verdict
                        if monitor.collapsing_atom:
                            verdict_report.add_verdict(
                                static_qd_index,
                                monitor._formula.verdict,
                                monitor.atom_to_observation,
                                monitor.atom_to_program_path,
                                atoms.index(monitor.collapsing_atom),
                                monitor.collapsing_atom_sub_index,
                                monitor.atom_to_state_dict
                            )

                # everything not here is static data that we need, and should be left
                maps.static_qd_to_monitors = {}

                # generate the verdict report

                report_map = verdict_report.get_final_verdict_report()

                binding_to_line_numbers = {}

                for bind_space_index in report_map.keys():

                    binding = bindings[bind_space_index]

                    binding_to_line_numbers[bind_space_index] = []

                    # for each element of the binding, print the appropriate representation
                    for bind_var in binding:

                        if type(bind_var) is CFGVertex:
                            binding_to_line_numbers[bind_space_index].append(
                                bind_var._previous_edge._instruction.lineno)
                        elif type(bind_var) is CFGEdge:
                            binding_to_line_numbers[bind_space_index].append(bind_var._instruction.lineno)

                # send the verdict
                # we send the function name, the time of the function call, the verdict report object,
                # the map of bindings to their line numbers and the date/time of the request the identify it (single threaded...)
                send_verdict_report(
                    function_name,
                    maps.latest_time_of_call,
                    datetime.datetime.now(),
                    maps.program_path,
                    verdict_report,
                    binding_to_line_numbers,
                    top_pair[3],
                    top_pair[4]
                )

                # reset the verdict report
                maps.verdict_report.reset()

                # reset the function start time for the next time
                maps.latest_time_of_call = None

                # reset the program path
                maps.program_path = []

            elif scope_event == "start":
                vypr_output("*" * 50)
                vypr_output("FUNCTION HAS STARTED")
                vypr_output("*" * 50)

                # remember when the function call started
                maps.latest_time_of_call = datetime.datetime.now()

                vypr_output("*" * 50)

        if instrument_type == "trigger":
            # we've received a trigger instrument

            vypr_output("processing trigger - dealing with monitor instantiation")

            static_qd_index = top_pair[2]
            bind_variable_index = top_pair[3]

            vypr_output("trigger is for bind variable %i" % bind_variable_index)
            if bind_variable_index == 0:
                vypr_output("instantiating new, clean monitor")
                # we've encountered a trigger for the first bind variable, so we simply instantiate a new monitor
                new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())
                try:
                    static_qd_to_monitors[static_qd_index].append(new_monitor)
                except:
                    static_qd_to_monitors[static_qd_index] = [new_monitor]
            else:
                vypr_output("processing existing monitors")
                # we look at the monitors' timestamps, and decide whether to generate a new monitor
                # and copy over existing information, or update timestamps of existing monitors
                new_monitors = []
                subsequences_processed = []
                for monitor in static_qd_to_monitors[static_qd_index]:
                    # check if the monitor's timestamp sequence includes a timestamp for this bind variable
                    vypr_output(
                        "  processing monitor with timestamp sequence %s" % str(monitor._monitor_instantiation_time))
                    if len(monitor._monitor_instantiation_time) == bind_variable_index + 1:
                        if monitor._monitor_instantiation_time[:bind_variable_index] in subsequences_processed:
                            # the same subsequence might have been copied and extended multiple times
                            # we only care about one
                            continue
                        else:
                            subsequences_processed.append(monitor._monitor_instantiation_time[:bind_variable_index])
                            # construct new monitor
                            vypr_output("    instantiating new monitor with modified timestamp sequence")
                            # instantiate a new monitor using the timestamp subsequence excluding the current bind variable
                            # and copy over all observation, path and state information

                            old_instantiation_time = list(monitor._monitor_instantiation_time)
                            updated_instantiation_time = tuple(
                                old_instantiation_time[:bind_variable_index] + [datetime.datetime.now()])
                            new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())
                            new_monitors.append(new_monitor)

                            # copy timestamp sequence, observation, path and state information
                            new_monitor._monitor_instantiation_time = updated_instantiation_time

                            # iterate through the observations stored by the previous monitor
                            # for bind variables before the current one and use them to update the new monitor
                            for atom in monitor._state._state:
                                if not (type(atom) is formula_tree.LogicalNot):
                                    if (formula_structure._bind_variables.index(
                                            get_base_variable(atom)) < bind_variable_index
                                            and not (monitor._state._state[atom] is None)):
                                        if monitor._state._state[atom] == True:
                                            new_monitor.check_optimised(atom)
                                        elif monitor._state._state[atom] == False:
                                            new_monitor.check_optimised(formula_tree.lnot(atom))

                                        atom_index = atoms.index(atom)

                                        for sub_index in monitor.atom_to_observation[atom_index].keys():
                                            new_monitor.atom_to_observation[atom_index][sub_index] = \
                                                monitor.atom_to_observation[atom_index][sub_index]

                                        for sub_index in monitor.atom_to_program_path[atom_index].keys():
                                            new_monitor.atom_to_program_path[atom_index][sub_index] = \
                                                monitor.atom_to_program_path[atom_index][sub_index]

                                        for sub_index in monitor.atom_to_state_dict[atom_index].keys():
                                            new_monitor.atom_to_state_dict[atom_index][sub_index] = \
                                                monitor.atom_to_state_dict[atom_index][sub_index]

                    elif len(monitor._monitor_instantiation_time) == bind_variable_index:
                        vypr_output("    updating existing monitor timestamp sequence")
                        # extend the monitor's timestamp sequence
                        tmp_sequence = list(monitor._monitor_instantiation_time)
                        tmp_sequence.append(datetime.datetime.now())
                        monitor._monitor_instantiation_time = tuple(tmp_sequence)

                # add the new monitors
                static_qd_to_monitors[static_qd_index] += new_monitors

        if instrument_type == "path":
            # we've received a path recording instrument
            # append the branching condition to the program path encountered so far for this function.
            program_path.append(top_pair[2])

        if instrument_type == "instrument":

            static_qd_indices = top_pair[2]
            atom_index = top_pair[3]
            atom_sub_index = top_pair[4]
            instrumentation_point_db_ids = top_pair[5]
            observed_value = top_pair[6]
            thread_id = top_pair[7]
            try:
                state_dict = top_pair[8]
            except:
                # instrument isn't from a transition measurement
                state_dict = None

            vypr_output("consuming data from an instrument in thread %i" % thread_id)

            lists = zip(static_qd_indices, instrumentation_point_db_ids)

            for values in lists:

                static_qd_index = values[0]
                instrumentation_point_db_id = values[1]

                vypr_output("binding space index", static_qd_index)
                vypr_output("atom_index", atom_index)
                vypr_output("atom_sub_index", atom_sub_index)
                vypr_output("instrumentation point db id", instrumentation_point_db_id)
                vypr_output("observed value", observed_value)
                vypr_output("state dictionary", state_dict)

                instrumentation_atom = atoms[atom_index]

                # update all monitors associated with static_qd_index
                if static_qd_to_monitors.get(static_qd_index):
                    print("processing %i existing monitors" % len(static_qd_to_monitors[static_qd_index]))
                    for (n, monitor) in enumerate(static_qd_to_monitors[static_qd_index]):
                        print("processing")
                        print(monitor._state._state)
                        # checking for previous observation of the atom is done by the monitor's internal logic
                        monitor.process_atom_and_value(instrumentation_atom, observed_value, atom_index, atom_sub_index,
                                                       inst_point_id=instrumentation_point_db_id,
                                                       program_path=len(program_path), state_dict=state_dict)

        # set the task as done
        verification_obj.consumption_queue.task_done()

        vypr_output("Consumption finished.")

        vypr_output("=" * 100)


class PropertyMapGroup(object):
    """
    Groups together all the maps needed for verification of a single run of a single function, wrt a single property.
    """

    def __init__(self, module_name, function_name, property_hash):
        self._function_name = function_name
        self._property_hash = property_hash

        # read in instrumentation map
        with open(os.path.join(PROJECT_ROOT, "instrumentation_maps/module-%s-function-%s-property-%s.dump") % \
                  (module_name.replace(".", "-"), function_name.replace(":", "-"), property_hash), "rb") as h:
            instr_map_dump = h.read()

        # read in binding spaces
        with open(os.path.join(PROJECT_ROOT, "binding_spaces/module-%s-function-%s-property-%s.dump") % \
                  (module_name.replace(".", "-"), function_name.replace(":", "-"), property_hash), "rb") as h:
            binding_space_dump = h.read()

        # read in index hash map
        with open(os.path.join(PROJECT_ROOT, "index_hash/module-%s-function-%s.dump") % \
                  (module_name.replace(".", "-"), function_name.replace(":", "-")), "rb") as h:
            index_to_hash_dump = h.read()

        inst_configuration = read_configuration("vypr.config")

        # get the specification file name
        verification_conf_file = inst_configuration.get("specification_file") \
            if inst_configuration.get("specification_file") else "verification_conf.py"

        # reconstruct formula structure
        # there's probably a better way to do this
        exec("".join(open(verification_conf_file, "r").readlines()))
        index_to_hash = pickle.loads(index_to_hash_dump)
        property_index = index_to_hash.index(property_hash)

        print(function_name, property_index)

        # might just change the syntax in the verification conf file at some point to use : instead of .
        self.formula_structure = verification_conf[module_name][function_name.replace(":", ".")][property_index]
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

    def __init__(self, flask_object=None):
        """
        Sets up the consumption thread for events from instruments.
        """
        vypr_output("Initialising VyPR monitoring...")

        # read configuration file
        inst_configuration = read_configuration("vypr.config")
        global VERDICT_SERVER_URL, VYPR_OUTPUT_VERBOSE, PROJECT_ROOT
        VERDICT_SERVER_URL = inst_configuration.get("verdict_server_url") if inst_configuration.get(
            "verdict_server_url") else "http://localhost:9001/"
        VYPR_OUTPUT_VERBOSE = inst_configuration.get("verbose") if inst_configuration.get("verbose") else True
        PROJECT_ROOT = inst_configuration.get("project_root") if inst_configuration.get("project_root") else ""

        # try to connect to the verdict server before we set anything up
        try:
            attempt = requests.get(VERDICT_SERVER_URL)
            self.initialisation_failure = False
        except Exception:
            vypr_output("Couldn't connect to the verdict server at '%s'.  Initialisation failed." % VERDICT_SERVER_URL)
            self.initialisation_failure = True
            return

        if flask_object:
            # add the request time recording function before every request
            def set_request_time():
                import datetime
                flask.g.request_time = datetime.datetime.now()

            flask_object.before_request(set_request_time)

            # add VyPR end points - we may use this for statistics collection on the server
            # add the safe exist end point
            @flask_object.route("/vypr/stop-monitoring/")
            def endpoint_stop_monitoring():
                from app import verification
                # send end-monitoring message
                verification.end_monitoring()
                # wait for the thread to end
                verification.consumption_thread.join()
                return "VyPR monitoring thread exited.  The server must be restarted to turn monitoring back on.\n"

            @flask_object.route("/vypr/pause-monitoring/")
            def endpoint_pause_monitoring():
                from app import verification
                verification.pause_monitoring()
                return "VyPR monitoring paused - thread is still running.\n"

            @flask_object.route("/vypr/resume-monitoring/")
            def endpoint_resume_monitoring():
                from app import verification
                verification.resume_monitoring()
                return "VyPR monitoring resumed.\n"

        # set up the maps that the monitoring algorithm that the consumption thread runs

        # we need the list of functions that we have instrumentation data from, so read the instrumentation maps directory
        dump_files = filter(lambda filename: ".dump" in filename,
                            os.listdir(os.path.join(PROJECT_ROOT, "instrumentation_maps")))
        functions_and_properties = map(lambda function_dump_file: function_dump_file.replace(".dump", ""), dump_files)
        tokens = map(lambda string: string.split("-"), functions_and_properties)

        self.function_to_maps = {}

        for token_chain in tokens:

            start_of_module = token_chain.index("module") + 1
            start_of_function = token_chain.index("function") + 1
            start_of_property = token_chain.index("property") + 1

            module_string = ".".join(token_chain[start_of_module:start_of_function - 1])
            # will need to be modified to support functions that are methods
            # function = ".".join(token_chain[start_of_function:start_of_property-1])
            function = ":".join(token_chain[start_of_function:start_of_property - 1])

            property_hash = token_chain[start_of_property]

            vypr_output("Setting up monitoring state for module/function/property triple %s, %s, %s" % (
                module_string, function, property_hash))

            module_function_string = "%s.%s" % (module_string, function)

            if not (self.function_to_maps.get(module_function_string)):
                self.function_to_maps[module_function_string] = {}
            self.function_to_maps[module_function_string][property_hash] = PropertyMapGroup(module_string, function,
                                                                                            property_hash)

        vypr_output(self.function_to_maps)

        vypr_output("Setting up monitoring thread.")

        # setup consumption queue and store it globally across requests
        self.consumption_queue = Queue.Queue()
        # setup consumption thread
        self.consumption_thread = threading.Thread(
            target=consumption_thread_function,
            args=[self]
        )
        self.consumption_thread.start()

        vypr_output("VyPR monitoring initialisation finished.")

    def send_event(self, event_description):
        if not (self.initialisation_failure):
            vypr_output("adding %s to consumption queue" % str(event_description))
            self.consumption_queue.put(event_description)

    def end_monitoring(self):
        if not (self.initialisation_failure):
            vypr_output("ending VyPR monitoring")
            self.consumption_queue.put(("end-monitoring",))

    def pause_monitoring(self):
        if not (self.initialisation_failure):
            vypr_output("Sending monitoring pause message.")
            self.consumption_queue.put(("inactive-monitoring-start",))

    def resume_monitoring(self):
        if not (self.initialisation_failure):
            vypr_output("Sending monitoring resume message.")
            self.consumption_queue.put(("inactive-monitoring-stop",))
