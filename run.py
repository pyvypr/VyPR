"""
Script to be used to run a program under VyPR monitoring.
Command line arguments:
  --module <module> gives us the module to use (we run 'python -m <module>').
  --local-server tells us to start a local verdict server.
  --server <address> tells us to use a remote verdict server, given with this argument.
"""

import argparse
import sys
import os
import subprocess
import json
import time


def run_in_shell(*popenargs, **kwargs):
    """Run string-based commands in the shell and returns the result."""
    new_kwargs = kwargs
    if new_kwargs.get("stdout"):
        del new_kwargs["stdout"]
    process = subprocess.Popen(*popenargs,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, shell=True, **new_kwargs)
    stdout = process.communicate()[0]
    return_code = process.returncode
    cmd = kwargs.get('args')
    if cmd is None:
        cmd = popenargs[0]
    if return_code:
        raise subprocess.CalledProcessError(return_code, cmd)
    return stdout


def run_in_shell_nonblocking(command):
    """Run string-based commands in the shell and returns the result."""
    subprocess.Popen(command, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, shell=True)


def start_verdict_server():
    """Start a verdict server in a separate process."""
    print("Starting local verdict server at 'http://localhost:9002/'.")
    run_in_shell_nonblocking(
        'tmux new -d -s server; tmux send-keys -t server.0 "python VyPRServer/run_service.py" ENTER;'
    )
    # give the server time to start up
    time.sleep(2)



if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='The VyPR performance analysis tool.')
    parser.add_argument('--module', type=str,
                        help='The name of the module to monitor.', required=True)
    parser.add_argument('--local-server', action='store_true',
                        help='If given, a local verdict server will be initialised for analysis of monitoring data.',
                        required=False)
    parser.add_argument('--server', type=str,
                        help='If given, the address of a remote verdict server to use during instrumentation and '
                             'monitoring',
                        required=False)

    args = parser.parse_args()

    # check if we should start a local server
    if args.local_server:
        # check if we already have a verdict server in the working directory
        if os.path.exists("VyPRServer"):
            print("Local verdict server exists and --local-server given.")
            # start the server
            start_verdict_server()
        else:
            print("No local verdict server found in directory '%s'.  Setting up a new one."
                  % os.path.join(os.getcwd(), "VyPR/VyPRServer"))

            # clone the server
            run_in_shell("git clone git@github.com:pyvypr/VyPRServer-py3.git VyPRServer")
            # clone VyPR into the server
            run_in_shell("git clone git@github.com:pyvypr/VyPRLocal.git VyPRServer/VyPR")
            # set up the verdict database
            run_in_shell("sqlite3 VyPRServer/verdicts.db < VyPRServer/verdict-schema.sql")

            # start the server
            start_verdict_server()

        # set the verdict server that VyPR will use
        verdict_server = "http://localhost:9002/"

    if args.server:
        verdict_server = args.server

    # write the VyPR configuration file
    configuration_dict = {
        "verdict_server_url" : verdict_server,
        "explanation" : "on",
        "bytecode_extension" : ".pyc",
        "project_root" : ""
    }
    configuration_string = json.dumps(configuration_dict)
    with open("vypr.config", "w") as h:
        h.write(configuration_string)

    # set up directories for logs
    if not(os.path.isdir("instrumentation_logs")):
        os.mkdir("instrumentation_logs/")
    if not(os.path.isdir("vypr_monitoring_logs/")):
        os.mkdir("vypr_monitoring_logs/")

    sys.path.append("VyPR")

    # run instrumentation and monitoring
    print("Instrumenting and monitoring...")
    run_in_shell("python VyPR/instrument.py; python -m %s;" % args.module)

    print("Program run under VyPR finished.")
