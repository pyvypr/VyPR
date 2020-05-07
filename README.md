# VyPR

A prototype performance analysis tool for Python-based web services written with the Flask framework.

## Setup

Start by pulling our setup script and running it from your service's root directory.
```
curl -L http://cern.ch/vypr/setup -o setup
chmod +x setup
./setup
```
This will pull VyPR and its server, create the server's virtual environment,
install dependencies and create the server's database.

#### Start the verdict server

To run the server, open a new terminal (tmux is useful here), navigate to `VyPRServer/`
and run
```
python run_service.py
```
This will start VyPR's server on port 8080, unless you specify a different port with the
`--port` argument.

#### Setup configuration files

We'll start with the query file.  The first time, pull our sample query file at `http://cern.ch/vypr/VyPR_queries.py`.
This assumes that you have a function `paths_branching_test` in the module `routes`, in the package `app`.
You probably don't have this, so follow the instructions at http://cern.ch/vypr/writing_queries.py
to write your own queries.

We'll now create the VyPR configuration file.  Again, a sample file can be pulled from
`http://cern.ch/vypr/vypr.config`.  Here, we tell VyPR that it should use the verdict server running at
`http://localhost:8080` and that it should turn its explanation mode on.  Explanation mode currently means VyPR
will add path recording instruments to enable path analysis once some results have been stored.

#### Add VyPR to your service

Assuming you're using Flask, to add VyPR to monitored service you should add the lines
```
app = Flask(...)
...
from VyPR import Monitor
vypr = Monitor()
vypr.initialise(app)
```
Here, we import VyPR's monitoring mechanism, instantiate it, then initialise it over your Flask application.
Initialisation includes adding special end-points to your service to control VyPR, and also adding before_request and
teardown_request hooks to manage VyPR's monitoring thread.

#### Instrument your service

Instrumentation adds the necessary instructions to your service that will interact with VyPR at runtime, allowing
it to monitor for your queries without having to check every piece of information your program gives.

From the root directory of your service, run
```
python VyPR/instrument.py
```
This will take your queries and instrument the service accordingly.

#### Run your service

With instrumentation performed and VyPR added to your service's code, you can run your service as normal and VyPR
will work behind the scenes!  The next step is analysing the data you get, for which we have built VyPR Analysis.

# License Information

(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester
