Open Verification Methodology
Questa-specifc Topics

Installing the OVM Kit
-----------------------

Installation of the OVM kit requires only unpacking the kit in a
convenient location.  No additional installation procedures or scripts
are necessary.

Running the examples
--------------------

The scripts included with the OVM kit package require that you have
ModelSim or Questa version 6.3 or later installed (see the Questa
compatibility table below) and that the commands vlib, vcom, vlog, and
vsim are in your command search path.

The simplest way to run an example is to cd to the example directory of
your choice and execute the run_questa.doc file.

  % cd ovm/examples/tlm/tlm_fifo
  % ./run_questa

The "run_questa" scripts execute the following commands

  % vlib work
  % vlog -f compile_questa_sv.f
  % vsim -do vsim.do

Each compile_questa_sv.f file contains all the command line options
necessary to compile each example.

Using the OVM Library
---------------------

The OVM library is made accessible by your SystemVerilog code by
importing the OVM package, ovm_pkg.  You may also need to `include the
macro definitions.

  import ovm_pkg::*;
  `include "ovm_macros.svh"

You will need to put the location of the OVM source as a include
directory in your compilation command line.

For example:

  vlog +incdir+$OVM_HOME/src $OVM_HOME/src/ovm_pkg.sv

where $OVM_HOME is set to the root of your ovm installation.


OVM and Questa Compatibility
----------------------------

OVM has been tested on several versions of Questa. The table below
indicates which combinations of Questa and OVM were tested. In
general, OVM is forward compatible with any later version of Questa
on which it was tested.

+-------------+-------------------------------------+
| OVM Version |  Questa Version                     |
+-------------+-------------------------------------+
| 1.0         | 6.3d                                |
+-------------+-------------------------------------+
| 1.0.1       | 6.3d+                               |
+-------------+-------------------------------------+
| 1.1         | 6.3d+                               |
+-------------+-------------------------------------+
| 2.0         | 6.3h, 6.4                           |
+-------------+-------------------------------------+
| 2.0.1       | 6.3i+, 6.4                          |
+-------------+-------------------------------------+
| 2.0.2       | 6.4d+, 6.5                          |
+-------------+-------------------------------------+
| 2.0.3       | 6.4d+, 6.5                          |
+-------------+-------------------------------------+
| 2.1         | 6.4d+, 6.5, 6.6                     |
+-------------+-------------------------------------+
| 2.1.1       | 6.4d+, 6.5, 6.6                     |
+-------------+-------------------------------------+
| 2.1.2       | 6.4d+, 6.5, 6.6, 10.0               |
+-------------+-------------------------------------+

Note: Questa-6.3x provides limited support for the type-based
factory. The two examples which use type-based factory are
examples/factory and examples/hello_world.  Contact your Mentor
technical representative for more details.

----------------------------------------------------------------------
