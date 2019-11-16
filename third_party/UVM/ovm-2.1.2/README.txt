Open Verification Methodology
version 2.1.2

(C) Copyright 2007-2011 Mentor Graphics Corporation
(C) Copyright 2007-2011 Cadence Design Systems, Incorporated
All Rights Reserved Worldwide

The OVM kit is licensed under the Apache-2.0 license.  The full text of
the licese is provided in this kit in the file LICENSE.txt

Installing the kit
------------------

Installation of OVM requires only unpacking the kit in a convenient
location.  No additional installation procedures or scripts are
necessary.

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

------------------------------------------------------------------------


