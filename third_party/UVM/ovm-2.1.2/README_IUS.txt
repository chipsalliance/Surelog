This file contains information for using OVM 1.0, OVM 1.1, OVM 2.0, and OVM
2.1 with Cadence Design Systems, Inc. Incisive Unified Simulator (IUS).

OVM version 1.0 and 1.1 have been validated with IUS version 6.2-p001 
and will run with all IUS releases after 6.2-p001.

OVM version 2.0 has been validated with IUS version 8.1-s005 and will
run with any IUS version after this.

OVM version 2.1 has been validated with IUS version 8.2-s019 and will
run with any IUS version after this.

OVM and IUS Compatibility
----------------------------

Various versions of OVM have been tested on various version of IUS.
The table below matches OVM versions and IUS versions they were tested
on.

+-------------+--------------------+
| OVM Version | IUS Version        |
+-------------+--------------------+
| 1.0         | 6.2-p001, 6.2-s003 |
+-------------+--------------------+
| 1.0.1       | 6.2-p001, 6.2-s003 |
+-------------+--------------------+
| 1.1         | 6.2-p001, 6.2-s004 |
+-------------+--------------------+
| 2.0         | 8.1-s005           |
|             | 8.2-p001           |
+-------------+--------------------+
| 2.0.1       | 8.1-s007           |
|             | 8.2-p001           |
+-------------+--------------------+
| 2.0.2       | 8.1-s016           |
|             | 8.2-p001, 8.2-s010 |
+-------------+--------------------+
| 2.0.3       | 8.1-s016           |
|             | 8.2-p001, 8.2-s019 |
|             | 9.2-p007           |
+-------------+--------------------+
| 2.1         | 8.2-s019           |
|             | 9.2-p001           |
+-------------+--------------------+
| 2.1.1       | 8.2-s019           |
|             | 9.2-p001           |
+-------------+--------------------+

##############################################################################
###  Running OVM Examples on IUS                                           ###
##############################################################################

All of the examples in the OVM examples area contain a file called 
compile_ius.f. All OVM examples can be run from within the OVM directory
tree using the command:

$ irun -f compile_ius.f

If an example is moved outside of the OVM directory, the relative paths in
the compile_ius.f file must be changed so that they point correctly to the
OVM home directory (e.g. change the relative path to $OVMHOME).

##############################################################################
###  Single step invocation of OVM with IUS                                ###
##############################################################################

Set an environment variable to point to your OVM installation. This is not
required, but it generally makes life easier.

$ setenv OVMHOME <ovm root directory>            <-- csh
$ OVMHOME=<ovm root directory>; export OVMHOME   <-- bash

To run OVM 2.1 with IUS version 8.2 using irun

  $ irun -ovmhome $OVMHOME <files>

To run OVM 2.1 with IUS version 8.2 where OVM is preloaded at 
`ncroot`/tools/ovm

  $ irun -ovm <files>


##############################################################################
###  Known problems and solutions                                          ###
##############################################################################

Problem: An OVM 1.1 test produces an ncvlog compiler error similar to --
  class simple_sequencer extends ovm_sequencer;
                                            |
  ncvlog: *E,UNDIDN (./simple_sequencer.sv,33|43): 'ovm_sequencer': undeclared
  identifier [12.5(IEEE)].

  This problem is due to the fact that svpp does not handle default 
  specializations, and in OVM 2.0, ovm_sequence, ovm_sequencer, and ovm_driver 
  are all parameterized types. In the above case, the type sequencer is not 
  known by ncvlog because the actual type is ovm_sequencer#(ovm_sequence_item,
  ovm_sequence_item).

Solution: This problem is fixed in IUS 8.1-s005 and later. svpp has been
  made aware of these three special types and knows how to set up the default
  specialization for them. An alternative to upgrading to IUS 8.1-s005 is to
  change ovm_sequencer (and ovm_sequence and ovm_driver) to explicit
  specializations. 

Problem: An OVM 1.1 test using IUS 8.1-s005 generates and error similar to --
      ovm_sequence parent_seq = null);
                 |
  ncvlog: *E,EXPRPA (./cdn_apb_uvc/cdn_apb_transfer.sv,30|17): expecting a right
  parenthesis (')') [A.2.6(IEEE)].

  The error may also show an extra #() by the ovm_sequence identifier. This
  problem is caused by using the default specialization of ovm_sequence, 
  ovm_sequencer, or ovm_driver as an argument to an externed task or function.

Solution: If the problem type is ovm_sequence (which is most likely) then 
  it can be changed to ovm_sequence_base. Or, an explicit specialization can
  be used. This problem is also fixed in IUS 8.1-s006 and later.

Problem: svpp corrupts the endpackage label producing an error like --
  endpackagemypkg
               |
  ncvlog: *E,NPITEM (./INCA_libs/irun.lnx86.08.10.nc/svpplib/foo.sv,13|15): Not
  a valid package item: 'module/udp instance' [SystemVerilog].

  Notice that the : is missing between the endpackage and mypkg.

Solution: Remove the spaces around the colon in the source code, or remove
  the label altogether. This problem is also fixed in IUS 8.1-s006 and later.


##############################################################################
###  Using packages versus including OVM into a scope                      ###
##############################################################################

There are two ways to load OVM into a design. OVM can either be included into
the scope where it will be used by using the form:
  `include "ovm.svh"
or it may be imported from the OVM package by first compiling the file
ovm_pkg.sv and then using the form:
  import ovm_pkg::*;
  `include "ovm_macros.svh"

Starting with IUS 8.2, the package import use model is preferred since
IUS 8.2 natively supports parameterized classes (no -svpp requirement) and
the package use model is more flexible. When using the package use model,
you must include the ovm_macros.svh file in order to ensure access to
ovm macro definitions.

When class definitions are being shared between scopes (packages, interfaces,
modules) it is necessary to use the package form. Prior to IUS 8.2, IUS has a 
limitation with respect to using parameterized types and specializations of 
the types in different scopes, therefore, if you are using IUS 8.1 or if
you have any need that is only filled by using svpp,  we recommend using the
`include methodology unless the package methodology is specifically
required.

NOTE: because of the scoping rules of SystemVerilog, if the ovm package is
imported into a scope AND ovm.svh is included in the scope, the local version
of OVM (the one using the `include of ovm.svh) will take precedence unless the
scope resolution operator (ovm_pkg::) is used. Thus, it is legal to have a
precompiled ovm_pkg and still use the `include methodology to load OVM into a
specific scope, but this is not generally a good practice.

##############################################################################
###  Precompiling the OVM Package                                          ###
##############################################################################

If you plan to use the ovm_pkg package, it is a good idea to compile the 
package separately -- this is not required, but often makes life easier. 
Compilation of the OVM package can be done like:

  $ irun -c -ovmhome $OVMHOME $OVMHOME/src/ovm_pkg.sv

The above command will compile the ovm_pkg into the local INCA_libs library
and will be used by future invocations of irun from the working directory.


##############################################################################
###  OVM Integration with IUS                                              ###
##############################################################################

Starting with IUS 6.2-s003, irun supports additional options for OVM. The
options are:
  -ovmhome <ovmhome dir>
    Sets the ovm home directory to <ovmhome dir>. Adds the -svpp, -nowarn
    and -incdir options as shown above.
  -ovm
    Same as -ovmhome, but looks for OVM at `ncroot`/tools/ovm.

  Both of the above options will look for Cadence specific additions for
  OVM which include transaction recording and tcl support. These 
  additions are delivered with IUS starting in the IUS 8.1 release.

