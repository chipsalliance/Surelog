+UVM_NO_RELNOTES
+incdir+${PROJ_HOME}
+incdir+${PROJ_HOME}/sv

-dpi
-DIRUN
-cpost "${PROJ_HOME}/sv/svaunit_vpi_api.cpp" -end
-uvm
-sv
-assert
${PROJ_HOME}/sv/svaunit_pkg.sv
${PROJ_HOME}/sv/svaunit_vpi_interface.sv
-f ${file_name}
-access rwc
-linedebug
-assert
-coverage all
-covoverwrite
-timescale 1ns/1ps

-top ${top_name}
