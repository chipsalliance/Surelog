-sverilog

+incdir+${PROJ_HOME}
+incdir+${PROJ_HOME}/sv

+vpi
+dpi
+acc

-assert cbSuccessOnlyNonVacuous

-cm assert+line+cond+fsm+tgl+branch

${PROJ_HOME}/sv/svaunit_pkg.sv
${PROJ_HOME}/sv/svaunit_vpi_interface.sv
${PROJ_HOME}/sv/svaunit_vpi_api.cpp
-f ${file_name}

-timescale=1ns/1ps

-top ${top_name}