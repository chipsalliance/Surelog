FILES = rtl.sv interface.sv  top.sv 
IFILES = Packet.sv Configuration.sv Driver.sv Environment.sv Sequencer.sv Sequence.sv test.sv Scoreboard.sv Receiver.sv
UVM_FLAGS = +incdir+${UVM_HOME}/src ${UVM_HOME}/src/uvm_pkg.sv
VCS_FLAGS = -sverilog +plusarg_save -timescale=1ns/1ns

vcs:	simv
	simv +UVM_TESTNAME=test1 -l simv.log

simv:   ${FILES} ${IFILES}
	@if [ ! -e ${UVM_HOME}/src/uvm_pkg.sv ];then \
	 echo "*******************************************************";\
         echo "Environemnt varible UVM_HOME is not set or points to incorrect path"; \
	 echo "*******************************************************";\
	 fi 
	vcs ${UVM_FLAGS} ${VCS_FLAGS} ${FILES}

questa: ${FILES} ${IFILES}
	@if [ ! -e ${UVM_HOME}/src/uvm_pkg.sv ];then \
	 echo "*******************************************************";\
         echo "Environemnt varible UVM_HOME is not set or points to incorrect path"; \
	 echo "*******************************************************";\
	 fi 
	qverilog ${UVM_FLAGS} +incdir+. ${FILES} -R +UVM_TESTNAME=test1

ius: ${FILES} ${IFILES}
	@if [ ! -e ${UVM_HOME}/src/uvm_pkg.sv ];then \
	 echo "*******************************************************";\
         echo "Environemnt varible UVM_HOME is not set or points to incorrect path"; \
	 echo "*******************************************************";\
	 fi 
	irun ${UVM_FLAGS} +incdir+. ${FILES} +UVM_TESTNAME=test1


DIR = $(shell basename `pwd`)

tar:	clean
	cd ..; \
	tar cvf ${DIR}.tar ${DIR}

clean:
	@rm -rf simv* csrc* *.log *.key core* *.vpd *.vcd 
	@rm -rf *~ .vcsmx_rebuild vc_hdrs.h DVEfiles
	@rm -rf work vsim.wlf INCA_libs 

