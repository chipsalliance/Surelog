OPTS	=

VCS	= vcs -R -sverilog -ntb_opts dtm \
	      +incdir+$(VMM_HOME)/sv $(OPTS) 

all test: sqltxt sqlite

sqlite:
	$(VCS) +define+USE_SQLITE test.sv \
	       $(VMM_HOME)/shared/src/vmm_sqlite_interface.c \
	       -CFLAGS "-I$(SQLITE3_HOME)/include"

sqltxt:
	$(VCS) +define+USE_SQLTXT test.sv \
	       $(VMM_HOME)/shared/src/vmm_sqltxt_interface.c

clean:
	rm -rf simv* csrc *~ *.db *.log *.sql vc_hdrs.h
