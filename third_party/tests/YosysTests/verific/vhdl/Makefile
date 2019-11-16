all: test.status
	grep -H . *.status | sed 's,.status:,\t,; s,PASS,pass,;' | expand -t20
	touch .stamp

test.status: bar.vhd foo.vhd tb.sv test.ys top.vhd
	yosys -ql test.log test.ys
	grep '^SAT .*: SUCCESS' test.log && echo PASS > test.status || echo FAIL > test.status

clean:
	rm -f test.status test.log .stamp

.PHONY: all clean
