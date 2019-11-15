all: test1.status test2.status test3.status test4.status test5.status
	@grep -H . *.status | sed 's,.status:,\t,; s,PASS,pass,;' | expand -t20
	@touch .stamp

test1.status: test1.out
	@(grep -q -e "^Importing module top_veri_v2k(WIDTH=2).$$" $< && \
          grep -q -e "^Importing module top_veri_95(WIDTH=2).$$" $< && \
          grep -q -e "^Importing module top_vhdl(width=2).$$" $< && \
          echo PASS > $@) || echo FAIL > $@

test2.status: test2.out
	@(grep -q -e "^Importing module top_veri_v2k(greeting=\"hola hola\").$$" $< && \
          grep -q -e "^Importing module top_veri_95(greeting=\"hola hola\").$$" $< && \
          grep -q -e "^Importing module top_vhdl(greeting=\"hola hola\").$$" $< && \
          echo PASS > $@) || echo FAIL > $@

test3.status: test3.out
	@(grep -q -e "^Importing module top_veri_v2k.$$" $< && \
         grep -q -e "^Importing module top_veri_95.$$" $< && \
	 grep -q -e "^Importing module top_vhdl.$$" $< && \
         grep -q -e "^VERIFIC-WARNING \\[VHDL-1676\\] top.vhd:1: unit 'top_vhdl' does not have a generic named 'nonexistent' to override$$" $< && \
	 grep -q -e "^VERIFIC-WARNING \\[VERI-1928\\] top.v:1: module 'top_veri_v2k' does not have a parameter named 'nonexistent' to override$$" $< && \
	 grep -q -e "^VERIFIC-WARNING \\[VERI-1928\\] top.v:10: module 'top_veri_95' does not have a parameter named 'nonexistent' to override$$" $< && \
	 echo PASS > $@) || echo FAIL > $@

test4.status: test4.out
	@(grep -q -e "^Importing module top_veri_v2k.$$" $< && \
         grep -q -e "^Importing module top_veri_95.$$" $< && \
	 grep -q -e "^Importing module top_vhdl.$$" $< && \
	 grep -q -e "^-chparam WIDTH already specified: overwriting.$$" $< && \
	 echo PASS > $@) || echo FAIL > $@

test5.status: test5.out
	@(grep -q -e "^Importing module top_veri_v2k(WIDTH=2,INIT=0,greeting=\"bonjour  \").$$" $< && \
          grep -q -e "^Importing module top_veri_95(WIDTH=2,INIT=0,greeting=\"bonjour  \").$$" $< && \
          grep -q -e "^Importing module top_vhdl(width=2,init='0',greeting=\"bonjour  \").$$" $< && \
          grep -q -e "^VERIFIC-WARNING \\[VHDL-1676\\] top.vhd:1: unit 'top_vhdl' does not have a generic named 'nonexistent' to override$$" $< && \
          grep -q -e "^VERIFIC-WARNING \\[VERI-1928\\] top.v:1: module 'top_veri_v2k' does not have a parameter named 'nonexistent' to override$$" $< && \
	  grep -q -e "^VERIFIC-WARNING \\[VERI-1928\\] top.v:10: module 'top_veri_95' does not have a parameter named 'nonexistent' to override$$" $< && \
          echo PASS > $@) || echo FAIL > $@

test1.out test2.out test3.out test4.out test5.out: test.ys top.v top.vhd
	@yosys -q -q test.ys

clean:
	rm -f *.status *.out .stamp

.PHONY: all clean
