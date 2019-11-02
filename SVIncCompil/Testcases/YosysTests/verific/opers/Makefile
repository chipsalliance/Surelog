TESTS := wide_mux sel_mux select wselect rednor

all: $(addsuffix .status,$(TESTS))
	grep -H . *.status | sed 's,.status:,\t,; s,PASS,pass,;' | expand -t20
	touch .stamp

%.status: %.sv run.sh
	-bash run.sh $(basename $@) > $(basename $@).log 2>&1
	test -f $@

clean:
	rm -f $(addsuffix .log,$(TESTS))
	rm -f $(addsuffix .status,$(TESTS))
	rm -f .stamp

.PHONY: all clean
