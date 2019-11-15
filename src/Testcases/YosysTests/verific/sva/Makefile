TESTS := consrep firstmatch gotorep intersect nonconsrep seq_and seq_or triggered until until_trig within repzero

all: $(addsuffix .status,$(TESTS))
	grep -H . *.status | sed 's,.status:,\t,; s,PASS,pass,;' | expand -t20
	touch .stamp

%.status: %.sv run.sh
	-bash run.sh $(basename $@) > $(basename $@).log 2>&1
	test -f $@

clean:
	rm -rf $(addsuffix .pass_??,$(TESTS))
	rm -rf $(addsuffix .fail_??,$(TESTS))
	rm -f $(addsuffix .pass_??.sby,$(TESTS))
	rm -f $(addsuffix .fail_??.sby,$(TESTS))
	rm -f $(addsuffix .status,$(TESTS))
	rm -f $(addsuffix .log,$(TESTS))
	rm -f .stamp

.PHONY: all clean
