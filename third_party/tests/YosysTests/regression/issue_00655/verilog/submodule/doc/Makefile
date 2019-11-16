DOCS=mmu.html

RM ?= rm -f

all: $(DOCS)

%.html: %.rst
	rst2html $< >$@

clean:
	$(RM) $(DOCS)

.PHONY: clean
