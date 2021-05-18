all: memboot

CFLAGS=-O2 -Wall

memboot: memboot.c
	$(CC) $(CFLAGS) -o $@ $^

.PHONY: clean
clean:
	rm -rf memboot

.PHONY: distclean
distclean: clean
	rm -rf *.c~ *.h~ *.i *.s Makefile~
