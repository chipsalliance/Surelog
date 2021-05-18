SUBDIRS += $(PLATDIR)/rhesus

RHESUS_OBJS = rhesus.o
RHESUS = $(PLATDIR)/rhesus/built-in.a
$(RHESUS): $(RHESUS_OBJS:%=$(PLATDIR)/rhesus/%)

