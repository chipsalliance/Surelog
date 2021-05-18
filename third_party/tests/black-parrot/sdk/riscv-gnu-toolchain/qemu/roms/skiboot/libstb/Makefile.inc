# -*-Makefile-*-

LIBSTB_DIR = libstb

SUBDIRS += $(LIBSTB_DIR)

LIBSTB_SRCS = container.c tpm_chip.c cvc.c secureboot.c trustedboot.c
LIBSTB_OBJS = $(LIBSTB_SRCS:%.c=%.o)
LIBSTB = $(LIBSTB_DIR)/built-in.a

include $(SRC)/$(LIBSTB_DIR)/mbedtls/Makefile.inc
include $(SRC)/$(LIBSTB_DIR)/drivers/Makefile.inc
include $(SRC)/$(LIBSTB_DIR)/tss/Makefile.inc

$(LIBSTB): $(LIBSTB_OBJS:%=$(LIBSTB_DIR)/%) $(DRIVERS) $(TSS) $(MBEDTLS)

libstb/create-container: libstb/create-container.c libstb/container-utils.c
	$(call Q, HOSTCC ,$(HOSTCC) $(HOSTCFLAGS) \
	-Wpadded -O0 -g -I$(SRC) -I$(SRC)/include -o $@ $^ -lssl -lcrypto,$<)

libstb/print-container: libstb/print-container.c libstb/container-utils.c
	$(call Q, HOSTCC , $(HOSTCC) $(HOSTCFLAGS) \
	-O0 -g -I$(SRC) -I$(SRC)/include -o $@ $^ -lssl -lcrypto, $<)

clean: create-container-clean

create-container-clean:
	$(RM) libstb/create-container
