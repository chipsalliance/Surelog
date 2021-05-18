# -*-Makefile-*-

MBEDTLS_DIR = libstb/mbedtls

SUBDIRS += $(MBEDTLS_DIR)

MBEDTLS_SRCS = sha512.c
MBEDTLS_OBJS = $(MBEDTLS_SRCS:%.c=%.o)
MBEDTLS = $(MBEDTLS_DIR)/built-in.a

$(MBEDTLS): $(MBEDTLS_OBJS:%=$(MBEDTLS_DIR)/%)
