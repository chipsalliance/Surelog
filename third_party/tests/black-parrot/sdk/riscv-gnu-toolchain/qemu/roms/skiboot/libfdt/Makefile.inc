# Makefile.libfdt
#
# This is not a complete Makefile of itself.  Instead, it is designed to
# be easily embeddable into other systems of Makefiles.
#

LIBFDT_INCLUDES = fdt.h libfdt.h
LIBFDT_SRCS = fdt.c fdt_ro.c fdt_wip.c fdt_sw.c fdt_rw.c fdt_strerror.c
LIBFDT_OBJS = $(LIBFDT_SRCS:%.c=%.o)

# That warning can't really be fixed so compile the file without it
CFLAGS_SKIP_libfdt/fdt_sw.o = -Wstack-usage=4096

SUBDIRS += libfdt
LIBFDT = libfdt/built-in.a

$(LIBFDT): $(LIBFDT_OBJS:%=libfdt/%)

