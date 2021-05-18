#
#    This source code is free software; you can redistribute it
#    and/or modify it in source code form under the terms of the GNU
#    Library General Public License as published by the Free Software
#    Foundation; either version 2 of the License, or (at your option)
#    any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU Library General Public License for more details.
#
#    You should have received a copy of the GNU Library General Public
#    License along with this program; if not, write to the Free
#    Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
#    Boston, MA 02110-1301, USA.
#
SHELL = /bin/sh

suffix = 

prefix = /home/alain/black-parrot/tools/bsg_sv2v/tools/iverilog/install
exec_prefix = ${prefix}
srcdir = .



bindir = ${exec_prefix}/bin
libdir = ${exec_prefix}/lib
includedir = $(prefix)/include

CC = gcc
RANLIB = ranlib
AR = ar
LD = ld
INSTALL = /usr/bin/install -c
INSTALL_PROGRAM = ${INSTALL}
INSTALL_DATA = ${INSTALL} -m 644

ifeq (.,.)
INCLUDE_PATH = -I. -I..
else
INCLUDE_PATH = -I. -I.. -I$(srcdir) -I$(srcdir)/..
endif

LDRELOCFLAGS = 

LDTARGETFLAGS = 

CPPFLAGS = $(INCLUDE_PATH)  -DHAVE_CONFIG_H -DICARUS_VPI_CONST=const -fPIC
CFLAGS = -Wall -Wextra -Wshadow -Wstrict-prototypes  -g -O2

A = a_close.o a_compare_handles.o a_configure.o a_fetch_argc.o \
    a_fetch_argv.o a_fetch_dir.o a_fetch_fullname.o a_fetch_location.o \
    a_fetch_param.o a_fetch_range.o a_fetch_tfarg.o a_fetch_time.o \
    a_fetch_type.o a_fetch_type_str.o a_fetch_value.o a_handle_by_name.o \
    a_handle_hiconn.o a_handle_object.o a_handle_parent.o \
    a_handle_simulated_net.o a_handle_tfarg.o a_initialize.o a_next.o \
    a_next_bit.o a_next_port.o a_next_topmod.o a_object_of_type.o \
    a_product_version.o a_set_value.o a_vcl.o a_version.o

O = asynch.o delay.o exprinfo.o finish.o getcstringp.o getinstance.o \
    getlongp.o getp.o getsimtime.o io_print.o math.o mc_scan_plusargs.o \
    nodeinfo.o nump.o putlongp.o putp.o spname.o typep.o workarea.o \
    veriusertfs.o priv.o $A

all: dep libveriuser.a $(ALL32)

check: all

clean:
	rm -rf *.o dep libveriuser.a libveriuser.o

distclean: clean
	rm -f Makefile config.log
	rm -f config.h stamp-config-h

cppcheck: $(O:.o=.c)
	cppcheck --enable=all -f $(INCLUDE_PATH) $^

Makefile: $(srcdir)/Makefile.in
	cd ..; ./config.status --file=libveriuser/$@

dep:
	mkdir dep

stamp-config-h: $(srcdir)/config.h.in ../config.status
	@rm -f $@
	cd ..; ./config.status --header=libveriuser/config.h
config.h: stamp-config-h

libveriuser.o: $O
	$(LD) $(LDTARGETFLAGS) -r -o $@ $O

libveriuser.a: libveriuser.o
	rm -f $@
	$(AR) cvq $@ libveriuser.o
	$(RANLIB) $@

%.o: %.c config.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -MD -c $< -o $*.o
	mv $*.d dep

install:: all installdirs $(libdir)/libveriuser$(suffix).a $(INSTALL32)

$(libdir)/libveriuser$(suffix).a: ./libveriuser.a
	$(INSTALL_DATA) ./libveriuser.a "$(DESTDIR)$(libdir)/libveriuser$(suffix).a"

installdirs: $(srcdir)/../mkinstalldirs
	$(srcdir)/../mkinstalldirs "$(DESTDIR)$(libdir)"

uninstall::
	rm -f "$(DESTDIR)$(libdir)/libveriuser$(suffix).a"

-include $(patsubst %.o, dep/%.d, $O)
