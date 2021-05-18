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

prefix = /home/alain/black-parrot/tools/bsg_sv2v/tools/iverilog/install
exec_prefix = ${prefix}
srcdir = .



bindir = ${exec_prefix}/bin
libdir = ${exec_prefix}/lib
includedir = $(prefix)/include

CC = gcc
INSTALL = /usr/bin/install -c
INSTALL_PROGRAM = ${INSTALL}
INSTALL_DATA = ${INSTALL} -m 644

ifeq (.,.)
INCLUDE_PATH = -I. -I..
else
INCLUDE_PATH = -I. -I.. -I$(srcdir) -I$(srcdir)/..
endif

CPPFLAGS = @ident_support@ $(INCLUDE_PATH)  -DHAVE_CONFIG_H -fPIC
CFLAGS = -Wall -Wextra -Wshadow -Wstrict-prototypes  -g -O2
LDFLAGS =  

O = verilog.o

all: dep verilog.tgt

check: all

clean:
	rm -rf *.o dep verilog.tgt

distclean: clean
	rm -f Makefile config.log

cppcheck: $(O:.o=.c)
	cppcheck --enable=all -f --suppressions-list=$(srcdir)/cppcheck.sup \
	         --relative-paths=$(srcdir) $(INCLUDE_PATH) $^

Makefile: $(srcdir)/Makefile.in ../config.status
	cd ..; ./config.status --file=tgt-verilog/$@

dep:
	mkdir dep

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -MD -c $< -o $*.o
	mv $*.d dep

ifeq (no,yes)
  TGTLDFLAGS= -L.. -livl
  TGTDEPLIBS=../libivl.a
else
  TGTLDFLAGS=
  TGTDEPLIBS=
endif

verilog.tgt: $O $(TGTDEPLIBS)
	$(CC) -shared $(LDFLAGS) -o $@ $O $(TGTLDFLAGS)

install: all installdirs $(libdir)/ivl/verilog.tgt \
	$(includedir)/vpi_user.h

$(libdir)/ivl/verilog.tgt: ./verilog.tgt
	$(INSTALL_PROGRAM) ./verilog.tgt "$(DESTDIR)$(libdir)/ivl/verilog.tgt"


installdirs: $(srcdir)/../mkinstalldirs
	$(srcdir)/../mkinstalldirs "$(DESTDIR)$(libdir)/ivl"

uninstall:
	rm -f "$(DESTDIR)$(libdir)/ivl/verilog.tgt"


-include $(patsubst %.o, dep/%.d, $O)
