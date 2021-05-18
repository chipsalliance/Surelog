#
#   Copyright (C) 2011-2012 Cary R. (cygcary@yahoo.com)
#
#    This program is free software; you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation; either version 2 of the License, or
#    (at your option) any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License along
#    with this program; if not, write to the Free Software Foundation, Inc.,
#    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
#
SHELL = /bin/sh

suffix = 

prefix = /home/alain/black-parrot/tools/bsg_sv2v/tools/iverilog/install
exec_prefix = ${prefix}
srcdir = .



bindir = ${exec_prefix}/bin
libdir = ${exec_prefix}/lib

CC = gcc
INSTALL = /usr/bin/install -c
INSTALL_PROGRAM = ${INSTALL}
INSTALL_DATA = ${INSTALL} -m 644

ifeq (.,.)
INCLUDE_PATH = -I. -I..
else
INCLUDE_PATH = -I. -I.. -I$(srcdir) -I$(srcdir)/..
endif

CPPFLAGS = $(INCLUDE_PATH)  -DHAVE_CONFIG_H -fPIC
CFLAGS = -Wall -Wextra -Wshadow -Wstrict-prototypes  -g -O2
LDFLAGS =  

O = vlog95.o event.o expr.o logic_lpm.o misc.o numbers.o scope.o stmt.o udp.o

all: dep vlog95.tgt

check: all

clean:
	rm -rf *.o dep vlog95.tgt

distclean: clean
	rm -f Makefile config.log

cppcheck: $(O:.o=.c)
	cppcheck --enable=all -f --suppressions-list=$(srcdir)/cppcheck.sup \
	         --relative-paths=$(srcdir) $(INCLUDE_PATH) $^

Makefile: $(srcdir)/Makefile.in ../config.status
	cd ..; ./config.status --file=tgt-vlog95/$@

dep:
	mkdir dep

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -MD -c $< -o $*.o
	mv $*.d dep

ifeq (no,yes)
  TGTLDFLAGS=-L.. -livl
  TGTDEPLIBS=../libivl.a
else
  TGTLDFLAGS=
  TGTDEPLIBS=
endif

vlog95.tgt: $O $(TGTDEPLIBS)
	$(CC) -shared $(LDFLAGS) -o $@ $O -lm $(TGTLDFLAGS)

install: all installdirs $(libdir)/ivl$(suffix)/vlog95.tgt $(INSTALL_DOC) $(libdir)/ivl$(suffix)/vlog95.conf $(libdir)/ivl$(suffix)/vlog95-s.conf

$(libdir)/ivl$(suffix)/vlog95.tgt: ./vlog95.tgt
	$(INSTALL_PROGRAM) ./vlog95.tgt "$(DESTDIR)$(libdir)/ivl$(suffix)/vlog95.tgt"

$(libdir)/ivl$(suffix)/vlog95.conf: $(srcdir)/vlog95.conf
	$(INSTALL_DATA) $(srcdir)/vlog95.conf "$(DESTDIR)$(libdir)/ivl$(suffix)/vlog95.conf"

$(libdir)/ivl$(suffix)/vlog95-s.conf: $(srcdir)/vlog95-s.conf
	$(INSTALL_DATA) $(srcdir)/vlog95-s.conf "$(DESTDIR)$(libdir)/ivl$(suffix)/vlog95-s.conf"


installdirs: $(srcdir)/../mkinstalldirs
	$(srcdir)/../mkinstalldirs "$(DESTDIR)$(bindir)" "$(DESTDIR)$(libdir)/ivl$(suffix)"

uninstall:
	rm -f "$(DESTDIR)$(libdir)/ivl$(suffix)/vlog95.tgt"
	rm -f "$(DESTDIR)$(libdir)/ivl$(suffix)/vlog95.conf"
	rm -f "$(DESTDIR)$(libdir)/ivl$(suffix)/vlog95-s.conf"


-include $(patsubst %.o, dep/%.d, $O)
