#
#    This source code is free software; you can redistribute it
#    and/or modify it in source code form under the terms of the GNU
#    Library General Public License as published by the Free Software
#    Foundation; either version 2 of the License, or (at your option)
#    any later version. In order to redistribute the software in
#    binary form, you will need a Picture Elements Binary Software
#    License.
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
INSTALL = /usr/bin/install -c
INSTALL_PROGRAM = ${INSTALL}
INSTALL_DATA = ${INSTALL} -m 644
LEX = flex

ifeq (.,.)
INCLUDE_PATH = -I. -I..
else
INCLUDE_PATH = -I. -I.. -I$(srcdir) -I$(srcdir)/..
endif

CPPFLAGS = $(INCLUDE_PATH)  -DHAVE_CONFIG_H
CFLAGS = -Wall -Wextra -Wshadow -Wstrict-prototypes  -g -O2
LDFLAGS =  

O = main.o lexor.o

all: ivlpp

check: all

clean:
	rm -f *.o lexor.c ivlpp

distclean: clean
	rm -f Makefile config.log

cppcheck: $(O:.o=.c)
	cppcheck --enable=all -f $(INCLUDE_PATH) $^

Makefile: $(srcdir)/Makefile.in ../config.status
	cd ..; ./config.status --file=ivlpp/$@

ivlpp: $O
	$(CC) $(LDFLAGS) $O -o ivlpp 

lexor.c: $(srcdir)/lexor.lex
	$(LEX) -t $< > $@

install: all installdirs $(libdir)/ivl$(suffix)/ivlpp

$(libdir)/ivl$(suffix)/ivlpp: ivlpp
	$(INSTALL_PROGRAM) ./ivlpp "$(DESTDIR)$(libdir)/ivl$(suffix)/ivlpp"

installdirs: $(srcdir)/../mkinstalldirs
	$(srcdir)/../mkinstalldirs "$(DESTDIR)$(libdir)/ivl$(suffix)"

uninstall:
	rm -f "$(DESTDIR)$(libdir)/ivl$(suffix)/ivlpp"

lexor.o: lexor.c globals.h
main.o: main.c globals.h $(srcdir)/../version_base.h ../version_tag.h
