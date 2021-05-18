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
datarootdir = ${prefix}/share



bindir = $(exec_prefix)/bin
libdir = $(exec_prefix)/lib
includedir = $(prefix)/include
mandir = ${datarootdir}/man

dllib=-ldl

CC = gcc
INSTALL = /usr/bin/install -c
INSTALL_PROGRAM = ${INSTALL}
INSTALL_DATA = ${INSTALL} -m 644
LEX = flex
YACC = bison
MAN = man
PS2PDF = ps2pdf

ifeq (.,.)
INCLUDE_PATH = -I. -I..
else
INCLUDE_PATH = -I. -I.. -I$(srcdir) -I$(srcdir)/..
endif

CPPFLAGS = $(INCLUDE_PATH)  -DHAVE_CONFIG_H
CFLAGS = -Wall -Wextra -Wshadow -Wstrict-prototypes  -g -O2
LDFLAGS =  

O = main.o substit.o cflexor.o cfparse.o

all: dep iverilog iverilog.man

check: all

clean:
	rm -f *.o cflexor.c cfparse.c cfparse.h cfparse.output
	rm -f iverilog iverilog.man iverilog.pdf iverilog.ps
	rm -rf dep

distclean: clean
	rm -f Makefile config.log

cppcheck: $(O:.o=.c)
	cppcheck --enable=all -f \
	         -UYY_USER_INIT \
	         -UYYPARSE_PARAM -UYYPRINT -Ushort -Uyyoverflow \
	         -UYYTYPE_INT8 -UYYTYPE_INT16 -UYYTYPE_UINT8 -UYYTYPE_UINT16 \
	         $(INCLUDE_PATH) $^

Makefile: $(srcdir)/Makefile.in ../config.status
	cd ..; ./config.status --file=driver/$@

dep:
	mkdir dep

iverilog: $O
	$(CC) $(LDFLAGS) $O -o iverilog 

cflexor.c: $(srcdir)/cflexor.lex
	$(LEX) -s -t $< > $@

# Build this in two steps to avoid parallel build issues (see pr3462585)
cfparse.c: $(srcdir)/cfparse.y
	$(YACC) --verbose -t -p cf -d -o $@ $<
cfparse.h: cfparse.c

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -MD -c $< -o $*.o
	mv $*.d dep

main.o: main.c globals.h $(srcdir)/../version_base.h ../version_tag.h Makefile
	$(CC) $(CPPFLAGS) $(CFLAGS) -MD -c -DIVL_ROOT='"${exec_prefix}/lib/ivl$(suffix)"' -DIVL_SUFFIX='"$(suffix)"' -DIVL_INC='"${prefix}/include"' -DIVL_LIB='"${exec_prefix}/lib"' -DDLLIB='"-ldl"' $(srcdir)/main.c
	mv $*.d dep

cflexor.o: cflexor.c cfparse.h

iverilog.man: $(srcdir)/iverilog.man.in ../version.exe
	../version.exe `head -1 $(srcdir)/iverilog.man.in`'\n' > $@
	tail -n +2 $(srcdir)/iverilog.man.in >> $@

iverilog.ps: iverilog.man
	$(MAN) -t ./iverilog.man > iverilog.ps

iverilog.pdf: iverilog.ps
	$(PS2PDF) iverilog.ps iverilog.pdf

ifeq (no,yes)
ifeq ($(MAN),none)
INSTALL_DOC = $(mandir)/man1/iverilog$(suffix).1
else
ifeq ($(PS2PDF),none)
INSTALL_DOC = $(mandir)/man1/iverilog$(suffix).1
else
INSTALL_DOC = $(prefix)/iverilog$(suffix).pdf $(mandir)/man1/iverilog$(suffix).1
all: iverilog.pdf
endif
endif
INSTALL_DOCDIR = $(mandir)/man1
else
INSTALL_DOC = $(mandir)/man1/iverilog$(suffix).1
INSTALL_DOCDIR = $(mandir)/man1
endif

install: all installdirs $(bindir)/iverilog$(suffix) $(INSTALL_DOC)

$(bindir)/iverilog$(suffix): ./iverilog
	$(INSTALL_PROGRAM) ./iverilog "$(DESTDIR)$(bindir)/iverilog$(suffix)"

$(mandir)/man1/iverilog$(suffix).1: iverilog.man
	$(INSTALL_DATA) iverilog.man "$(DESTDIR)$(mandir)/man1/iverilog$(suffix).1"

$(prefix)/iverilog$(suffix).pdf: iverilog.pdf
	$(INSTALL_DATA) iverilog.pdf "$(DESTDIR)$(prefix)/iverilog$(suffix).pdf"

installdirs: $(srcdir)/../mkinstalldirs
	$(srcdir)/../mkinstalldirs "$(DESTDIR)$(bindir)" "$(DESTDIR)$(INSTALL_DOCDIR)"

uninstall:
	rm -f "$(DESTDIR)$(bindir)/iverilog$(suffix)"
	rm -f "$(DESTDIR)$(mandir)/man1/iverilog$(suffix).1" "$(DESTDIR)$(prefix)/iverilog$(suffix).pdf"

-include $(patsubst %.o, dep/%.d, $O)
