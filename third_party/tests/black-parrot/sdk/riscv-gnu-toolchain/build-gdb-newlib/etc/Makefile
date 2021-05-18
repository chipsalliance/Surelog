# 
# Makefile.in for etc
#

DESTDIR		=

prefix 		= /home/alain/black-parrot/sdk/install
exec_prefix 	= ${prefix}

srcdir  = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/etc
VPATH	= /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/etc

bindir  = ${exec_prefix}/bin
libdir  = ${exec_prefix}/lib
tooldir = $(libdir)
datadir = ${datarootdir}

mandir  = ${datarootdir}/man
man1dir = $(mandir)/man1
man2dir = $(mandir)/man2
man3dir = $(mandir)/man3
man4dir = $(mandir)/man4
man5dir = $(mandir)/man5
man6dir = $(mandir)/man6
man7dir = $(mandir)/man7
man8dir = $(mandir)/man8
man9dir = $(mandir)/man9
datarootdir = ${prefix}/share
docdir = ${datarootdir}/doc/${PACKAGE}
infodir = ${datarootdir}/info
pdfdir = ${datarootdir}/doc/${PACKAGE}
htmldir = ${docdir}

SHELL = /bin/sh

INSTALL 	= /usr/bin/install -c
INSTALL_PROGRAM = /usr/bin/install -c
INSTALL_DATA    = /usr/bin/install -c -m 644

#### Host, target, and site specific Makefile fragments come in here.
###

all:

clean:

mostlyclean: clean

distclean:   clean
	rm -f Makefile config.status config.cache

maintainer-clean realclean:   distclean

Makefile: $(srcdir)/Makefile.in $(host_makefile_frag) $(target_makefile_frag) \
	config.status
	$(SHELL) ./config.status

AUTOCONF = autoconf
configure_deps = $(srcdir)/configure.in

$(srcdir)/configure: # $(configure_deps)
	cd $(srcdir) && $(AUTOCONF)

config.status: $(srcdir)/configure
	$(SHELL) ./config.status --recheck

## these last targets are for standards.texi conformance
dist:
check:
info html dvi ps pdf:
install install-strip install-info install-html install-pdf:
installcheck:
uninstall:
TAGS:
