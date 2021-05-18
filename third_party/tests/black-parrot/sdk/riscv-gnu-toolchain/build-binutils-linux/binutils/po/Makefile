# Makefile for program source directory in GNU NLS utilities package.
# Copyright (C) 1995, 1996, 1997 by Ulrich Drepper <drepper@gnu.ai.mit.edu>
# Copyright (C) 2003-2020 Free Software Foundation, Inc.
#
# This file may be copied and used freely without restrictions.  It can
# be used in projects which are not available under the GNU Public License
# but which still want to provide support for the GNU gettext functionality.
# Please note that the actual code is *not* freely available.

PACKAGE = binutils
VERSION = 2.34

SHELL = /bin/sh


srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/po
top_srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils
VPATH = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/po
top_builddir = ..

prefix = /home/alain/black-parrot/sdk/install
exec_prefix = ${prefix}
datadir = ${datarootdir}
localedir = ${datarootdir}/locale
gnulocaledir = ${prefix}/share/locale
gettextsrcdir = ${prefix}/share/gettext/po
subdir = po

DESTDIR =

INSTALL = /usr/bin/install -c
INSTALL_DATA = /usr/bin/install -c -m 644
MKINSTALLDIRS = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/../mkinstalldirs

CC = gcc
GENCAT = 
GMSGFMT = PATH=../src:$$PATH :
MSGFMT = :
XGETTEXT = PATH=../src:$$PATH :
MSGMERGE = PATH=../src:$$PATH msgmerge

DEFS = -DHAVE_CONFIG_H
CFLAGS = -g -O2
CPPFLAGS = 

INCLUDES = -I.. -I$(top_srcdir)/intl

COMPILE = $(CC) -c $(DEFS) $(INCLUDES) $(CPPFLAGS) $(CFLAGS) $(XCFLAGS)

SOURCES = cat-id-tbl.c
POFILES =  $(srcdir)/bg.po $(srcdir)/ca.po $(srcdir)/da.po $(srcdir)/es.po $(srcdir)/fi.po $(srcdir)/fr.po $(srcdir)/hr.po $(srcdir)/id.po $(srcdir)/it.po $(srcdir)/ja.po $(srcdir)/pt.po $(srcdir)/ro.po $(srcdir)/ru.po $(srcdir)/rw.po $(srcdir)/sk.po $(srcdir)/sr.po $(srcdir)/sv.po $(srcdir)/tr.po $(srcdir)/uk.po $(srcdir)/vi.po $(srcdir)/zh_CN.po $(srcdir)/zh_TW.po
GMOFILES =  $(srcdir)/bg.gmo $(srcdir)/ca.gmo $(srcdir)/da.gmo $(srcdir)/es.gmo $(srcdir)/fi.gmo $(srcdir)/fr.gmo $(srcdir)/hr.gmo $(srcdir)/id.gmo $(srcdir)/it.gmo $(srcdir)/ja.gmo $(srcdir)/pt.gmo $(srcdir)/ro.gmo $(srcdir)/ru.gmo $(srcdir)/rw.gmo $(srcdir)/sk.gmo $(srcdir)/sr.gmo $(srcdir)/sv.gmo $(srcdir)/tr.gmo $(srcdir)/uk.gmo $(srcdir)/vi.gmo $(srcdir)/zh_CN.gmo $(srcdir)/zh_TW.gmo
DISTFILES = ChangeLog Makefile.in.in POTFILES.in $(PACKAGE).pot \
stamp-cat-id $(POFILES) $(GMOFILES) $(SOURCES)

POTFILES = \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/addr2line.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/ar.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/arsup.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/arsup.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/bin2c.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/binemul.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/binemul.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/bucomm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/bucomm.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/budbg.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/coffdump.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/coffgrok.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/coffgrok.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/cxxfilt.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/debug.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/debug.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/debug.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/dlltool.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/dlltool.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/dllwrap.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/dwarf.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/dwarf.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/elfcomm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/elfcomm.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/elfedit.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/emul_aix.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/emul_vanilla.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/filemode.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/is-ranlib.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/is-strip.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/maybe-ranlib.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/maybe-strip.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/mclex.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/nm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/not-ranlib.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/not-strip.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/objcopy.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/objdump.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/objdump.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/od-macho.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/od-xcoff.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/prdbg.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/rclex.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/rdcoff.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/rdcoff.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/rddbg.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/rddbg.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/readelf.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/rename.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/resbin.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/rescoff.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/resrc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/resres.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/size.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/srconv.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/stabs.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/stabs.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/strings.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/sysdep.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/sysdump.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/syslex_wrap.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/unwind-ia64.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/unwind-ia64.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/version.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/windint.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/windmc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/windmc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/windres.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/windres.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/winduni.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/winduni.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/binutils/wrstabs.c

CATALOGS = 
CATOBJEXT = 
INSTOBJEXT = 

.SUFFIXES:
.SUFFIXES: .c .o .po .pox .gmo .mo .msg .cat

.c.o:
	$(COMPILE) $<

.po.pox:
	$(MAKE) $(PACKAGE).pot
	$(MSGMERGE) $< $(srcdir)/$(PACKAGE).pot -o $*.pox

.po.mo:
	$(MSGFMT) -o $@ $<

.po.gmo:
	file=`echo $* | sed 's,.*/,,'`.gmo \
	  && rm -f $$file && $(GMSGFMT) -o $$file $<

.po.cat:
	sed -f ../intl/po2msg.sed < $< > $*.msg \
	  && rm -f $@ && $(GENCAT) $@ $*.msg


all: all-no

all-yes: $(CATALOGS) # $(PACKAGE).pot
all-no:

$(srcdir)/$(PACKAGE).pot: $(POTFILES)
	$(XGETTEXT) --default-domain=$(PACKAGE) --directory=$(top_srcdir) \
	  --add-comments --keyword=_ --keyword=N_ \
	  --msgid-bugs-address=bug-binutils@gnu.org \
	  --files-from=$(srcdir)/POTFILES.in
	rm -f $(srcdir)/$(PACKAGE).pot
	mv $(PACKAGE).po $(srcdir)/$(PACKAGE).pot

$(srcdir)/cat-id-tbl.c: stamp-cat-id; @:
$(srcdir)/stamp-cat-id: $(PACKAGE).pot
	rm -f cat-id-tbl.tmp
	sed -f ../intl/po2tbl.sed $(srcdir)/$(PACKAGE).pot \
		| sed -e "s/@PACKAGE NAME@/$(PACKAGE)/" > cat-id-tbl.tmp
	if cmp -s cat-id-tbl.tmp $(srcdir)/cat-id-tbl.c; then \
	  rm cat-id-tbl.tmp; \
	else \
	  echo cat-id-tbl.c changed; \
	  rm -f $(srcdir)/cat-id-tbl.c; \
	  mv cat-id-tbl.tmp $(srcdir)/cat-id-tbl.c; \
	fi
	cd $(srcdir) && rm -f stamp-cat-id && echo timestamp > stamp-cat-id


install: install-exec install-data
install-exec:
install-info:
install-html:
install-pdf:
install-data: install-data-no
install-data-no: all
install-data-yes: all
	if test -r $(MKINSTALLDIRS); then \
	  $(MKINSTALLDIRS) $(DESTDIR)$(datadir); \
	else \
	  $(top_srcdir)/mkinstalldirs $(DESTDIR)$(datadir); \
	fi
	@catalogs='$(CATALOGS)'; \
	for cat in $$catalogs; do \
	  cat=`basename $$cat`; \
	  case "$$cat" in \
	    *.gmo) destdir=$(gnulocaledir);; \
	    *)     destdir=$(localedir);; \
	  esac; \
	  lang=`echo $$cat | sed 's/\$(CATOBJEXT)$$//'`; \
	  dir=$(DESTDIR)$$destdir/$$lang/LC_MESSAGES; \
	  if test -r $(MKINSTALLDIRS); then \
	    $(MKINSTALLDIRS) $$dir; \
	  else \
	    $(top_srcdir)/mkinstalldirs $$dir; \
	  fi; \
	  if test -r $$cat; then \
	    $(INSTALL_DATA) $$cat $$dir/$(PACKAGE)$(INSTOBJEXT); \
	    echo "installing $$cat as $$dir/$(PACKAGE)$(INSTOBJEXT)"; \
	  else \
	    $(INSTALL_DATA) $(srcdir)/$$cat $$dir/$(PACKAGE)$(INSTOBJEXT); \
	    echo "installing $(srcdir)/$$cat as" \
		 "$$dir/$(PACKAGE)$(INSTOBJEXT)"; \
	  fi; \
	  if test -r $$cat.m; then \
	    $(INSTALL_DATA) $$cat.m $$dir/$(PACKAGE)$(INSTOBJEXT).m; \
	    echo "installing $$cat.m as $$dir/$(PACKAGE)$(INSTOBJEXT).m"; \
	  else \
	    if test -r $(srcdir)/$$cat.m ; then \
	      $(INSTALL_DATA) $(srcdir)/$$cat.m \
		$$dir/$(PACKAGE)$(INSTOBJEXT).m; \
	      echo "installing $(srcdir)/$$cat as" \
		   "$$dir/$(PACKAGE)$(INSTOBJEXT).m"; \
	    else \
	      true; \
	    fi; \
	  fi; \
	done
	if test "$(PACKAGE)" = "gettext"; then \
	  if test -r $(MKINSTALLDIRS); then \
	    $(MKINSTALLDIRS) $(DESTDIR)$(gettextsrcdir); \
	  else \
	    $(top_srcdir)/mkinstalldirs $(DESTDIR)$(gettextsrcdir); \
	  fi; \
	  $(INSTALL_DATA) $(srcdir)/Makefile.in.in \
			  $(DESTDIR)$(gettextsrcdir)/Makefile.in.in; \
	else \
	  : ; \
	fi

# Define this as empty until I found a useful application.
installcheck:

uninstall:
	catalogs='$(CATALOGS)'; \
	for cat in $$catalogs; do \
	  cat=`basename $$cat`; \
	  lang=`echo $$cat | sed 's/\$(CATOBJEXT)$$//'`; \
	  rm -f $(DESTDIR)$(localedir)/$$lang/LC_MESSAGES/$(PACKAGE)$(INSTOBJEXT); \
	  rm -f $(DESTDIR)$(localedir)/$$lang/LC_MESSAGES/$(PACKAGE)$(INSTOBJEXT).m; \
	  rm -f $(DESTDIR)$(gnulocaledir)/$$lang/LC_MESSAGES/$(PACKAGE)$(INSTOBJEXT); \
	  rm -f $(DESTDIR)$(gnulocaledir)/$$lang/LC_MESSAGES/$(PACKAGE)$(INSTOBJEXT).m; \
	done
	rm -f $(DESTDIR)$(gettextsrcdir)/po-Makefile.in.in

check: all

cat-id-tbl.o: ../intl/libgettext.h

html dvi pdf ps info tags TAGS ID:

mostlyclean:
	rm -f core core.* *.pox $(PACKAGE).po *.old.po cat-id-tbl.tmp
	rm -fr *.o

clean: mostlyclean

distclean: clean
	rm -f Makefile Makefile.in POTFILES *.mo *.msg *.cat *.cat.m

maintainer-clean: distclean
	@echo "This command is intended for maintainers to use;"
	@echo "it deletes files that may require special tools to rebuild."
	rm -f $(GMOFILES)

distdir = ../$(PACKAGE)-$(VERSION)/$(subdir)
dist distdir: update-po $(DISTFILES)
	dists="$(DISTFILES)"; \
	for file in $$dists; do \
	  ln $(srcdir)/$$file $(distdir) 2> /dev/null \
	    || cp -p $(srcdir)/$$file $(distdir); \
	done

update-po: Makefile
	$(MAKE) $(PACKAGE).pot
	PATH=`pwd`/../src:$$PATH; \
	cd $(srcdir); \
	catalogs='$(CATALOGS)'; \
	for cat in $$catalogs; do \
	  cat=`basename $$cat`; \
	  lang=`echo $$cat | sed 's/\$(CATOBJEXT)$$//'`; \
	  mv $$lang.po $$lang.old.po; \
	  echo "$$lang:"; \
	  if $(MSGMERGE) $$lang.old.po $(PACKAGE).pot -o $$lang.po; then \
	    rm -f $$lang.old.po; \
	  else \
	    echo "msgmerge for $$cat failed!"; \
	    rm -f $$lang.po; \
	    mv $$lang.old.po $$lang.po; \
	  fi; \
	done

POTFILES: POTFILES.in
	( if test 'x$(srcdir)' != 'x.'; then \
	    posrcprefix='$(top_srcdir)/'; \
	  else \
	    posrcprefix="../"; \
	  fi; \
	  rm -f $@-t $@ \
	    && (sed -e '/^#/d' -e '/^[ 	]*$$/d' \
		    -e "s@.*@	$$posrcprefix& \\\\@" < $(srcdir)/$@.in \
		| sed -e '$$s/\\$$//') > $@-t \
	    && chmod a-w $@-t \
	    && mv $@-t $@ )

POTFILES.in: # ../Makefile
	cd .. && $(MAKE) po/POTFILES.in

Makefile: Make-in ../config.status POTFILES
	cd .. \
	  && CONFIG_FILES=$(subdir)/Makefile.in:$(subdir)/Make-in \
	     CONFIG_HEADERS= $(SHELL) ./config.status

# Tell versions [3.59,3.63) of GNU make not to export all variables.
# Otherwise a system limit (for SysV at least) may be exceeded.
.NOEXPORT:
