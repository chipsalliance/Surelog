# Makefile for program source directory in GNU NLS utilities package.
# Copyright (C) 1995, 1996, 1997 by Ulrich Drepper <drepper@gnu.ai.mit.edu>
# Copyright (C) 2003-2020 Free Software Foundation, Inc.
#
# This file may be copied and used freely without restrictions.  It can
# be used in projects which are not available under the GNU Public License
# but which still want to provide support for the GNU gettext functionality.
# Please note that the actual code is *not* freely available.

PACKAGE = ld
VERSION = 2.34

SHELL = /bin/sh


srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/po
top_srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld
VPATH = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/po
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
MKINSTALLDIRS = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/../mkinstalldirs

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
POFILES =  $(srcdir)/bg.po $(srcdir)/da.po $(srcdir)/de.po $(srcdir)/es.po $(srcdir)/fi.po $(srcdir)/fr.po $(srcdir)/ga.po $(srcdir)/id.po $(srcdir)/it.po $(srcdir)/ja.po $(srcdir)/pt_BR.po $(srcdir)/ru.po $(srcdir)/sr.po $(srcdir)/sv.po $(srcdir)/tr.po $(srcdir)/uk.po $(srcdir)/vi.po $(srcdir)/zh_CN.po $(srcdir)/zh_TW.po
GMOFILES =  $(srcdir)/bg.gmo $(srcdir)/da.gmo $(srcdir)/de.gmo $(srcdir)/es.gmo $(srcdir)/fi.gmo $(srcdir)/fr.gmo $(srcdir)/ga.gmo $(srcdir)/id.gmo $(srcdir)/it.gmo $(srcdir)/ja.gmo $(srcdir)/pt_BR.gmo $(srcdir)/ru.gmo $(srcdir)/sr.gmo $(srcdir)/sv.gmo $(srcdir)/tr.gmo $(srcdir)/uk.gmo $(srcdir)/vi.gmo $(srcdir)/zh_CN.gmo $(srcdir)/zh_TW.gmo
DISTFILES = ChangeLog Makefile.in.in SRC-POTFILES.in BLD-POTFILES.in $(PACKAGE).pot \
stamp-cat-id $(POFILES) $(GMOFILES) $(SOURCES)

SRC-POTFILES = \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/deffile.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/elf-hints-local.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ld.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldbuildid.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldbuildid.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldcref.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldctor.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldctor.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldelf.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldelf.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldelfgen.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldelfgen.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldemul.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldemul.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldexp.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldexp.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldfile.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldfile.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldlang.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldlang.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldlex-wrapper.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldlex.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldmain.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldmain.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldmisc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldmisc.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldver.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldver.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldwrite.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/ldwrite.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/lexsup.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/mri.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/mri.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/pe-dll.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/pe-dll.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/pep-dll.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/pep-dll.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/plugin.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/ld/plugin.h 

BLD-POTFILES = \
	../eaarch64cloudabi.c \
	../eaarch64cloudabib.c \
	../eaarch64elf.c \
	../eaarch64elf32.c \
	../eaarch64elf32b.c \
	../eaarch64elfb.c \
	../eaarch64fbsd.c \
	../eaarch64fbsdb.c \
	../eaarch64linux.c \
	../eaarch64linux32.c \
	../eaarch64linux32b.c \
	../eaarch64linuxb.c \
	../eaix5ppc.c \
	../eaix5rs6.c \
	../eaixppc.c \
	../eaixrs6.c \
	../ealpha.c \
	../ealphavms.c \
	../earcelf.c \
	../earclinux.c \
	../earclinux_nps.c \
	../earcv2elf.c \
	../earcv2elfx.c \
	../earm_wince_pe.c \
	../earmelf.c \
	../earmelf_fbsd.c \
	../earmelf_fuchsia.c \
	../earmelf_linux.c \
	../earmelf_linux_eabi.c \
	../earmelf_linux_fdpiceabi.c \
	../earmelf_nacl.c \
	../earmelf_nbsd.c \
	../earmelf_phoenix.c \
	../earmelf_vxworks.c \
	../earmelfb.c \
	../earmelfb_fbsd.c \
	../earmelfb_fuchsia.c \
	../earmelfb_linux.c \
	../earmelfb_linux_eabi.c \
	../earmelfb_linux_fdpiceabi.c \
	../earmelfb_nacl.c \
	../earmelfb_nbsd.c \
	../earmnto.c \
	../earmpe.c \
	../earmsymbian.c \
	../eavr1.c \
	../eavr2.c \
	../eavr25.c \
	../eavr3.c \
	../eavr31.c \
	../eavr35.c \
	../eavr4.c \
	../eavr5.c \
	../eavr51.c \
	../eavr6.c \
	../eavrtiny.c \
	../eavrxmega1.c \
	../eavrxmega2.c \
	../eavrxmega3.c \
	../eavrxmega4.c \
	../eavrxmega5.c \
	../eavrxmega6.c \
	../eavrxmega7.c \
	../ecrisaout.c \
	../ecriself.c \
	../ecrislinux.c \
	../ecskyelf.c \
	../ecskyelf_linux.c \
	../ed10velf.c \
	../ed30v_e.c \
	../ed30v_o.c \
	../ed30velf.c \
	../eelf32_dlx.c \
	../eelf32_sparc.c \
	../eelf32_sparc_sol2.c \
	../eelf32_sparc_vxworks.c \
	../eelf32_spu.c \
	../eelf32_tic6x_be.c \
	../eelf32_tic6x_elf_be.c \
	../eelf32_tic6x_elf_le.c \
	../eelf32_tic6x_le.c \
	../eelf32_tic6x_linux_be.c \
	../eelf32_tic6x_linux_le.c \
	../eelf32_x86_64.c \
	../eelf32_x86_64_nacl.c \
	../eelf32am33lin.c \
	../eelf32b4300.c \
	../eelf32bfin.c \
	../eelf32bfinfd.c \
	../eelf32bmip.c \
	../eelf32bmipn32.c \
	../eelf32bsmip.c \
	../eelf32btsmip.c \
	../eelf32btsmip_fbsd.c \
	../eelf32btsmipn32.c \
	../eelf32btsmipn32_fbsd.c \
	../eelf32cr16.c \
	../eelf32crx.c \
	../eelf32ebmip.c \
	../eelf32ebmipvxworks.c \
	../eelf32elmip.c \
	../eelf32elmipvxworks.c \
	../eelf32epiphany.c \
	../eelf32epiphany_4x4.c \
	../eelf32fr30.c \
	../eelf32frv.c \
	../eelf32frvfd.c \
	../eelf32ft32.c \
	../eelf32ip2k.c \
	../eelf32iq10.c \
	../eelf32iq2000.c \
	../eelf32l4300.c \
	../eelf32lm32.c \
	../eelf32lm32fd.c \
	../eelf32lmip.c \
	../eelf32lppc.c \
	../eelf32lppclinux.c \
	../eelf32lppcnto.c \
	../eelf32lppcsim.c \
	../eelf32lr5900.c \
	../eelf32lr5900n32.c \
	../eelf32lriscv.c \
	../eelf32lriscv_ilp32.c \
	../eelf32lriscv_ilp32f.c \
	../eelf32lsmip.c \
	../eelf32ltsmip.c \
	../eelf32ltsmip_fbsd.c \
	../eelf32ltsmipn32.c \
	../eelf32ltsmipn32_fbsd.c \
	../eelf32m32c.c \
	../eelf32mb_linux.c \
	../eelf32mbel_linux.c \
	../eelf32mcore.c \
	../eelf32mep.c \
	../eelf32metag.c \
	../eelf32microblaze.c \
	../eelf32microblazeel.c \
	../eelf32mipswindiss.c \
	../eelf32moxie.c \
	../eelf32mt.c \
	../eelf32or1k.c \
	../eelf32or1k_linux.c \
	../eelf32ppc.c \
	../eelf32ppc_fbsd.c \
	../eelf32ppclinux.c \
	../eelf32ppcnto.c \
	../eelf32ppcsim.c \
	../eelf32ppcvxworks.c \
	../eelf32ppcwindiss.c \
	../eelf32rl78.c \
	../eelf32rx.c \
	../eelf32tilegx.c \
	../eelf32tilegx_be.c \
	../eelf32tilepro.c \
	../eelf32vax.c \
	../eelf32visium.c \
	../eelf32xc16x.c \
	../eelf32xc16xl.c \
	../eelf32xc16xs.c \
	../eelf32xstormy16.c \
	../eelf32xtensa.c \
	../eelf32z80.c \
	../eelf64_aix.c \
	../eelf64_ia64.c \
	../eelf64_ia64_fbsd.c \
	../eelf64_ia64_vms.c \
	../eelf64_s390.c \
	../eelf64_sparc.c \
	../eelf64_sparc_fbsd.c \
	../eelf64_sparc_sol2.c \
	../eelf64alpha.c \
	../eelf64alpha_fbsd.c \
	../eelf64alpha_nbsd.c \
	../eelf64bmip.c \
	../eelf64bpf.c \
	../eelf64btsmip.c \
	../eelf64btsmip_fbsd.c \
	../eelf64hppa.c \
	../eelf64lppc.c \
	../eelf64lriscv.c \
	../eelf64lriscv_lp64.c \
	../eelf64lriscv_lp64f.c \
	../eelf64ltsmip.c \
	../eelf64ltsmip_fbsd.c \
	../eelf64mmix.c \
	../eelf64ppc.c \
	../eelf64ppc_fbsd.c \
	../eelf64rdos.c \
	../eelf64tilegx.c \
	../eelf64tilegx_be.c \
	../eelf_i386.c \
	../eelf_i386_be.c \
	../eelf_i386_fbsd.c \
	../eelf_i386_ldso.c \
	../eelf_i386_nacl.c \
	../eelf_i386_sol2.c \
	../eelf_i386_vxworks.c \
	../eelf_iamcu.c \
	../eelf_k1om.c \
	../eelf_k1om_fbsd.c \
	../eelf_l1om.c \
	../eelf_l1om_fbsd.c \
	../eelf_s390.c \
	../eelf_x86_64.c \
	../eelf_x86_64_cloudabi.c \
	../eelf_x86_64_fbsd.c \
	../eelf_x86_64_nacl.c \
	../eelf_x86_64_sol2.c \
	../eh8300elf.c \
	../eh8300elf_linux.c \
	../eh8300helf.c \
	../eh8300helf_linux.c \
	../eh8300hnelf.c \
	../eh8300self.c \
	../eh8300self_linux.c \
	../eh8300snelf.c \
	../eh8300sxelf.c \
	../eh8300sxelf_linux.c \
	../eh8300sxnelf.c \
	../ehppa64linux.c \
	../ehppaelf.c \
	../ehppalinux.c \
	../ehppanbsd.c \
	../ehppaobsd.c \
	../ei386beos.c \
	../ei386bsd.c \
	../ei386go32.c \
	../ei386lynx.c \
	../ei386moss.c \
	../ei386msdos.c \
	../ei386nto.c \
	../ei386pe.c \
	../ei386pe_posix.c \
	../ei386pep.c \
	../em32relf.c \
	../em32relf_linux.c \
	../em32rlelf.c \
	../em32rlelf_linux.c \
	../em68hc11elf.c \
	../em68hc11elfb.c \
	../em68hc12elf.c \
	../em68hc12elfb.c \
	../em68kelf.c \
	../em68kelfnbsd.c \
	../em9s12zelf.c \
	../emcorepe.c \
	../emmo.c \
	../emn10200.c \
	../emn10300.c \
	../emoxiebox.c \
	../emsp430X.c \
	../emsp430elf.c \
	../ends32belf.c \
	../ends32belf16m.c \
	../ends32belf_linux.c \
	../ends32elf.c \
	../ends32elf16m.c \
	../ends32elf_linux.c \
	../enios2elf.c \
	../enios2linux.c \
	../ens32knbsd.c \
	../epc532macha.c \
	../epdp11.c \
	../epjelf.c \
	../epjlelf.c \
	../eppclynx.c \
	../eppcmacos.c \
	../eppcpe.c \
	../epruelf.c \
	../escore3_elf.c \
	../escore7_elf.c \
	../esh.c \
	../eshelf.c \
	../eshelf_fd.c \
	../eshelf_linux.c \
	../eshelf_nbsd.c \
	../eshelf_nto.c \
	../eshelf_uclinux.c \
	../eshelf_vxworks.c \
	../eshl.c \
	../eshlelf.c \
	../eshlelf_fd.c \
	../eshlelf_linux.c \
	../eshlelf_nbsd.c \
	../eshlelf_nto.c \
	../eshlelf_vxworks.c \
	../eshpe.c \
	../etic30aout.c \
	../etic30coff.c \
	../etic3xcoff.c \
	../etic3xcoff_onchip.c \
	../etic4xcoff.c \
	../etic54xcoff.c \
	../ev850.c \
	../ev850_rh850.c \
	../evanilla.c \
	../evaxnbsd.c \
	../exgateelf.c \
	../ez80.c \
	../ez8001.c \
	../ez8002.c 

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

$(srcdir)/$(PACKAGE).pot: $(SRC-POTFILES) $(BLD-POTFILES)
	$(XGETTEXT) --default-domain=$(PACKAGE) --directory=$(top_srcdir) \
	  --add-comments --keyword=_ --keyword=N_ \
	  --msgid-bugs-address=bug-binutils@gnu.org \
	  --files-from=$(srcdir)/SRC-POTFILES.in
	$(XGETTEXT) --default-domain=$(PACKAGE) --directory=.. \
	  --add-comments --keyword=_ --keyword=N_ \
	  --join-existing \
	  --msgid-bugs-address=bug-binutils@gnu.org \
	  --files-from=$(srcdir)/BLD-POTFILES.in
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
	rm -f Makefile Makefile.in *.mo *.msg *.cat *.cat.m
	rm -f SRC-POTFILES BLD-POTFILES

maintainer-clean: distclean
	@echo "This command is intended for maintainers to use;"
	@echo "it deletes files that may require special tools to rebuild."
	rm -f $(GMOFILES) SRC-POTFILES.in BLD-POTFILES.in

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

SRC-POTFILES: SRC-POTFILES.in
	( if test 'x$(srcdir)' != 'x.'; then \
	    posrcprefix='$(top_srcdir)/'; \
	  else \
	    posrcprefix="../"; \
	  fi; \
	  rm -f $@-t $@ \
	    && (sed -e '/^#/d' -e '/^[	 ]*$$/d' \
		    -e "s@.*@	$$posrcprefix& \\\\@" < $(srcdir)/$@.in \
		| sed -e '$$s/\\$$//') > $@-t \
	    && chmod a-w $@-t \
	    && mv $@-t $@ )

BLD-POTFILES: BLD-POTFILES.in
	  rm -f $@-t $@ \
	  && sed -e '/^#/d' -e '/^[	 ]*$$/d' \
		 -e "s@.*@	../& \\\\@" < $(srcdir)/$@.in \
	     | sed -e '$$s/\\$$//' > $@-t \
	  && chmod a-w $@-t \
	  && mv $@-t $@

SRC-POTFILES.in: # ../Makefile
	cd .. && $(MAKE) po/SRC-POTFILES.in

BLD-POTFILES.in: # ../Makefile
	cd .. && $(MAKE) po/BLD-POTFILES.in

Makefile: Make-in ../config.status SRC-POTFILES BLD-POTFILES
	cd .. \
	  && CONFIG_FILES=$(subdir)/Makefile.in:$(subdir)/Make-in \
	     CONFIG_HEADERS= $(SHELL) ./config.status

# Tell versions [3.59,3.63) of GNU make not to export all variables.
# Otherwise a system limit (for SysV at least) may be exceeded.
.NOEXPORT:
