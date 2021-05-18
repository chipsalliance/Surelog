# Makefile for program source directory in GNU NLS utilities package.
# Copyright (C) 1995, 1996, 1997 by Ulrich Drepper <drepper@gnu.ai.mit.edu>
# Copyright (C) 2003-2020 Free Software Foundation, Inc.
#
# This file may be copied and used freely without restrictions.  It can
# be used in projects which are not available under the GNU Public License
# but which still want to provide support for the GNU gettext functionality.
# Please note that the actual code is *not* freely available.

PACKAGE = gas
VERSION = 2.34

SHELL = /bin/sh


srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/po
top_srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas
VPATH = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/po
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
MKINSTALLDIRS = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/../mkinstalldirs

CC = gcc
GENCAT = gencat
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
POFILES =  $(srcdir)/es.po $(srcdir)/fi.po $(srcdir)/fr.po $(srcdir)/id.po $(srcdir)/ja.po $(srcdir)/ru.po $(srcdir)/rw.po $(srcdir)/sv.po $(srcdir)/tr.po $(srcdir)/uk.po $(srcdir)/zh_CN.po
GMOFILES =  $(srcdir)/es.gmo $(srcdir)/fi.gmo $(srcdir)/fr.gmo $(srcdir)/id.gmo $(srcdir)/ja.gmo $(srcdir)/ru.gmo $(srcdir)/rw.gmo $(srcdir)/sv.gmo $(srcdir)/tr.gmo $(srcdir)/uk.gmo $(srcdir)/zh_CN.gmo
DISTFILES = ChangeLog Makefile.in.in POTFILES.in $(PACKAGE).pot \
stamp-cat-id $(POFILES) $(GMOFILES) $(SOURCES)

POTFILES = \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/app.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/as.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/as.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/asintl.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/atof-generic.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/bignum.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/bit_fix.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/cgen.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/cgen.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/compress-debug.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/compress-debug.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/cond.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/atof-ieee.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/atof-vax.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/e-crisaout.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/e-criself.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/e-i386aout.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/e-i386coff.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/e-i386elf.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/e-mipself.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-aout.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-aout.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-coff.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-coff.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-ecoff.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-ecoff.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-elf.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-elf.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-evax.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-evax.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-fdpicelf.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-fdpicelf.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-macho.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-macho.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-multi.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-multi.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-som.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/obj-som.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-aarch64.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-aarch64.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-alpha.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-alpha.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-arc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-arc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-arm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-arm.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-avr.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-avr.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-bfin.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-bfin.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-bpf.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-bpf.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-cr16.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-cr16.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-cris.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-cris.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-crx.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-crx.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-csky.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-csky.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-d10v.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-d10v.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-d30v.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-d30v.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-dlx.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-dlx.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-epiphany.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-epiphany.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-fr30.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-fr30.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-frv.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-frv.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ft32.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ft32.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-h8300.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-h8300.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-hppa.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-hppa.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-i386.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-i386.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ia64.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ia64.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ip2k.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ip2k.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-iq2000.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-iq2000.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-lm32.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-lm32.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-m32c.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-m32c.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-m32r.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-m32r.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-m68hc11.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-m68hc11.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-m68k.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-m68k.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mcore.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mcore.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mep.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mep.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-metag.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-metag.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-microblaze.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-microblaze.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mips.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mips.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mmix.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mmix.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mn10200.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mn10200.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mn10300.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mn10300.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-moxie.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-msp430.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-msp430.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mt.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-mt.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-nds32.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-nds32.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-nios2.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-nios2.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ns32k.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ns32k.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-or1k.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-or1k.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-pdp11.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-pdp11.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-pj.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-pj.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ppc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-ppc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-pru.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-pru.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-riscv.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-riscv.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-rl78.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-rl78.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-rx.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-rx.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-s12z.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-s12z.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-s390.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-s390.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-score.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-score.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-sh.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-sh.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-sparc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-sparc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-spu.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-spu.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tic30.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tic30.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tic4x.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tic4x.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tic54x.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tic54x.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tic6x.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tic6x.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tilegx.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tilegx.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tilepro.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-tilepro.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-v850.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-v850.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-vax.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-vax.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-visium.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-visium.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-wasm32.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-wasm32.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-xc16x.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-xc16x.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-xgate.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-xgate.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-xstormy16.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-xstormy16.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-xtensa.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-xtensa.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-z80.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-z80.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-z8k.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/tc-z8k.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-386bsd.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-aix5.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-armeabi.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-armfbsdeabi.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-armfbsdvfp.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-armlinuxeabi.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-csky_abiv1.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-csky_abiv1_linux.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-csky_abiv2.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-csky_abiv2_linux.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-freebsd.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-generic.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-gnu.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-go32.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-hppa.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-hppa64.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-hppalinux64.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-ia64aix.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-interix.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-lynx.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-macos.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-nbsd.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-nbsd532.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-pc532mach.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-pe.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-solaris.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-svr4.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-symbian.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-tmips.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-vms.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-vxworks.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/te-wince-pe.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/xtensa-relax.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/config/xtensa-relax.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/depend.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/dw2gencfi.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/dw2gencfi.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/dwarf2dbg.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/dwarf2dbg.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/ecoff.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/ecoff.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/ehopt.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/emul-target.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/emul.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/expr.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/expr.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/flonum-copy.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/flonum-konst.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/flonum-mult.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/flonum.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/frags.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/frags.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/hash.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/hash.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/input-file.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/input-file.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/input-scrub.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/itbl-lex.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/itbl-ops.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/itbl-ops.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/listing.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/listing.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/literal.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/macro.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/macro.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/messages.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/obj.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/output-file.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/output-file.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/read.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/read.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/remap.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/sb.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/sb.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/stabs.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/subsegs.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/subsegs.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/symbols.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/symbols.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/tc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/write.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-binutils/gas/write.h

CATALOGS =  es.gmo fi.gmo fr.gmo id.gmo ja.gmo ru.gmo rw.gmo sv.gmo tr.gmo uk.gmo zh_CN.gmo
CATOBJEXT = .gmo
INSTOBJEXT = .mo

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


all: all-yes

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
install-data: install-data-yes
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
