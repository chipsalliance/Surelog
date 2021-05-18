# Makefile for program source directory in GNU NLS utilities package.
# Copyright (C) 1995, 1996, 1997 by Ulrich Drepper <drepper@gnu.ai.mit.edu>
# Copyright (C) 2003-2019 Free Software Foundation, Inc.
#
# This file may be copied and used freely without restrictions.  It can
# be used in projects which are not available under the GNU Public License
# but which still want to provide support for the GNU gettext functionality.
# Please note that the actual code is *not* freely available.

PACKAGE = opcodes
VERSION = 2.32.51

SHELL = /bin/sh


srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/po
top_srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes
VPATH = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/po
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
MKINSTALLDIRS = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/../mkinstalldirs

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
POFILES =  $(srcdir)/da.po $(srcdir)/de.po $(srcdir)/es.po $(srcdir)/fi.po $(srcdir)/fr.po $(srcdir)/ga.po $(srcdir)/id.po $(srcdir)/it.po $(srcdir)/nl.po $(srcdir)/pt_BR.po $(srcdir)/ro.po $(srcdir)/sr.po $(srcdir)/sv.po $(srcdir)/tr.po $(srcdir)/uk.po $(srcdir)/vi.po $(srcdir)/zh_CN.po
GMOFILES =  $(srcdir)/da.gmo $(srcdir)/de.gmo $(srcdir)/es.gmo $(srcdir)/fi.gmo $(srcdir)/fr.gmo $(srcdir)/ga.gmo $(srcdir)/id.gmo $(srcdir)/it.gmo $(srcdir)/nl.gmo $(srcdir)/pt_BR.gmo $(srcdir)/ro.gmo $(srcdir)/sr.gmo $(srcdir)/sv.gmo $(srcdir)/tr.gmo $(srcdir)/uk.gmo $(srcdir)/vi.gmo $(srcdir)/zh_CN.gmo
DISTFILES = ChangeLog Makefile.in.in POTFILES.in $(PACKAGE).pot \
stamp-cat-id $(POFILES) $(GMOFILES) $(SOURCES)

POTFILES = \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-asm-2.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-asm.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-dis-2.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-dis.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-gen.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-opc-2.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/aarch64-tbl.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/alpha-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/alpha-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/arc-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/arc-ext.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/arc-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/arm-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/avr-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/bfin-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/cgen-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/cgen-bitset.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/cgen-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/cgen-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/cr16-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/cr16-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/cris-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/cris-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/crx-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/crx-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/csky-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/d10v-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/d10v-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/d30v-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/d30v-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/dis-buf.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/dis-init.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/disassemble.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/dlx-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/epiphany-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/epiphany-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/epiphany-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/epiphany-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/epiphany-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/epiphany-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/epiphany-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/fr30-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/fr30-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/fr30-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/fr30-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/fr30-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/fr30-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/fr30-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/frv-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/frv-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/frv-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/frv-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/frv-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/frv-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/frv-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ft32-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ft32-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/h8300-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/hppa-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/i386-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/i386-gen.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/i386-init.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/i386-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/i386-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/i386-tbl.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-asmtab.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-asmtab.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-gen.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-opc-a.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-opc-b.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-opc-d.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-opc-f.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-opc-i.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-opc-m.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ia64-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ip2k-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ip2k-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ip2k-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ip2k-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ip2k-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ip2k-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ip2k-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/iq2000-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/iq2000-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/iq2000-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/iq2000-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/iq2000-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/iq2000-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/iq2000-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/lm32-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/lm32-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/lm32-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/lm32-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/lm32-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/lm32-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/lm32-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/lm32-opinst.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m10200-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m10200-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m10300-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m10300-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32c-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32c-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32c-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32c-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32c-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32c-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32c-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32r-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32r-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32r-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32r-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32r-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32r-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32r-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m32r-opinst.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m68hc11-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m68hc11-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m68k-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/m68k-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mcore-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mcore-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mep-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mep-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mep-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mep-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mep-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mep-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mep-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/metag-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/microblaze-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/microblaze-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/micromips-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mips-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mips-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mips16-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mmix-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mmix-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/moxie-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/moxie-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/msp430-decode.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/msp430-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mt-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mt-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mt-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mt-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mt-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mt-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/mt-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/nds32-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/nds32-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/nfp-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/nios2-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/nios2-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ns32k-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/or1k-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/or1k-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/or1k-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/or1k-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/or1k-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/pdp11-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/pdp11-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/pj-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/pj-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ppc-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/ppc-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/pru-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/pru-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/riscv-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/riscv-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/rl78-decode.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/rl78-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/rx-decode.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/rx-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/s12z-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/s12z-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/s390-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/s390-mkopc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/s390-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/score-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/score-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/score7-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/sh-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/sh-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/sparc-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/sparc-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/spu-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/spu-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/sysdep.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tic30-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tic4x-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tic54x-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tic54x-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tic6x-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tic80-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tic80-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tilegx-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tilegx-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tilepro-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/tilepro-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/v850-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/v850-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/vax-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/visium-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/visium-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/wasm32-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xc16x-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xc16x-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xc16x-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xc16x-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xc16x-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xc16x-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xc16x-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xgate-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xgate-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xstormy16-asm.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xstormy16-desc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xstormy16-desc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xstormy16-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xstormy16-ibld.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xstormy16-opc.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xstormy16-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/xtensa-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/z80-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/z8k-dis.c \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/z8k-opc.h \
     /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/opcodes/z8kgen.c

CATALOGS =  da.gmo de.gmo es.gmo fi.gmo fr.gmo ga.gmo id.gmo it.gmo nl.gmo pt_BR.gmo ro.gmo sr.gmo sv.gmo tr.gmo uk.gmo vi.gmo zh_CN.gmo
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
