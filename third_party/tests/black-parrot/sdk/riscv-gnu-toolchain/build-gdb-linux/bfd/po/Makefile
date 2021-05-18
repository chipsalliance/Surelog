# Makefile for program source directory in GNU NLS utilities package.
# Copyright (C) 1995, 1996, 1997 by Ulrich Drepper <drepper@gnu.ai.mit.edu>
# Copyright (C) 2001-2019 Free Software Foundation, Inc.
#
# This file may be copied and used freely without restrictions.  It can
# be used in projects which are not available under the GNU Public License
# but which still want to provide support for the GNU gettext functionality.
# Please note that the actual code is *not* freely available.

PACKAGE = bfd
VERSION = 2.32.51

SHELL = /bin/sh


srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/po
top_srcdir = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd
VPATH = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/po
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
MKINSTALLDIRS = /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/../mkinstalldirs

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
POFILES =  $(srcdir)/da.po $(srcdir)/es.po $(srcdir)/fi.po $(srcdir)/fr.po $(srcdir)/hr.po $(srcdir)/id.po $(srcdir)/ja.po $(srcdir)/ro.po $(srcdir)/ru.po $(srcdir)/rw.po $(srcdir)/sr.po $(srcdir)/sv.po $(srcdir)/tr.po $(srcdir)/uk.po $(srcdir)/vi.po $(srcdir)/zh_CN.po $(srcdir)/pt.po
GMOFILES =  $(srcdir)/da.gmo $(srcdir)/es.gmo $(srcdir)/fi.gmo $(srcdir)/fr.gmo $(srcdir)/hr.gmo $(srcdir)/id.gmo $(srcdir)/ja.gmo $(srcdir)/ro.gmo $(srcdir)/ru.gmo $(srcdir)/rw.gmo $(srcdir)/sr.gmo $(srcdir)/sv.gmo $(srcdir)/tr.gmo $(srcdir)/uk.gmo $(srcdir)/vi.gmo $(srcdir)/zh_CN.gmo $(srcdir)/pt.gmo
DISTFILES = ChangeLog Makefile.in.in SRC-POTFILES.in BLD-POTFILES.in $(PACKAGE).pot \
stamp-cat-id $(POFILES) $(GMOFILES) $(SOURCES)

# Note - the following line gets processed by bfd/configure and amended
# to contain the full list of source dir POTFILES.
SRC-POTFILES = \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/aix386-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/aix5ppc-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/aout-cris.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/aout-ns32k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/aout-target.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/aout-tic30.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/aout32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/aout64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/aoutx.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/archive.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/archive64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/archures.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/bfd.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/bfdio.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/bfdwin.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/binary.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cache.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cf-i386lynx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cisco-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-alpha.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-bfd.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-go32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-i386.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-mips.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-rs6000.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-sh.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-stgo32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-tic30.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-tic4x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-tic54x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-tic80.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-x86_64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-z80.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff-z8k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coff64-rs6000.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coffcode.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coffgen.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cofflink.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/coffswap.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/compress.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/corefile.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-aarch64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-alpha.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-arc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-arm.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-avr.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-bfin.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-cr16.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-cr16c.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-cris.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-crx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-csky.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-d10v.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-d30v.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-dlx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-epiphany.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-fr30.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-frv.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-ft32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-h8300.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-hppa.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-i386.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-ia64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-iamcu.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-ip2k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-iq2000.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-k1om.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-l1om.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-lm32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-m10200.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-m10300.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-m32c.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-m32r.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-m68hc11.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-m68hc12.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-m68k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-m9s12x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-m9s12xg.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-mcore.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-mep.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-metag.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-microblaze.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-mips.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-mmix.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-moxie.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-msp430.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-mt.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-nds32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-nfp.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-nios2.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-ns32k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-or1k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-pdp11.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-pj.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-plugin.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-powerpc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-pru.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-riscv.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-rl78.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-rs6000.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-rx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-s12z.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-s390.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-score.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-sh.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-sparc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-spu.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-tic30.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-tic4x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-tic54x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-tic6x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-tic80.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-tilegx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-tilepro.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-v850.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-v850_rh850.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-vax.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-visium.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-wasm32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-xc16x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-xgate.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-xstormy16.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-xtensa.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-z80.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/cpu-z8k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/dwarf1.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/dwarf2.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/ecoff.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/ecofflink.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/ecoffswap.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-attrs.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-bfd.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-eh-frame.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-hppa.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-ifunc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-linux-core.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-m10200.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-m10300.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-nacl.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-properties.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-strtab.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf-vxworks.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-am33lin.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-arc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-arm.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-avr.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-bfin.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-cr16.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-cr16c.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-cris.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-crx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-csky.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-d10v.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-d30v.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-dlx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-epiphany.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-fr30.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-frv.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-ft32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-gen.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-h8300.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-hppa.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-hppa.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-i386.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-ip2k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-iq2000.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-lm32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-m32c.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-m32r.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-m68hc11.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-m68hc12.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-m68hc1x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-m68k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-mcore.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-mep.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-metag.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-microblaze.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-mips.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-moxie.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-msp430.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-mt.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-nds32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-nios2.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-or1k.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-pj.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-ppc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-pru.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-rl78.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-rx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-s12z.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-s390.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-score.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-score7.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-sh.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-sparc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-spu.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-tic6x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-tilegx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-tilepro.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-v850.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-vax.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-visium.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-wasm32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-xc16x.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-xgate.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-xstormy16.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32-xtensa.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf32.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-alpha.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-gen.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-hppa.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-hppa.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-ia64-vms.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-mips.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-mmix.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-nfp.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-ppc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-s390.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-sparc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-tilegx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64-x86-64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elf64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfcode.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfcore.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elflink.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfn32-mips.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfxx-aarch64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfxx-ia64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfxx-mips.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfxx-riscv.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfxx-sparc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfxx-tilegx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfxx-x86.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/elfxx-x86.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/format.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/genlink.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/go32stub.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/hash.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/hpux-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/i386aout.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/i386bsd.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/i386lynx.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/i386msdos.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/ihex.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/init.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/irix-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/libaout.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/libbfd.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/libbfd.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/libcoff.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/libecoff.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/libhppa.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/libpei.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/libxcoff.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/linker.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/lynx-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/mach-o-aarch64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/mach-o-arm.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/mach-o-i386.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/mach-o-x86-64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/mach-o.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/mach-o.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/merge.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/mmo.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/netbsd-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/netbsd.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/ns32k.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/ns32knetbsd.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/opncls.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/osf-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pc532-mach.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pdp11.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pe-arm-wince.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pe-arm.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pe-i386.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pe-mcore.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pe-ppc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pe-sh.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pe-x86_64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pef-traceback.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pef.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pef.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pei-arm-wince.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pei-arm.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pei-i386.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pei-ia64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pei-mcore.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pei-ppc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pei-sh.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/pei-x86_64.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/peicode.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/plugin.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/ppcboot.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/reloc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/reloc16.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/rs6000-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/sco5-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/section.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/simple.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/som.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/som.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/srec.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/stab-syms.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/stabs.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/syms.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/targets.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/tekhex.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/trad-core.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/vax1knetbsd.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/vaxnetbsd.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/verilog.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/version.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/vms-alpha.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/vms-lib.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/vms-misc.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/vms.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/wasm-module.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/xcofflink.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/xsym.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/xsym.h \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/xtensa-isa.c \
	/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-gdb/bfd/xtensa-modules.c 

# Note - the following line gets processed by bfd/configure and amended
# to contain the full list of build dir POTFILES.
BLD-POTFILES = \
	../bfd_stdint.h \
	../bfdver.h \
	../elf32-aarch64.c \
	../elf32-ia64.c \
	../elf32-riscv.c \
	../elf32-target.h \
	../elf64-aarch64.c \
	../elf64-ia64.c \
	../elf64-riscv.c \
	../elf64-target.h \
	../peigen.c \
	../pepigen.c \
	../pex64igen.c \
	../targmatch.h 

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
	$(XGETTEXT) --default-domain=$(PACKAGE) \
	  --directory=$(top_srcdir) \
	  --add-comments --keyword=_ --keyword=N_ \
	  --msgid-bugs-address=bug-binutils@gnu.org \
	  --files-from=$(srcdir)/SRC-POTFILES.in 
	$(XGETTEXT) --default-domain=$(PACKAGE) \
	  --directory=.. \
	  --directory=. \
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
	    && (sed -e '/^#/d' \
	            -e '/^[ 	]*$$/d' \
		    -e "s@.*@	$$posrcprefix& \\\\@" < $(srcdir)/$@.in \
		| sed -e '$$s/\\$$//') > $@-t \
	    && chmod a-w $@-t \
	    && mv $@-t $@ )

BLD-POTFILES: BLD-POTFILES.in
	  ( rm -f $@-t $@ \
	    && (sed -e '/^#/d' \
	            -e '/^[ 	]*$$/d' \
		    -e "s@.*@	../& \\\\@" < $(srcdir)/$@.in \
		| sed -e '$$s/\\$$//') > $@-t \
	    && chmod a-w $@-t \
	    && mv $@-t $@ )

SRC-POTFILES.in: # ../Makefile
	cd .. && $(MAKE) po/SRC-POTFILES.in

BLD-POTFILES.in: # ../Makefile
	cd .. && $(MAKE) po/BLD-POTFILES.in

# Note - The presence of SRC-POTFILES and BLD-POTFILES as dependencies
# here breaks the implementation of the 'distclean' rule for maintainers.
# This is because if 'make distclean' is run in the BFD directory, the
# Makefile there will be deleted before 'distclean' is made here, and so
# the dependency SRC-POTFILES -> SRC-POTFILES.in -> ../Makefile cannot
# be satisfied.
#
# The SRC-POTFILES and BLD-POTFILES dependencies cannot be removed,
# however since it is necessary that these files be built during
# *configure* time, so that configure can insert them into the
# po/Makefile that it is creating, so that the Makefile will have
# the correct dependencies.
Makefile: Make-in ../config.status SRC-POTFILES BLD-POTFILES
	cd .. \
	  && CONFIG_FILES=$(subdir)/Makefile.in:$(subdir)/Make-in \
	     CONFIG_HEADERS= $(SHELL) ./config.status

# Tell versions [3.59,3.63) of GNU make not to export all variables.
# Otherwise a system limit (for SysV at least) may be exceeded.
.NOEXPORT:
