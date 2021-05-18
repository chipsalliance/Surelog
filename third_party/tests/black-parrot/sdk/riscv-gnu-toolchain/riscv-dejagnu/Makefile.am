# Copyright (C) 1992-2015 Free Software Foundation, Inc.
#
# This file is part of DejaGnu.
#
# DejaGnu is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# DejaGnu is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with DejaGnu; if not, write to the Free Software Foundation,
# Inc., 51 Franklin Street - Fifth Floor, Boston, MA 02110-1301, USA.

# Process this file with automake to generate Makefile.in

AUTOMAKE_OPTIONS = dejagnu
export DEJAGNU

EXTRA_DIST = ChangeLog-1992 MAINTAINERS runtest \
	$(pkgdata_DATA) $(config_DATA) $(baseboard_DATA) \
	$(TESTSUITE_FILES) $(XML) $(CONTRIB)

DISTCLEANFILES = xXx.log xXx.sum x.log x.sum testrun.log testrun.sum

# Give a reassuring message so that users know the "build" worked.
all-local:
	@echo "Done. Now run 'make install'."

bin_SCRIPTS = runtest
include_HEADERS = dejagnu.h

pkgdata_DATA = \
  stub-loader.c \
  testglue.c \
  runtest.exp \
  lib/debugger.exp \
  lib/dejagnu.exp \
  lib/dg.exp \
  lib/framework.exp \
  lib/ftp.exp \
  lib/kermit.exp \
  lib/libgloss.exp \
  lib/remote.exp \
  lib/rlogin.exp \
  lib/rsh.exp \
  lib/standard.exp \
  lib/target.exp \
  lib/targetdb.exp \
  lib/telnet.exp \
  lib/tip.exp \
  lib/utils.exp

configdir = $(pkgdatadir)/config
config_DATA = \
	config/README \
	config/adb.exp \
	config/aarch64-fv8.exp \
	config/default.exp \
	config/gdb-comm.exp \
	config/gdb_stub.exp \
	config/sid.exp \
	config/sim.exp \
	config/unix.exp \
	config/vxworks.exp

baseboarddir = $(pkgdatadir)/baseboards
baseboard_DATA = \
	baseboards/README \
	baseboards/androideabi.exp \
	baseboards/am33_2.0-libremote.exp \
	baseboards/arm-ice.exp \
	baseboards/arm-sid.exp \
	baseboards/arm-sim.exp \
	baseboards/basic-sid.exp \
	baseboards/basic-sim.exp \
	baseboards/cris-sim.exp \
	baseboards/d30v-sim.exp \
	baseboards/fr30-sim.exp \
	baseboards/frv-sim.exp \
	baseboards/gdbserver-sample.exp \
	baseboards/i386-sid.exp \
	baseboards/iq2000-sim.exp \
	baseboards/jmr3904-sim.exp \
	baseboards/linux-gdbserver.exp \
	baseboards/linux-libremote.exp \
	baseboards/m68k-sid.exp \
	baseboards/mcore-moto-sim.exp \
	baseboards/mcore-sim.exp \
	baseboards/mips-lnews-sim.exp \
	baseboards/mips-lsi-sim.exp \
	baseboards/mips-sim-idt32.exp \
	baseboards/mips-sim-idt64.exp \
	baseboards/mips-sim.exp \
	baseboards/mips-sim-mti32.exp \
	baseboards/mips-sim-mti64.exp \
	baseboards/mips-sim-mti64_n32.exp \
	baseboards/mips-sim-mti64_64.exp \
	baseboards/mips-sim-sde32.exp \
	baseboards/mips-sim-sde64.exp \
	baseboards/mmixware-sim.exp \
	baseboards/mn10200-sim.exp \
	baseboards/mn10300-sim.exp \
	baseboards/mt-sid.exp \
	baseboards/multi-sim.exp \
	baseboards/powerpc-sim.exp \
	baseboards/powerpcle-sim.exp \
	baseboards/riscv-sim.exp \
	baseboards/riscv-sim-gdb.exp \
	baseboards/riscv-sim-nano.exp \
	baseboards/rx-sim.exp \
	baseboards/sh-sid.exp \
	baseboards/sh-sim.exp \
	baseboards/sparc-sim.exp \
	baseboards/sparc64-sim.exp \
	baseboards/sparclite-sim-le.exp \
	baseboards/sparclite-sim.exp \
	baseboards/tx39-sim.exp \
	baseboards/unix.exp \
	baseboards/v850-sim.exp \
	baseboards/visium-sim.exp \
	baseboards/vr4100-sim.exp \
	baseboards/vr4111-sim.exp \
	baseboards/vr4300-sim.exp \
	baseboards/xtensa-sim.exp

djlibexecdir = $(pkgdatadir)/libexec
djlibexec_SCRIPTS = config.guess

# Contributed scripts, etc.

CONTRIB = contrib/compare_tests contrib/sum2junit.sh \
	contrib/mysql/create-db.sql contrib/mysql/importxml.sh \
	contrib/mysql/make-datafile.sh contrib/mysql/plot.sh \
	contrib/mysql/README contrib/mysql/sum2xml.sh

# Testsuite.

TESTSUITE_FILES = \
	testsuite/runtest.all/topdir/subdir1/subsubdir1/subsubfile1 \
	testsuite/runtest.all/topdir/subdir1/subfile1 \
	testsuite/runtest.all/topdir/subdir1/subfile2 \
	testsuite/runtest.all/topdir/subdir2/subfile2 \
	testsuite/runtest.all/libs.exp \
	testsuite/runtest.all/options.exp \
	testsuite/runtest.all/remote.test \
	testsuite/runtest.all/stats-sub.exp \
	testsuite/runtest.all/stats.exp \
	testsuite/runtest.all/target.test \
	testsuite/runtest.all/utils.test \
	testsuite/runtest.all/clone_output.test \
	testsuite/runtest.all/config.test \
	testsuite/runtest.all/default_procs.tcl \
	testsuite/runtest.all/load_lib.exp \
	testsuite/config/default.exp \
	testsuite/lib/libsup.exp \
	testsuite/lib/util-defs.exp \
	testsuite/libdejagnu/tunit.exp

RUNTEST = ${top_srcdir}/runtest
RUNTESTDEFAULTFLAGS = --srcdir $(srcdir)/testsuite RUNTEST=$(RUNTEST)

AM_CXXFLAGS = -I$(top_srcdir) -g
check_PROGRAMS = unit
unit_SOURCES = testsuite/libdejagnu/unit.cc

# Documentation.

dist_man_MANS = doc/runtest.1
info_TEXINFOS = doc/dejagnu.texi
