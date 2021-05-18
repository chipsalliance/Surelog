# Makefile.am for building a BEEBS benchmark
#
# Copyright (C) 2013 Embecosm Limited and University of Bristol
#
# This file is part of the Bristol/Embecosm Embedded Benchmark Suite.
#
# Contributor: James Pallister <james.pallister@bristol.ac.uk>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# SPDX-License-Identifier: GPL-3.0-or-later

if ENABLED_BENCHMARK_STRINGSEARCH1

include $(top_srcdir)/src/common.mk.am

bin_PROGRAMS                = stringsearch1
noinst_LTLIBRARIES          = libstringsearch1.la

stringsearch1_SOURCES       =
libstringsearch1_la_SOURCES = stringsearch1.c fast.fwd.inc.c fast.rev.d12.c

stringsearch1_LDADD         = $(DUMMY_CRT0) \
                              $(top_builddir)/support/libsupport.la \
                              libstringsearch1.la \
                              $(DUMMY_LIBC) $(DUMMY_LIBGCC) $(DUMMY_COMPILERRT)

endif
