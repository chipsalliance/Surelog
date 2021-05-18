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


# Make sure your sources include the headers as well as the C/C++ source
# files, so they go into the distribution. If there are other files that are
# needed, they should go in EXTRA_SOURCES.

if ENABLED_BENCHMARK_SGLIB_LISTINSERTSORT

include $(top_srcdir)/src/common.mk.am

bin_PROGRAMS                       = sglib-listinsertsort
noinst_LTLIBRARIES                 = libsglib-listinsertsort.la

sglib_listinsertsort_SOURCES       =
libsglib_listinsertsort_la_SOURCES = listinsertsort.c sglib.h

sglib_listinsertsort_LDADD         = $(DUMMY_CRT0) \
                                     $(top_builddir)/support/libsupport.la \
                                     libsglib-listinsertsort.la \
                                     $(DUMMY_LIBC) $(DUMMY_LIBGCC) $(DUMMY_COMPILERRT)



endif
