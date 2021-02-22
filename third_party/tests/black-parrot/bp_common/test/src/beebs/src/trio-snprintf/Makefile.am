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

if ENABLED_BENCHMARK_TRIO_SNPRINTF

include $(top_srcdir)/src/common.mk.am

bin_PROGRAMS                 = trio-snprintf
noinst_LTLIBRARIES           = libtrio-snprintf.la

trio_snprintf_SOURCES        =

libtrio_snprintf_la_SOURCES  = trio.c trio.h trio_test.c triostr.c triostr.h \
                               triodef.h triop.h

trio_snprintf_LDADD          = $(DUMMY_CRT0) \
                               $(top_builddir)/support/libsupport.la \
                               libtrio-snprintf.la \
                               $(DUMMY_LIBC) $(DUMMY_LIBGCC) $(DUMMY_COMPILERRT)
libtrio_snprintf_la_CPPFLAGS = -DTRIO_EXTENSION=0 -DTRIO_DEPRECATED=0 \
                               -DTRIO_MICROSOFT=0 -DTRIO_ERRORS=0     \
                               -DTRIO_FEATURE_FLOAT=0 -DTRIO_SNPRINTF \
                               -DTRIO_SNPRINTF_ONLY ${AM_CPPFLAGS}

endif
