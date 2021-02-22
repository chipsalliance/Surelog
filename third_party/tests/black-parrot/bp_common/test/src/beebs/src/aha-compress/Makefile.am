# Makefile.am for building a BEEBS benchmark
#
# Copyright (C) 2014 Embecosm Limited and University of Bristol
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

if ENABLED_BENCHMARK_AHA_COMPRESS

include $(top_srcdir)/src/common.mk.am

bin_PROGRAMS               = aha-compress
noinst_LTLIBRARIES         = libaha-compress.la

aha_compress_SOURCES       =

libaha_compress_la_SOURCES = compress_test.c

aha_compress_LDADD         = $(DUMMY_CRT0) \
                             $(top_builddir)/support/libsupport.la \
                             libaha-compress.la \
                             $(DUMMY_LIBC) $(DUMMY_LIBGCC) $(DUMMY_COMPILERRT)

endif
