# Makefile.am for BEEBS AES test
#
# Copyright (C) 2013 Embecosm Limited and University of Bristol
#
# Contributor Jeremy Bennett <jeremy.bennett@embecosm.com>
#
# This file is part of the Bristol/Embecosm Embedded Benchmark Suite.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program. If not, see <http://www.gnu.org/licenses/>.

# SPDX-License-Identifier: GPL-3.0-or-later

if ENABLED_BENCHMARK_RIJNDAEL

include $(top_srcdir)/src/common.mk.am

bin_PROGRAMS           = rijndael
noinst_LTLIBRARIES     = librijndael.la

rijndael_SOURCES       =

librijndael_la_SOURCES = aes.c aes.h aestab.h aesxam.c

rijndael_LDADD         = $(DUMMY_CRT0) \
                         $(top_builddir)/support/libsupport.la \
                         librijndael.la \
                         $(DUMMY_LIBC) $(DUMMY_LIBGCC) $(DUMMY_COMPILERRT)
rijndael_CFLAGS  = -fno-strict-aliasing ${AM_CFLAGS}

endif
