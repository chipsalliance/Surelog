# Main configure script for BEEBS

# Copyright (C) 2013-2014 Embecosm Limited and the University of Bristol
# Copyright (C) 2018 Embecosm Limited

# Contributor James Pallister <james.pallister@embecosm.com>
# Contributor Jeremy Bennett <jeremy.bennett@embecosm.com>

# This file is part of BEEBS

# This program is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by the Free
# Software Foundation; either version 3 of the License, or (at your option)
# any later version.

# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.

# You should have received a copy of the GNU General Public License along
# with this program.  If not, see <http://www.gnu.org/licenses/>.

# SPDX-License-Identifier: GPL-3.0-or-later

# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.68])

AC_INIT([beebs], [3.0], [beebs@mageec.org])
AC_CONFIG_MACRO_DIR([m4])

AC_CANONICAL_BUILD
AC_CANONICAL_HOST
AC_CANONICAL_TARGET

AM_INIT_AUTOMAKE([-Wno-portability])
AM_MAINTAINER_MODE([disable])
AM_SILENT_RULES([yes])

# List of all benchmarks

bmlist="aha-compress          \
        aha-mont64            \
        bs                    \
        bubblesort            \
        cnt                   \
        compress              \
        cover                 \
        crc                   \
        crc32                 \
        ctl                   \
        ctl-stack             \
        ctl-string            \
        ctl-vector            \
        cubic                 \
        dijkstra              \
        dtoa                  \
        duff                  \
        edn                   \
        expint                \
        fac                   \
        fasta                 \
        fdct                  \
        fibcall               \
        fir                   \
        frac                  \
        huffbench             \
        insertsort            \
        janne_complex         \
        jfdctint              \
        lcdnum                \
        levenshtein           \
        ludcmp                \
        matmult               \
        matmult-float         \
        matmult-int           \
        mergesort             \
        miniz                 \
        minver                \
        nbody                 \
        ndes                  \
        nettle-aes            \
        nettle-arcfour        \
        nettle-cast128        \
        nettle-des            \
        nettle-md5            \
        nettle-sha256         \
        newlib-exp            \
        newlib-log            \
        newlib-mod            \
        newlib-sqrt           \
        ns                    \
        nsichneu              \
        picojpeg              \
        prime                 \
        qrduino               \
        qsort                 \
        qurt                  \
        recursion             \
        rijndael              \
        select                \
        sglib-arraybinsearch  \
        sglib-arrayheapsort   \
        sglib-arrayquicksort  \
        sglib-arraysort       \
        sglib-dllist          \
        sglib-hashtable       \
        sglib-listinsertsort  \
        sglib-listsort        \
        sglib-queue           \
        sglib-rbtree          \
        slre                  \
        sqrt                  \
        st                    \
        statemate             \
        stb_perlin            \
        stringsearch1         \
        strstr                \
        tarai                 \
        template              \
        trio                  \
        trio-snprintf         \
        trio-sscanf           \
        ud                    \
        whetstone             \
        wikisort"

# Set default values enabling all architectures

benchmark_aha_compress=true
benchmark_aha_mont64=true
benchmark_bs=true
benchmark_bubblesort=true
benchmark_cnt=true
benchmark_compress=true
benchmark_cover=true
benchmark_crc=true
benchmark_crc32=true
benchmark_ctl_stack=true
benchmark_ctl_string=true
benchmark_ctl_vector=true
benchmark_cubic=true
benchmark_dijkstra=true
benchmark_dtoa=true
benchmark_duff=true
benchmark_edn=true
benchmark_expint=true
benchmark_fac=true
benchmark_fasta=true
benchmark_fdct=true
benchmark_fibcall=true
benchmark_fir=true
benchmark_frac=true
benchmark_huffbench=true
benchmark_insertsort=true
benchmark_janne_complex=true
benchmark_jfdctint=true
benchmark_lcdnum=true
benchmark_levenshtein=true
benchmark_ludcmp=true
benchmark_matmult_float=true
benchmark_matmult_int=true
benchmark_mergesort=true
benchmark_miniz=true
benchmark_minver=true
benchmark_nbody=true
benchmark_ndes=true
benchmark_nettle_aes=true
benchmark_nettle_arcfour=true
benchmark_nettle_cast128=true
benchmark_nettle_des=true
benchmark_nettle_md5=true
benchmark_nettle_sha256=true
benchmark_newlib_exp=true
benchmark_newlib_log=true
benchmark_newlib_mod=true
benchmark_newlib_sqrt=true
benchmark_ns=true
benchmark_nsichneu=true
benchmark_picojpeg=true
benchmark_prime=true
benchmark_qrduino=true
benchmark_qsort=true
benchmark_qurt=true
benchmark_recursion=true
benchmark_rijndael=true
benchmark_select=true
benchmark_sglib_arraybinsearch=true
benchmark_sglib_arrayheapsort=true
benchmark_sglib_arrayquicksort=true
benchmark_sglib_dllist=true
benchmark_sglib_hashtable=true
benchmark_sglib_listinsertsort=true
benchmark_sglib_listsort=true
benchmark_sglib_queue=true
benchmark_sglib_rbtree=true
benchmark_slre=true
benchmark_sqrt=true
benchmark_st=true
benchmark_statemate=true
benchmark_stb_perlin=true
benchmark_stringsearch1=true
benchmark_strstr=true
benchmark_tarai=true
benchmark_template=true
benchmark_trio_snprintf=true
benchmark_trio_sscanf=true
benchmark_ud=true
benchmark_whetstone=true
benchmark_wikisort=true

# Work out which architecture we are targeting
# Also pass this through to be substituted

arch=$host_cpu

# Option for selecting the target board

AC_ARG_WITH([board],
    [AS_HELP_STRING([--with-board], [Select the board to target])],
    [board=$with_board],
    [board=none])

# Option for selecting the target chip

AC_ARG_WITH([chip],
[AS_HELP_STRING([--with-chip], [Select the chip to target])],
    [chip=$with_chip],
    [chip=generic])

# Default settings for dummy libraries. These can be overridden by the
# chip configuration or configure flags. We default to having them all
# off because we expect the default setup to produce compiled code that
# can actually be executed - however, the dummy libraries are helpful
# for analysing code size without library code inclusion confounding
# things.

USE_DUMMY_CRT0=no
USE_DUMMY_LIBGCC=no
USE_DUMMY_COMPILERRT=no
USE_DUMMY_LIBC=no
USE_DUMMY_LIBM=no

# Execute any architecture, board or chip specific configuration. These can
# set architecture, chip and board CPPFLAGS, CFLAGS and LDFLAGS and exclude
# individual tests by setting benchmark_<bm> to false.

# We can't use AC_CHECK_FILE, because we are cross-compiling, and that
# prohibits use of AC_CHECK_FILE.

AS_IF([test -f $srcdir/config/$arch/arch.cfg],
      [source $srcdir/config/$arch/arch.cfg], [])

AS_IF([test -d $srcdir/config/$arch/chips/$chip],
      [], [AC_MSG_ERROR([Chip config directory "$chip" does not exist])])

AS_IF([test -f $srcdir/config/$arch/chips/$chip/chip.cfg],
      [source $srcdir/config/$arch/chips/$chip/chip.cfg], [])

AS_IF([test -d $srcdir/config/$arch/boards/$board],
      [], [AC_MSG_ERROR([Board config directory "$board" does not exist])])

AS_IF([test -f $srcdir/config/$arch/boards/$board/board.cfg ],
      [source $srcdir/config/$arch/boards/$board/board.cfg], [])

# Options for enabling/disabling each test in alphabetical order (see
# genmacros.sh for a script to generate all of this). To add one new test just
# insert the same pattern at the correct place in the list.

# Remember that ctl, matmult, sglib-arraysort and trio are not benchmarks
# themselves, but the frameworks from which others are created.

# NOTE. There is the m4_foreach macro, but getting it to work for this seems to
# be impossible

AC_ARG_ENABLE([benchmark-aha-compress],
  [AS_HELP_STRING([--enable-benchmark-aha-compress],
     [Enable benchmark aha-compress])],
  [case "${enableval}" in
      yes) benchmark_aha_compress=true ;;
      no)  benchmark_aha_compress=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-aha-compress]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_AHA_COMPRESS],
               [test x$benchmark_aha_compress = xtrue])

AC_ARG_ENABLE([benchmark-aha-mont64],
  [AS_HELP_STRING([--enable-benchmark-aha-mont64],
     [Enable benchmark aha-mont64])],
  [case "${enableval}" in
      yes) benchmark_aha_mont64=true ;;
      no)  benchmark_aha_mont64=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-aha-mont64]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_AHA_MONT64],
               [test x$benchmark_aha_mont64 = xtrue])

AC_ARG_ENABLE([benchmark-bs],
  [AS_HELP_STRING([--enable-benchmark-bs],
     [Enable benchmark bs])],
  [case "${enableval}" in
      yes) benchmark_bs=true ;;
      no)  benchmark_bs=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-bs]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_BS],
               [test x$benchmark_bs = xtrue])

AC_ARG_ENABLE([benchmark-bubblesort],
  [AS_HELP_STRING([--enable-benchmark-bubblesort],
     [Enable benchmark bubblesort])],
  [case "${enableval}" in
      yes) benchmark_bubblesort=true ;;
      no)  benchmark_bubblesort=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-bubblesort]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_BUBBLESORT],
               [test x$benchmark_bubblesort = xtrue])

AC_ARG_ENABLE([benchmark-cnt],
  [AS_HELP_STRING([--enable-benchmark-cnt],
     [Enable benchmark cnt])],
  [case "${enableval}" in
      yes) benchmark_cnt=true ;;
      no)  benchmark_cnt=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-cnt]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_CNT],
               [test x$benchmark_cnt = xtrue])

AC_ARG_ENABLE([benchmark-compress],
  [AS_HELP_STRING([--enable-benchmark-compress],
     [Enable benchmark compress])],
  [case "${enableval}" in
      yes) benchmark_compress=true ;;
      no)  benchmark_compress=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-compress]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_COMPRESS],
               [test x$benchmark_compress = xtrue])

AC_ARG_ENABLE([benchmark-cover],
  [AS_HELP_STRING([--enable-benchmark-cover],
     [Enable benchmark cover])],
  [case "${enableval}" in
      yes) benchmark_cover=true ;;
      no)  benchmark_cover=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-cover]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_COVER],
               [test x$benchmark_cover = xtrue])

AC_ARG_ENABLE([benchmark-crc],
  [AS_HELP_STRING([--enable-benchmark-crc],
     [Enable benchmark crc])],
  [case "${enableval}" in
      yes) benchmark_crc=true ;;
      no)  benchmark_crc=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-crc]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_CRC],
               [test x$benchmark_crc = xtrue])

AC_ARG_ENABLE([benchmark-crc32],
  [AS_HELP_STRING([--enable-benchmark-crc32],
     [Enable benchmark crc32])],
  [case "${enableval}" in
      yes) benchmark_crc32=true ;;
      no)  benchmark_crc32=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-crc32]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_CRC32],
               [test x$benchmark_crc32 = xtrue])

AC_ARG_ENABLE([benchmark-ctl-stack],
  [AS_HELP_STRING([--enable-benchmark-ctl-stack],
     [Enable benchmark ctl-stack])],
  [case "${enableval}" in
      yes) benchmark_ctl_stack=true ;;
      no)  benchmark_ctl_stack=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-ctl-stack]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_CTL_STACK],
               [test x$benchmark_ctl_stack = xtrue])

AC_ARG_ENABLE([benchmark-ctl-string],
  [AS_HELP_STRING([--enable-benchmark-ctl-string],
     [Enable benchmark ctl-string])],
  [case "${enableval}" in
      yes) benchmark_ctl_string=true ;;
      no)  benchmark_ctl_string=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-ctl-string]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_CTL_STRING],
               [test x$benchmark_ctl_string = xtrue])

AC_ARG_ENABLE([benchmark-ctl-vector],
  [AS_HELP_STRING([--enable-benchmark-ctl-vector],
     [Enable benchmark ctl-vector])],
  [case "${enableval}" in
      yes) benchmark_ctl_vector=true ;;
      no)  benchmark_ctl_vector=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-ctl-vector]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_CTL_VECTOR],
               [test x$benchmark_ctl_vector = xtrue])

AC_ARG_ENABLE([benchmark-cubic],
  [AS_HELP_STRING([--enable-benchmark-cubic],
     [Enable benchmark cubic])],
  [case "${enableval}" in
      yes) benchmark_cubic=true ;;
      no)  benchmark_cubic=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-cubic]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_CUBIC],
               [test x$benchmark_cubic = xtrue])

AC_ARG_ENABLE([benchmark-dijkstra],
  [AS_HELP_STRING([--enable-benchmark-dijkstra],
     [Enable benchmark dijkstra])],
  [case "${enableval}" in
      yes) benchmark_dijkstra=true ;;
      no)  benchmark_dijkstra=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-dijkstra]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_DIJKSTRA],
               [test x$benchmark_dijkstra = xtrue])

AC_ARG_ENABLE([benchmark-dtoa],
  [AS_HELP_STRING([--enable-benchmark-dtoa],
     [Enable benchmark dtoa])],
  [case "${enableval}" in
      yes) benchmark_dtoa=true ;;
      no)  benchmark_dtoa=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-dtoa]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_DTOA],
               [test x$benchmark_dtoa = xtrue])

AC_ARG_ENABLE([benchmark-duff],
  [AS_HELP_STRING([--enable-benchmark-duff],
     [Enable benchmark duff])],
  [case "${enableval}" in
      yes) benchmark_duff=true ;;
      no)  benchmark_duff=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-duff]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_DUFF],
               [test x$benchmark_duff = xtrue])

AC_ARG_ENABLE([benchmark-edn],
  [AS_HELP_STRING([--enable-benchmark-edn],
     [Enable benchmark edn])],
  [case "${enableval}" in
      yes) benchmark_edn=true ;;
      no)  benchmark_edn=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-edn]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_EDN],
               [test x$benchmark_edn = xtrue])

AC_ARG_ENABLE([benchmark-expint],
  [AS_HELP_STRING([--enable-benchmark-expint],
     [Enable benchmark expint])],
  [case "${enableval}" in
      yes) benchmark_expint=true ;;
      no)  benchmark_expint=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-expint]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_EXPINT],
               [test x$benchmark_expint = xtrue])

AC_ARG_ENABLE([benchmark-fac],
  [AS_HELP_STRING([--enable-benchmark-fac],
     [Enable benchmark fac])],
  [case "${enableval}" in
      yes) benchmark_fac=true ;;
      no)  benchmark_fac=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-fac]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_FAC],
               [test x$benchmark_fac = xtrue])

AC_ARG_ENABLE([benchmark-fasta],
  [AS_HELP_STRING([--enable-benchmark-fasta],
     [Enable benchmark fasta])],
  [case "${enableval}" in
      yes) benchmark_fasta=true ;;
      no)  benchmark_fasta=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-fasta]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_FASTA],
               [test x$benchmark_fasta = xtrue])

AC_ARG_ENABLE([benchmark-fdct],
  [AS_HELP_STRING([--enable-benchmark-fdct],
     [Enable benchmark fdct])],
  [case "${enableval}" in
      yes) benchmark_fdct=true ;;
      no)  benchmark_fdct=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-fdct]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_FDCT],
               [test x$benchmark_fdct = xtrue])

AC_ARG_ENABLE([benchmark-fibcall],
  [AS_HELP_STRING([--enable-benchmark-fibcall],
     [Enable benchmark fibcall])],
  [case "${enableval}" in
      yes) benchmark_fibcall=true ;;
      no)  benchmark_fibcall=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-fibcall]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_FIBCALL],
               [test x$benchmark_fibcall = xtrue])

AC_ARG_ENABLE([benchmark-fir],
  [AS_HELP_STRING([--enable-benchmark-fir],
     [Enable benchmark fir])],
  [case "${enableval}" in
      yes) benchmark_fir=true ;;
      no)  benchmark_fir=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-fir]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_FIR],
               [test x$benchmark_fir = xtrue])

AC_ARG_ENABLE([benchmark-frac],
  [AS_HELP_STRING([--enable-benchmark-frac],
     [Enable benchmark frac])],
  [case "${enableval}" in
      yes) benchmark_frac=true ;;
      no)  benchmark_frac=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-frac]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_FRAC],
               [test x$benchmark_frac = xtrue])

AC_ARG_ENABLE([benchmark-huffbench],
  [AS_HELP_STRING([--enable-benchmark-huffbench],
     [Enable benchmark huffbench])],
  [case "${enableval}" in
      yes) benchmark_huffbench=true ;;
      no)  benchmark_huffbench=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-huffbench]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_HUFFBENCH],
               [test x$benchmark_huffbench = xtrue])

AC_ARG_ENABLE([benchmark-insertsort],
  [AS_HELP_STRING([--enable-benchmark-insertsort],
     [Enable benchmark insertsort])],
  [case "${enableval}" in
      yes) benchmark_insertsort=true ;;
      no)  benchmark_insertsort=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-insertsort]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_INSERTSORT],
               [test x$benchmark_insertsort = xtrue])

AC_ARG_ENABLE([benchmark-janne_complex],
  [AS_HELP_STRING([--enable-benchmark-janne_complex],
     [Enable benchmark janne_complex])],
  [case "${enableval}" in
      yes) benchmark_janne_complex=true ;;
      no)  benchmark_janne_complex=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-janne_complex]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_JANNE_COMPLEX],
               [test x$benchmark_janne_complex = xtrue])

AC_ARG_ENABLE([benchmark-jfdctint],
  [AS_HELP_STRING([--enable-benchmark-jfdctint],
     [Enable benchmark jfdctint])],
  [case "${enableval}" in
      yes) benchmark_jfdctint=true ;;
      no)  benchmark_jfdctint=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-jfdctint]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_JFDCTINT],
               [test x$benchmark_jfdctint = xtrue])

AC_ARG_ENABLE([benchmark-lcdnum],
  [AS_HELP_STRING([--enable-benchmark-lcdnum],
     [Enable benchmark lcdnum])],
  [case "${enableval}" in
      yes) benchmark_lcdnum=true ;;
      no)  benchmark_lcdnum=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-lcdnum]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_LCDNUM],
               [test x$benchmark_lcdnum = xtrue])

AC_ARG_ENABLE([benchmark-levenshtein],
  [AS_HELP_STRING([--enable-benchmark-levenshtein],
     [Enable benchmark levenshtein])],
  [case "${enableval}" in
      yes) benchmark_levenshtein=true ;;
      no)  benchmark_levenshtein=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-levenshtein]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_LEVENSHTEIN],
               [test x$benchmark_levenshtein = xtrue])

AC_ARG_ENABLE([benchmark-ludcmp],
  [AS_HELP_STRING([--enable-benchmark-ludcmp],
     [Enable benchmark ludcmp])],
  [case "${enableval}" in
      yes) benchmark_ludcmp=true ;;
      no)  benchmark_ludcmp=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-ludcmp]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_LUDCMP],
               [test x$benchmark_ludcmp = xtrue])

AC_ARG_ENABLE([benchmark-matmult-float],
  [AS_HELP_STRING([--enable-benchmark-matmult-float],
     [Enable benchmark matmult-float])],
  [case "${enableval}" in
      yes) benchmark_matmult_float=true ;;
      no)  benchmark_matmult_float=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-matmult-float]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_MATMULT_FLOAT],
               [test x$benchmark_matmult_float = xtrue])

AC_ARG_ENABLE([benchmark-matmult-int],
  [AS_HELP_STRING([--enable-benchmark-matmult-int],
     [Enable benchmark matmult-int])],
  [case "${enableval}" in
      yes) benchmark_matmult_int=true ;;
      no)  benchmark_matmult_int=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-matmult-int]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_MATMULT_INT],
               [test x$benchmark_matmult_int = xtrue])

AC_ARG_ENABLE([benchmark-mergesort],
  [AS_HELP_STRING([--enable-benchmark-mergesort],
     [Enable benchmark mergesort])],
  [case "${enableval}" in
      yes) benchmark_mergesort=true ;;
      no)  benchmark_mergesort=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-mergesort]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_MERGESORT],
               [test x$benchmark_mergesort = xtrue])

AC_ARG_ENABLE([benchmark-miniz],
  [AS_HELP_STRING([--enable-benchmark-miniz],
     [Enable benchmark miniz])],
  [case "${enableval}" in
      yes) benchmark_miniz=true ;;
      no)  benchmark_miniz=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-miniz]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_MINIZ],
               [test x$benchmark_miniz = xtrue])

AC_ARG_ENABLE([benchmark-minver],
  [AS_HELP_STRING([--enable-benchmark-minver],
     [Enable benchmark minver])],
  [case "${enableval}" in
      yes) benchmark_minver=true ;;
      no)  benchmark_minver=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-minver]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_MINVER],
               [test x$benchmark_minver = xtrue])

AC_ARG_ENABLE([benchmark-nbody],
  [AS_HELP_STRING([--enable-benchmark-nbody],
     [Enable benchmark nbody])],
  [case "${enableval}" in
      yes) benchmark_nbody=true ;;
      no)  benchmark_nbody=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-nbody]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NBODY],
               [test x$benchmark_nbody = xtrue])

AC_ARG_ENABLE([benchmark-ndes],
  [AS_HELP_STRING([--enable-benchmark-ndes],
     [Enable benchmark ndes])],
  [case "${enableval}" in
      yes) benchmark_ndes=true ;;
      no)  benchmark_ndes=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-ndes]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NDES],
               [test x$benchmark_ndes = xtrue])

AC_ARG_ENABLE([benchmark-nettle-aes],
  [AS_HELP_STRING([--enable-benchmark-nettle-aes],
     [Enable benchmark nettle-aes])],
  [case "${enableval}" in
      yes) benchmark_nettle_aes=true ;;
      no)  benchmark_nettle_aes=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-nettle-aes]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NETTLE_AES],
               [test x$benchmark_nettle_aes = xtrue])

AC_ARG_ENABLE([benchmark-nettle-arcfour],
  [AS_HELP_STRING([--enable-benchmark-nettle-arcfour],
     [Enable benchmark nettle-arcfour])],
  [case "${enableval}" in
      yes) benchmark_nettle_arcfour=true ;;
      no)  benchmark_nettle_arcfour=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-nettle-arcfour]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NETTLE_ARCFOUR],
               [test x$benchmark_nettle_arcfour = xtrue])

AC_ARG_ENABLE([benchmark-nettle-cast128],
  [AS_HELP_STRING([--enable-benchmark-nettle-cast128],
     [Enable benchmark nettle-cast128])],
  [case "${enableval}" in
      yes) benchmark_nettle_cast128=true ;;
      no)  benchmark_nettle_cast128=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-nettle-cast128]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NETTLE_CAST128],
               [test x$benchmark_nettle_cast128 = xtrue])

AC_ARG_ENABLE([benchmark-nettle-des],
  [AS_HELP_STRING([--enable-benchmark-nettle-des],
     [Enable benchmark nettle-des])],
  [case "${enableval}" in
      yes) benchmark_nettle_des=true ;;
      no)  benchmark_nettle_des=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-nettle-des]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NETTLE_DES],
               [test x$benchmark_nettle_des = xtrue])

AC_ARG_ENABLE([benchmark-nettle-md5],
  [AS_HELP_STRING([--enable-benchmark-nettle-md5],
     [Enable benchmark nettle-md5])],
  [case "${enableval}" in
      yes) benchmark_nettle_md5=true ;;
      no)  benchmark_nettle_md5=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-nettle-md5]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NETTLE_MD5],
               [test x$benchmark_nettle_md5 = xtrue])

AC_ARG_ENABLE([benchmark-nettle-sha256],
  [AS_HELP_STRING([--enable-benchmark-nettle-sha256],
     [Enable benchmark nettle-sha256])],
  [case "${enableval}" in
      yes) benchmark_nettle_sha256=true ;;
      no)  benchmark_nettle_sha256=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-nettle-sha256]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NETTLE_SHA256],
               [test x$benchmark_nettle_sha256 = xtrue])


AC_ARG_ENABLE([benchmark-newlib-exp],
  [AS_HELP_STRING([--enable-benchmark-newlib-exp],
     [Enable benchmark newlib-exp])],
  [case "${enableval}" in
      yes) benchmark_newlib_exp=true ;;
      no)  benchmark_newlib_exp=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-newlib-exp]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NEWLIB_EXP],
               [test x$benchmark_newlib_exp = xtrue])

AC_ARG_ENABLE([benchmark-newlib-log],
  [AS_HELP_STRING([--enable-benchmark-newlib-log],
     [Enable benchmark newlib-log])],
  [case "${enableval}" in
      yes) benchmark_newlib_log=true ;;
      no)  benchmark_newlib_log=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-newlib-log]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NEWLIB_LOG],
               [test x$benchmark_newlib_log = xtrue])

AC_ARG_ENABLE([benchmark-newlib-mod],
  [AS_HELP_STRING([--enable-benchmark-newlib-mod],
     [Enable benchmark newlib-mod])],
  [case "${enableval}" in
      yes) benchmark_newlib_mod=true ;;
      no)  benchmark_newlib_mod=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-newlib-mod]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NEWLIB_MOD],
               [test x$benchmark_newlib_mod = xtrue])

AC_ARG_ENABLE([benchmark-newlib-sqrt],
  [AS_HELP_STRING([--enable-benchmark-newlib-sqrt],
     [Enable benchmark newlib-sqrt])],
  [case "${enableval}" in
      yes) benchmark_newlib_sqrt=true ;;
      no)  benchmark_newlib_sqrt=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-newlib-sqrt]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NEWLIB_SQRT],
               [test x$benchmark_newlib_sqrt = xtrue])

AC_ARG_ENABLE([benchmark-ns],
  [AS_HELP_STRING([--enable-benchmark-ns],
     [Enable benchmark ns])],
  [case "${enableval}" in
      yes) benchmark_ns=true ;;
      no)  benchmark_ns=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-ns]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NS],
               [test x$benchmark_ns = xtrue])

AC_ARG_ENABLE([benchmark-nsichneu],
  [AS_HELP_STRING([--enable-benchmark-nsichneu],
     [Enable benchmark nsichneu])],
  [case "${enableval}" in
      yes) benchmark_nsichneu=true ;;
      no)  benchmark_nsichneu=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-nsichneu]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_NSICHNEU],
               [test x$benchmark_nsichneu = xtrue])

AC_ARG_ENABLE([benchmark-picojpeg],
  [AS_HELP_STRING([--enable-benchmark-picojpeg],
     [Enable benchmark picojpeg])],
  [case "${enableval}" in
      yes) benchmark_picojpeg=true ;;
      no)  benchmark_picojpeg=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-picojpeg]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_PICOJPEG],
               [test x$benchmark_picojpeg = xtrue])

AC_ARG_ENABLE([benchmark-prime],
  [AS_HELP_STRING([--enable-benchmark-prime],
     [Enable benchmark prime])],
  [case "${enableval}" in
      yes) benchmark_prime=true ;;
      no)  benchmark_prime=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-prime]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_PRIME],
               [test x$benchmark_prime = xtrue])

AC_ARG_ENABLE([benchmark-qrduino],
  [AS_HELP_STRING([--enable-benchmark-qrduino],
     [Enable benchmark qrduino])],
  [case "${enableval}" in
      yes) benchmark_qrduino=true ;;
      no)  benchmark_qrduino=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-qrduino]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_QRDUINO],
               [test x$benchmark_qrduino = xtrue])

AC_ARG_ENABLE([benchmark-qsort],
  [AS_HELP_STRING([--enable-benchmark-qsort],
     [Enable benchmark qsort])],
  [case "${enableval}" in
      yes) benchmark_qsort=true ;;
      no)  benchmark_qsort=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-qsort]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_QSORT],
               [test x$benchmark_qsort = xtrue])

AC_ARG_ENABLE([benchmark-qurt],
  [AS_HELP_STRING([--enable-benchmark-qurt],
     [Enable benchmark qurt])],
  [case "${enableval}" in
      yes) benchmark_qurt=true ;;
      no)  benchmark_qurt=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-qurt]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_QURT],
               [test x$benchmark_qurt = xtrue])

AC_ARG_ENABLE([benchmark-recursion],
  [AS_HELP_STRING([--enable-benchmark-recursion],
     [Enable benchmark recursion])],
  [case "${enableval}" in
      yes) benchmark_recursion=true ;;
      no)  benchmark_recursion=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-recursion]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_RECURSION],
               [test x$benchmark_recursion = xtrue])

AC_ARG_ENABLE([benchmark-rijndael],
  [AS_HELP_STRING([--enable-benchmark-rijndael],
     [Enable benchmark rijndael])],
  [case "${enableval}" in
      yes) benchmark_rijndael=true ;;
      no)  benchmark_rijndael=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-rijndael]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_RIJNDAEL],
               [test x$benchmark_rijndael = xtrue])

AC_ARG_ENABLE([benchmark-select],
  [AS_HELP_STRING([--enable-benchmark-select],
     [Enable benchmark select])],
  [case "${enableval}" in
      yes) benchmark_select=true ;;
      no)  benchmark_select=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-select]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SELECT],
               [test x$benchmark_select = xtrue])

AC_ARG_ENABLE([benchmark-sglib-arraybinsearch],
  [AS_HELP_STRING([--enable-benchmark-sglib-arraybinsearch],
     [Enable benchmark sglib-arraybinsearch])],
  [case "${enableval}" in
      yes) benchmark_sglib_arraybinsearch=true ;;
      no)  benchmark_sglib_arraybinsearch=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sglib-arraybinsearch]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SGLIB_ARRAYBINSEARCH],
               [test x$benchmark_sglib_arraybinsearch = xtrue])

AC_ARG_ENABLE([benchmark-sglib-arrayheapsort],
  [AS_HELP_STRING([--enable-benchmark-sglib-arrayheapsort],
     [Enable benchmark sglib-arrayheapsort])],
  [case "${enableval}" in
      yes) benchmark_sglib_arrayheapsort=true ;;
      no)  benchmark_sglib_arrayheapsort=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sglib-arrayheapsort]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SGLIB_ARRAYHEAPSORT],
               [test x$benchmark_sglib_arrayheapsort = xtrue])

AC_ARG_ENABLE([benchmark-sglib-arrayquicksort],
  [AS_HELP_STRING([--enable-benchmark-sglib-arrayquicksort],
     [Enable benchmark sglib-arrayquicksort])],
  [case "${enableval}" in
      yes) benchmark_sglib_arrayquicksort=true ;;
      no)  benchmark_sglib_arrayquicksort=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sglib-arrayquicksort]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SGLIB_ARRAYQUICKSORT],
               [test x$benchmark_sglib_arrayquicksort = xtrue])

AC_ARG_ENABLE([benchmark-sglib-dllist],
  [AS_HELP_STRING([--enable-benchmark-sglib-dllist],
     [Enable benchmark sglib-dllist])],
  [case "${enableval}" in
      yes) benchmark_sglib_dllist=true ;;
      no)  benchmark_sglib_dllist=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sglib-dllist]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SGLIB_DLLIST],
               [test x$benchmark_sglib_dllist = xtrue])

AC_ARG_ENABLE([benchmark-sglib-hashtable],
  [AS_HELP_STRING([--enable-benchmark-sglib-hashtable],
     [Enable benchmark sglib-hashtable])],
  [case "${enableval}" in
      yes) benchmark_sglib_hashtable=true ;;
      no)  benchmark_sglib_hashtable=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sglib-hashtable]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SGLIB_HASHTABLE],
               [test x$benchmark_sglib_hashtable = xtrue])

AC_ARG_ENABLE([benchmark-sglib-listinsertsort],
  [AS_HELP_STRING([--enable-benchmark-sglib-listinsertsort],
     [Enable benchmark sglib-listinsertsort])],
  [case "${enableval}" in
      yes) benchmark_sglib_listinsertsort=true ;;
      no)  benchmark_sglib_listinsertsort=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sglib-listinsertsort]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SGLIB_LISTINSERTSORT],
               [test x$benchmark_sglib_listinsertsort = xtrue])

AC_ARG_ENABLE([benchmark-sglib-listsort],
  [AS_HELP_STRING([--enable-benchmark-sglib-listsort],
     [Enable benchmark sglib-listsort])],
  [case "${enableval}" in
      yes) benchmark_sglib_listsort=true ;;
      no)  benchmark_sglib_listsort=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sglib-listsort]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SGLIB_LISTSORT],
               [test x$benchmark_sglib_listsort = xtrue])

AC_ARG_ENABLE([benchmark-sglib-queue],
  [AS_HELP_STRING([--enable-benchmark-sglib-queue],
     [Enable benchmark sglib-queue])],
  [case "${enableval}" in
      yes) benchmark_sglib_queue=true ;;
      no)  benchmark_sglib_queue=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sglib-queue]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SGLIB_QUEUE],
               [test x$benchmark_sglib_queue = xtrue])

AC_ARG_ENABLE([benchmark-sglib-rbtree],
  [AS_HELP_STRING([--enable-benchmark-sglib-rbtree],
     [Enable benchmark sglib-rbtree])],
  [case "${enableval}" in
      yes) benchmark_sglib_rbtree=true ;;
      no)  benchmark_sglib_rbtree=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sglib-rbtree]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SGLIB_RBTREE],
               [test x$benchmark_sglib_rbtree = xtrue])

AC_ARG_ENABLE([benchmark-slre],
  [AS_HELP_STRING([--enable-benchmark-slre],
     [Enable benchmark slre])],
  [case "${enableval}" in
      yes) benchmark_slre=true ;;
      no)  benchmark_slre=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-slre]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SLRE],
               [test x$benchmark_slre = xtrue])

AC_ARG_ENABLE([benchmark-sqrt],
  [AS_HELP_STRING([--enable-benchmark-sqrt],
     [Enable benchmark sqrt])],
  [case "${enableval}" in
      yes) benchmark_sqrt=true ;;
      no)  benchmark_sqrt=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-sqrt]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_SQRT],
               [test x$benchmark_sqrt = xtrue])

AC_ARG_ENABLE([benchmark-st],
  [AS_HELP_STRING([--enable-benchmark-st],
     [Enable benchmark st])],
  [case "${enableval}" in
      yes) benchmark_st=true ;;
      no)  benchmark_st=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-st]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_ST],
               [test x$benchmark_st = xtrue])

AC_ARG_ENABLE([benchmark-statemate],
  [AS_HELP_STRING([--enable-benchmark-statemate],
     [Enable benchmark statemate])],
  [case "${enableval}" in
      yes) benchmark_statemate=true ;;
      no)  benchmark_statemate=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-statemate]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_STATEMATE],
               [test x$benchmark_statemate = xtrue])

AC_ARG_ENABLE([benchmark-stb_perlin],
  [AS_HELP_STRING([--enable-benchmark-stb_perlin],
     [Enable benchmark stb_perlin])],
  [case "${enableval}" in
      yes) benchmark_stb_perlin=true ;;
      no)  benchmark_stb_perlin=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-stb_perlin]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_STB_PERLIN],
               [test x$benchmark_stb_perlin = xtrue])

AC_ARG_ENABLE([benchmark-stringsearch1],
  [AS_HELP_STRING([--enable-benchmark-stringsearch1],
     [Enable benchmark stringsearch1])],
  [case "${enableval}" in
      yes) benchmark_stringsearch1=true ;;
      no)  benchmark_stringsearch1=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-stringsearch1]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_STRINGSEARCH1],
               [test x$benchmark_stringsearch1 = xtrue])

AC_ARG_ENABLE([benchmark-strstr],
  [AS_HELP_STRING([--enable-benchmark-strstr],
     [Enable benchmark strstr])],
  [case "${enableval}" in
      yes) benchmark_strstr=true ;;
      no)  benchmark_strstr=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-strstr]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_STRSTR],
               [test x$benchmark_strstr = xtrue])

AC_ARG_ENABLE([benchmark-tarai],
  [AS_HELP_STRING([--enable-benchmark-tarai],
     [Enable benchmark tarai])],
  [case "${enableval}" in
      yes) benchmark_tarai=true ;;
      no)  benchmark_tarai=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-tarai]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_TARAI],
               [test x$benchmark_tarai = xtrue])

AC_ARG_ENABLE([benchmark-template],
  [AS_HELP_STRING([--enable-benchmark-template],
     [Enable benchmark template])],
  [case "${enableval}" in
      yes) benchmark_template=true ;;
      no)  benchmark_template=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-template]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_TEMPLATE],
               [test x$benchmark_template = xtrue])

AC_ARG_ENABLE([benchmark-trio-snprintf],
  [AS_HELP_STRING([--enable-benchmark-trio-snprintf],
     [Enable benchmark trio-snprintf])],
  [case "${enableval}" in
      yes) benchmark_trio_snprintf=true ;;
      no)  benchmark_trio_snprintf=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-trio-snprintf]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_TRIO_SNPRINTF],
               [test x$benchmark_trio_snprintf = xtrue])

AC_ARG_ENABLE([benchmark-trio-sscanf],
  [AS_HELP_STRING([--enable-benchmark-trio-sscanf],
     [Enable benchmark trio-sscanf])],
  [case "${enableval}" in
      yes) benchmark_trio_sscanf=true ;;
      no)  benchmark_trio_sscanf=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-trio-sscanf]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_TRIO_SSCANF],
               [test x$benchmark_trio_sscanf = xtrue])

AC_ARG_ENABLE([benchmark-ud],
  [AS_HELP_STRING([--enable-benchmark-ud],
     [Enable benchmark ud])],
  [case "${enableval}" in
      yes) benchmark_ud=true ;;
      no)  benchmark_ud=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-ud]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_UD],
               [test x$benchmark_ud = xtrue])

AC_ARG_ENABLE([benchmark-whetstone],
  [AS_HELP_STRING([--enable-benchmark-whetstone],
     [Enable benchmark whetstone])],
  [case "${enableval}" in
      yes) benchmark_whetstone=true ;;
      no)  benchmark_whetstone=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-whetstone]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_WHETSTONE],
               [test x$benchmark_whetstone = xtrue])

AC_ARG_ENABLE([benchmark-wikisort],
  [AS_HELP_STRING([--enable-benchmark-wikisort],
     [Enable benchmark wikisort])],
  [case "${enableval}" in
      yes) benchmark_wikisort=true ;;
      no)  benchmark_wikisort=false ;;
      *)   AC_MSG_ERROR([bad value ${enableval} for --enable-benchmark-wikisort]) ;;
   esac],
  [])
AM_CONDITIONAL([ENABLED_BENCHMARK_WIKISORT],
               [test x$benchmark_wikisort = xtrue])


# What to set DUMMY_* to if the dummy libraries are enabled.

DUMMY_CRT0_YES="\$(top_builddir)/support/libdummycrt0.la"
DUMMY_LIBGCC_YES="\$(top_builddir)/support/libdummygcc.la"
DUMMY_COMPILERRT_YES="\$(top_builddir)/support/libdummycompilerrt.la"
DUMMY_LIBC_YES="-Wl,--start-group \$(top_builddir)/support/libdummyc.la"
DUMMY_LIBM_YES="\$(top_builddir)/support/libdummym.la"

# Enable dummy libraries

case "${USE_DUMMY_CRT0}" in
   yes) DUMMY_CRT0=${DUMMY_CRT0_YES} ;;
   no)  DUMMY_CRT0= ;;
   *)   DUMMY_CRT0=${USE_DUMMY_CRT0} ;;
esac

case "${USE_DUMMY_LIBGCC}" in
   yes) DUMMY_LIBGCC=${DUMMY_LIBGCC_YES} ;;
   no)  DUMMY_LIBGCC= ;;
   *)   DUMMY_LIBGCC=${USE_DUMMY_LIBGCC} ;;
esac

case "${USE_DUMMY_COMPILERRT}" in
   yes) DUMMY_COMPILERRT=${DUMMY_COMPILERRT_YES} ;;
   no)  DUMMY_COMPILERRT= ;;
   *)   DUMMY_COMPILERRT=${USE_DUMMY_COMPILERRT} ;;
esac

case "${USE_DUMMY_LIBC}" in
   yes) DUMMY_LIBC=${DUMMY_LIBC_YES} ;;
   no)  DUMMY_LIBC= ;;
   *)   DUMMY_LIBC=${USE_DUMMY_LIBC} ;;
esac

case "${USE_DUMMY_LIBM}" in
   yes) DUMMY_LIBM=${DUMMY_LIBM_YES} ;;
   no)  DUMMY_LIBM="-lm" ;;
   *)   DUMMY_LIBM=${USE_DUMMY_LIBM} ;;
esac

# Check for support code

AM_CONDITIONAL([CHIPSUPPORT_C],
	       [test -f $srcdir/config/$arch/chips/$chip/chipsupport.c])

# Check for support headers

test -f $srcdir/config/$arch/boards/$board/boardsupport.h && \
    AC_DEFINE([HAVE_BOARDSUPPORT_H], [1], [Board support header is present])

test -f $srcdir/config/$arch/chips/$chip/chipsupport.h && \
    AC_DEFINE([HAVE_CHIPSUPPORT_H], [1], [Chip support header is present])

# Test whether we have a calibration file

test -f $srcdir/config/$arch/boards/$board/calibration && \
    HAVE_CALIBRATION=yes && \
    AC_DEFINE([HAVE_CALIBRATION], [1], [Calibration file is present])

AM_CONDITIONAL([CALIBRATION], [test x$HAVE_CALIBRATION == xyes])

# Architecture, board and chip specific and user CFLAGS and LDFLAGS
CFLAGS="$CFLAGS $ARCH_CFLAGS $CHIP_CFLAGS $BOARD_CFLAGS $USER_CFLAGS"
LDFLAGS="$LDFLAGS $ARCH_LDFLAGS $CHIP_LDFLAGS $BOARD_LDFLAGS $USER_LDFLAGS"

LT_INIT
AC_SUBST([LIBTOOL_DEPS])

AC_PROG_CC()
AM_PROG_AS
AC_PROG_CC_C99

# Set up testing

if test x"$DEJAGNU" = x
then
    DEJAGNU="\$(top_srcdir)/testsuite/beebs-conf.exp"
fi

# Substitute flags

AC_SUBST([CFLAGS])
AC_SUBST([LDFLAGS])

# Substitute dummy libraries

AC_SUBST([DUMMY_CRT0])
AC_SUBST([DUMMY_LIBGCC])
AC_SUBST([DUMMY_COMPILERRT])
AC_SUBST([DUMMY_LIBC])
AC_SUBST([DUMMY_LIBM])

# Substitute architecture, board and chip

AC_SUBST(ARCH, $arch)
AC_SUBST(BOARD, $board)
AC_SUBST(CHIP, $chip)

AM_CONDITIONAL([ARC], [test x$arch = xarc])

# Substitute DejaGnu variable

AC_SUBST([DEJAGNU])

# Substitute benchmark list

AC_SUBST([BENCHMARKS],$bmlist)

# Safety check we haven't been given a nonsense srcdir

AC_CONFIG_SRCDIR([src/])

# Generate the config.h

AC_CONFIG_HEADERS([config.h])

# Generate makefiles

AC_CONFIG_FILES([Makefile                          \
                 doc/Makefile                      \
                 src/Makefile                      \
                 src/aha-compress/Makefile         \
		 src/aha-mont64/Makefile           \
                 src/bs/Makefile                   \
                 src/bubblesort/Makefile           \
                 src/cnt/Makefile                  \
                 src/compress/Makefile             \
                 src/cover/Makefile                \
                 src/crc/Makefile                  \
                 src/crc32/Makefile                \
                 src/ctl/Makefile                  \
                 src/ctl-stack/Makefile            \
                 src/ctl-string/Makefile           \
                 src/ctl-vector/Makefile           \
                 src/cubic/Makefile                \
                 src/dijkstra/Makefile             \
                 src/dtoa/Makefile                 \
                 src/duff/Makefile                 \
                 src/edn/Makefile                  \
                 src/expint/Makefile               \
                 src/fac/Makefile                  \
                 src/fasta/Makefile                \
                 src/fdct/Makefile                 \
                 src/fibcall/Makefile              \
                 src/fir/Makefile                  \
                 src/frac/Makefile                 \
                 src/huffbench/Makefile            \
                 src/insertsort/Makefile           \
                 src/janne_complex/Makefile        \
                 src/jfdctint/Makefile             \
                 src/lcdnum/Makefile               \
                 src/levenshtein/Makefile          \
                 src/ludcmp/Makefile               \
                 src/matmult/Makefile              \
                 src/matmult-float/Makefile        \
                 src/matmult-int/Makefile          \
                 src/mergesort/Makefile            \
                 src/miniz/Makefile                \
                 src/minver/Makefile               \
                 src/nbody/Makefile                \
                 src/ndes/Makefile                 \
                 src/nettle-aes/Makefile           \
                 src/nettle-arcfour/Makefile       \
                 src/nettle-cast128/Makefile       \
                 src/nettle-des/Makefile           \
                 src/nettle-md5/Makefile           \
                 src/nettle-sha256/Makefile        \
                 src/newlib-exp/Makefile           \
                 src/newlib-log/Makefile           \
                 src/newlib-mod/Makefile           \
                 src/newlib-sqrt/Makefile          \
                 src/ns/Makefile                   \
                 src/nsichneu/Makefile             \
                 src/picojpeg/Makefile             \
                 src/prime/Makefile                \
                 src/qrduino/Makefile              \
                 src/qsort/Makefile                \
                 src/qurt/Makefile                 \
                 src/recursion/Makefile            \
                 src/rijndael/Makefile             \
                 src/select/Makefile               \
                 src/sglib-arraybinsearch/Makefile \
                 src/sglib-arrayheapsort/Makefile  \
                 src/sglib-arrayquicksort/Makefile \
                 src/sglib-arraysort/Makefile      \
                 src/sglib-dllist/Makefile         \
                 src/sglib-hashtable/Makefile      \
                 src/sglib-listinsertsort/Makefile \
                 src/sglib-listsort/Makefile       \
                 src/sglib-queue/Makefile          \
                 src/sglib-rbtree/Makefile         \
                 src/slre/Makefile                 \
                 src/sqrt/Makefile                 \
                 src/st/Makefile                   \
                 src/statemate/Makefile            \
                 src/stb_perlin/Makefile           \
                 src/stringsearch1/Makefile        \
                 src/strstr/Makefile               \
                 src/tarai/Makefile                \
                 src/template/Makefile             \
                 src/trio/Makefile                 \
                 src/trio-snprintf/Makefile        \
                 src/trio-sscanf/Makefile          \
                 src/ud/Makefile                   \
                 src/whetstone/Makefile            \
                 src/wikisort/Makefile             \
		 support/Makefile                  \
		 testsuite/Makefile                \
		 testsuite/beebs.test/Makefile     \
		 testsuite/config/Makefile         \
		 testsuite/lib/Makefile])

# And spit it all out

AC_OUTPUT
