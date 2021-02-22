#!/bin/bash

# Script to generate some of the configuration for BEEBS
#
# Copyright (C) 2018 Embecosm Limited
#
# Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>
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
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# SPDX-License-Identifier: GPL-3.0-or-later

# This is a convenience script to generate repeat text in various
# files. Should never really need to be used.

bmlist=$(cd src && find . -maxdepth 1 -type d -not -name ".*" | sed 's/.\///' | sort)

for bm in ${bmlist}
do
    [ -f src/$bm/Makefile.am ] || continue

    if ! grep --silent "bin_PROGRAMS" src/$bm/Makefile.am
    then
        continue
    fi

    bm_var=$(echo $bm | tr "-" "_")
    bm_uc=$(echo $bm_var | tr "[:lower:]" "[:upper:]")
    echo "AC_ARG_ENABLE([benchmark-${bm}],"
    echo "  [AS_HELP_STRING([--enable-benchmark-${bm}],"
    echo "     [Enable benchmark ${bm}])],"
    echo "  [case \"\${enableval}\" in"
    echo "      yes) benchmark_${bm_var}=true ;;"
    echo "      no)  benchmark_${bm_var}=false ;;"
    echo "      *)   AC_MSG_ERROR([bad value \${enableval} for --enable-benchmark-${bm}]) ;;"
    echo "   esac],"
    echo "  [])"
    echo "AM_CONDITIONAL([ENABLED_BENCHMARK_${bm_uc}],"
    echo "               [test x\$benchmark_${bm_var} = xtrue])"
    echo
done
