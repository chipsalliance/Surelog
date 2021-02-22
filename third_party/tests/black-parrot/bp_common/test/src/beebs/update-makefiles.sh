#!/bin/bash

# Script to update makefiles
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

# This is a convenience script to apply a snobol4 program to all the makefiles.

# Sort out arguments

if [ $# -ne 1 ]
then
    echo "Usage: $0 <snobol script>"
    exit 1
fi

mydir=$(dirname "$0")
rootdir=$(cd "${mydir}"; pwd)

# Sort out whether script is absolute or relative

case $1 in
    /*) script=$1 ;;
    *)  script=${rootdir}/$1
esac

cd ${rootdir}/src

for d in *
do
    if [ -d ${d} -a -f ${d}/Makefile.am ]
    then

	# Create the temporary directory unless it exists

	if ! [ -f ${d}/Makefile.am.tmp ]
	then
	    cp ${d}/Makefile.am ${d}/Makefile.am.tmp
	fi

	# Run the script

	snobol4 ${script} < ${d}/Makefile.am.tmp > ${d}/Makefile.am
    fi
done

echo "To remove temporaries: find src -name Makefile.am.tmp -exec rm {} \\;"
echo "To restore originals: find src -name Makefile.am.tmp -exec mv Makefile.am.tmp Makefile.am \\;"
