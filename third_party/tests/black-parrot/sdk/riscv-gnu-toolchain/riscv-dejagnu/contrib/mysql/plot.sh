#!/bin/bash

# plot.sh
#
# Copyright (C) 2016 Free Software Foundation, Inc.
#
# This file is part of DejaGnu.
#
# DejaGnu is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.

# This script executes a series of SQL calls to our testing database,
# and makes a data file for gnuplot.

if test "$#" -eq 0; then
    echo "Need to supply a graph name!"
    name="GCC"
else
    name=$1
fi

# These are required to access the database
user="USER"
passwd="PASSWD"
outfile="testrun.data"

# Check the environment for the database access information
if test x"${CBUILD_DBUSER}" != x; then
    user="${CBUILD_DBUSER}"
fi
if test x"${CBUILD_DBPASSWD}" != x; then
    passwd="${CBUILD_DBPASSWD}"
fi

# setup an array of colors, since the number of data files varies
declare -a colors=('green' 'red' 'cyan' 'blue' 'purple' 'brown' 'coral' 'yellow' 'black')

type="with lines"
type=

machines=$(mysql -u"$user" -p"$passwd" --local -e "SELECT DISTINCT(build_machine) FROM dejagnu.testruns" | sed -e 's/build_machine//'  | sed -e 's:\.::' | tr '\n' ' ')
echo "Build machines are: ${machines}"

tools=$(mysql -u"$user" -p"$passwd" --local -e "SELECT DISTINCT(tool) FROM dejagnu.testruns" | sed -e 's/tool//' | tr '\n' ' ')

# Only graph if there is a data file
#tools="`ls *.data | cut -d '.' -f 1`"
echo "Tools are: ${tools}"

datafiles="${machines}"
if test "$#" -gt 1; then
    case $2 in
	m*) datafiles="echo ${machines}"
	    echo "Separating graphs by build machine name"
	    ;;
	t*) datafiles="${tools}"
	    echo "Separating graphs by tool name"
	    ;;
	*)
	    datafiles="${machines}"
	    ;;
    esac
fi

outfile="gnuplot.cmd"
cindex=0
for j in ${datafiles}; do
    # for now we don't want aarch64 results in the chart as they distort the data
    # heavily.
    if test "$(echo "$j" | grep -c aarch64)" -gt 0; then
	continue
    fi
    if test -f "$j".data -a -s "$j".data; then
	if test ${cindex} -eq 0; then
	    echo "Creating gnuplot comand file: ${outfile}"
	    cat <<EOF >${outfile}
set boxwidth 0.9 relative 
set style data histograms 
set style histogram cluster 
set style fill solid 1.0 border lt -1
set autoscale x
set autoscale y
#set yrange [97:100]
set title "Precentage PASSes"
set ylabel "Precent PASS"
set format y "%g%%"
#set xlabel "Architecture"

# Rotate the X axis labels 90 degrees, so they all fit
set xtics border in scale 1,0.5 nomirror rotate by -90  offset character 0, 0, 0

# Out the key in out of the way
set key right top

set term png size 1900,1024
set output "testrun.png"

set xlabel "${name} Versions"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
#set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

EOF
#	    echo -n "plot \"$j.data\" using (((\$6+\$9)/\$5)/100):xtic(3) title \"$j\" lt rgb \"${colors[$cindex]}\" ${type}" >> ${outfile}
	    echo -n "plot \"$j.data\" using ((\$6/\$5) * 100):xtic(3) title \"$j\" lt rgb \"${colors[$cindex]}\" ${type}" >> ${outfile}
#	    cindex=`expr $cindex + 1`
#	    echo -n ", \"\" using (((\$7+\$8+\$10+\$11+\$12)/\$5) * 100):xtic(3) title \"FAILS\" lt rgb \"${colors[$cindex]}\" ${type}" >> ${outfile}
	else
#	    echo -n ", \"$j.data\" using ((\$6+\$9/\$5)/100):xtic(3) title \"$j\" lt rgb \"${colors[$cindex]}\" ${type}" >> ${outfile}
	    echo -n ", \"$j.data\" using ((\$6/\$5) * 100):xtic(3) title \"$j\" lt rgb \"${colors[$cindex]}\" ${type}" >> ${outfile}
	fi
	cindex=$((cindex + 1))
    fi
done

#for j in ${datafiles}; do
#    if test -f $j.data -a -s $j.data; then
	cat <<EOF >>${outfile}

set term x11 persist
replot

EOF
#    fi
#done


