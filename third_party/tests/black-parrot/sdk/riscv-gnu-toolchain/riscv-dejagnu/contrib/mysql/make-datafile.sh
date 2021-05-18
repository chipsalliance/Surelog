#!/bin/bash

# make-datafile.sh -- export data from MySQL testing database.
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

if test $# -eq 0; then
  echo "ERROR: no testrun numbers specified!"
  exit
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

# Create the output file
rm -f ${outfile}

# Add a header to make the file human readable
echo "# date tool version arch total PASS FAIL UNSUPPORTED UNTESTED UNRESOLVED XPASS XFAIL" > ${outfile}

machines=$(mysql -u"$user" -p"$passwd" --local -e "SELECT DISTINCT(build_machine) FROM dejagnu.testruns" | sed -e 's/build_machine//' | tr '\n' ' ')
echo "Build machines are: ${machines}"

tools="gcc g++ gfortran libstdc++ objc"
echo "Tools are: ${tools}"

for testrun in "$@"; do
  # Get the build info
  binfo=$(mysql -u"$user" -p"$passwd" --local -e "SELECT tool,arch,date,version,branch,build_machine FROM dejagnu.testruns WHERE testrun=${testrun}" | tail -1)
 
  # Get rid of the embedded newlines
  binfo=$(echo "$binfo" | tr -d '\n')

  # Split the query result into fields
  tool=$(echo "$binfo" | cut -d ' ' -f 1)
  arch=$(echo "$binfo" | cut -d ' ' -f 2)
  date=$(echo "$binfo" | cut -d ' ' -f 3)
  version=$(echo "$binfo" | cut -d ' ' -f 5)
  build_machine=$(echo "$binfo" | cut -d ' ' -f 7)
 
  # Get the test counts
#  total=`mysql -u"$user" -p${passwd} -e "SELECT count(*) FROM dejagnu.test WHERE result!=''" | tail -1`
  passes=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='PASS'" | tail -1)
  fails=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='FAIL'" | tail -1)
  xpasses=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='XPASS'" | tail -1)
  xfails=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='XFAIL'" | tail -1)
  untested=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='UNTESTED'" | tail -1)
  unsupported=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='UNSUPPORTED'" | tail -1)
  unresolved=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='UNRESOLVED'" | tail -1)
  # total=$(mysql -u"$user" -p"$passwd" -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result!=''" | tail -1)
  # passes=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='PASS'" | tail -1)
  # fails=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='FAIL'" | tail -1)
  # xpasses=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='XPASS'" | tail -1)
  # xfails=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='XFAIL'" | tail -1)
  # untested=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='UNTESTED'" | tail -1)
  # unsupported=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='UNSUPPORTED'" | tail -1)
  # unresolved=$(mysql -u"$user" -p"$passwd" --local -e "SELECT count(*) FROM dejagnu.test WHERE testrun=${testrun} AND result='UNRESOLVED'" | tail -1)

  # Write the data line
  all_passes=$((passes+ xfails))
  all_failures=$((fails + xpasses + untested + unresolved + unsupported))
  all_tests=$((all_passes + all_failures))

  echo "${date} ${tool} ${version} ${arch} ${all_tests} ${passes} ${fails} ${xpasses} ${xfails} ${untested} ${unresolved} ${unsupported} ${build_machine}" >> ${outfile}
done

# Extract the list of architectures supported for these results
arches=$(grep -v '#' testrun.data | cut -d ' ' -f 13 | sort | uniq | tr '\n' ' ')
echo "Architectures for this set of results: ${arches}"

# Make a separate data file for each architecture so gnuplot can keep them organized
for i in ${arches}; do
    if test "$i" = '.'; then
	continue
    fi
    # filter out bogus test results to avoid weird spikes in the data
    if test "$passes" -eq 0 -a "$fails" -eq 0; then
	continue
    fi
    rm -f "$i".data
    grep "$i" testrun.data | sort  -V -k 3 | uniq -u > "$i".data
done

rm testrun.data

files=$(find . -maxdepth 1 -name '*.data' | tr '\n' ' ')
# Get all the versions in the files, we'll pad rows so all the rows match
versions=$(cut -d ' ' -f 3 $files | sort -V | uniq | tr '\n' ' ')

for i in ${files}; do
   for j in ${versions}; do
	cnt=$(grep -c "$j" "$i")
	if test "$cnt" -eq 0; then
	    echo "Adding $j to $i"
	    machine=$(echo "$i" | cut -d '.' -f 1)
	    echo "${date} ${tool} $j ${arch} 0 0 0 0 0 0 0 0 $machine" >> "$i"
	fi
   done
done

# Re-sort based on the versions we just added as padding so the rows line up
for j in ${files}; do
    mv "$j" tmp.data
    sort  -V -k 3 < tmp.data > "$j"
    rm tmp.data
done
