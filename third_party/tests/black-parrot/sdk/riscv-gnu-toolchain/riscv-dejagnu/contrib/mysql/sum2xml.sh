#!/bin/bash

# sum2xml.sh -- convert a .sum file into XML.
#
# Copyright (C) 2016 Free Software Foundation, Inc.
#
# This file is part of DejaGnu.
#
# DejaGnu is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.


if test x"$1" = x; then
  outfile="/tmp/testrun.xml"
  infile="/tmp/testrun.sum"
else
  outfile=${1//\.sum.*/.xml}
  infile=$1
fi

# Where to put the output file
if test x"$2" = x; then
  outfile="$outfile"
else
  outfile="/tmp/$outfile"
fi

if test ! -e "$infile"; then
  echo "ERROR: no input file specified!"
  exit
fi

# If compressed, uncompress it
type=$(file "$infile")
count=$(echo "$type" | grep -c "XZ compressed data")
if test "$count" -gt 0; then
  decomp="xz -d"
  comp="xz"
else
  count=$(echo "$type" | grep -c "XZ compressed data")
  if test "$count" -gt 0; then
    decomp="gzip"
    comp="gunzip"
  fi
fi

#
cat <<EOF > "$outfile"
<?xml version="1.0"?>
<!DOCTYPE testsuite [
<!-- testsuite.dtd -->
<!ELEMENT testsuite (test | summary)+>
<!ELEMENT test (input, output, result, name, prms_id )>
  <!ELEMENT input              (#PCDATA)>
  <!ELEMENT output             (#PCDATA)>
  <!ELEMENT result             (#PCDATA)>
  <!ELEMENT name               (#PCDATA)>
  <!ELEMENT prms_id            (#PCDATA)>
  <!ELEMENT summary     (result, description, total)>
  <!ELEMENT description        (#PCDATA)>
  <!ELEMENT total              (#PCDATA)>
]>
EOF

# Write the opening tag for the test results
echo "<testsuite>" >> "$outfile"

${decomp} "$infile"
infile=$(echo "$infile" | sed -e 's:\.xz::' -e 's:\.gz::')

while read line
do
  # ignore blank lines
    if test x"${line}" = x; then
	continue
    fi
  # # ignore the test case name
  # if test `echo ${line} | grep -c Running` -gt 0; then
  #   continue
  # fi
  # ignore the summary, we get this via SQL later
    if test "$(echo "$line" | grep -c Summary)" -gt 0; then
	break
    fi
    valid=$(echo "$line" | egrep -c 'PASS|FAIL|UNTESTED|UNSUPPORTED|UNRESOLVED')
    if test "$valid" -eq 0; then
	continue
    fi
    echo -n "."
    { echo "<test>"; echo "  <input></input>"; echo "  <output></output>"; } >> "$outfile"
    result=$(echo "$line" | sed -e 's/: .*$//')
    echo "  <result>${result}</result>" >> "$outfile"
    name=${line/^[A-Z]*: /}
    { echo "  <name>${name}</name>"; echo "  <prms_id></prms_id>"; echo "</test>"; } >> "$outfile"
done < "$infile"

# Write the closing tag for the test results
echo "</testsuite>" >> "$outfile"

# compress the file again
${comp} "$infile"

