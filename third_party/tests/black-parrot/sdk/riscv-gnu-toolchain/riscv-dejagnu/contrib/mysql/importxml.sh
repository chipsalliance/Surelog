#!/bin/bash

# importxml.sh -- import a .sum file into MySQL.
#
# Copyright (C) 2016 Free Software Foundation, Inc.
#
# This file is part of DejaGnu.
#
# DejaGnu is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.

# This script takes a compressed or uncompressed sum file from a
# DejaGnu test run. It then extracts the relevant information about
# the build and writes that to the dejagnu.testruns control
# table. After that it converts the sum file to XML, and imports it
# into an SQL database, in this case MySQL.

if test x"$1" = x; then
  infile="/tmp/testrun.xml"
  outfile="/tmp/testrun.xml"
else
  infile=$1
  outfile=${1//\.sum.*/.xml}
fi

if test ! -e "$infile"; then
  echo "ERROR: no input file specified!"
  exit
fi

# These are required to access the database
user="USER"
passwd="PASSWD"

# Check the environment for the database access information
if test x"${CBUILD_DBUSER}" != x; then
    user="${CBUILD_DBUSER}"
fi
if test x"${CBUILD_DBPASSWD}" != x; then
    passwd="${CBUILD_DBPASSWD}"
fi

total=$(mysql -u"$user" -p"$passwd" -e "SELECT testrun from testruns ORDER BY testrun DESC LIMIT 1" dejagnu | tail -1)
total=$((total + 1))

type=$(file "$infile")

build_machine=$(dirname "$infile" | cut -d '-' -f 8)

# If compressed, uncompress it
count=$(echo "$type" | grep -c "XZ compressed data")
if test "$count" -gt 0; then
  catprog="xzcat"
  uncomp="xz -d"
else
  count=$(echo "$type" | grep -c "XZ compressed data")
  if test "$count" -gt 0; then
    catprog="gzcat"
    uncomp="gnzip"
  else
    catprog="cat"
    uncomp=""
  fi
fi

# extract the build info from the sum file.
# This goes in the dejagnu.testruns table
tool=$(${catprog} "$infile" | grep "tests ===" | cut -d ' ' -f 2)
target=$(${catprog} "$infile" | head -20 | grep "configuration is " | cut -d ' ' -f 4)
version=$(${catprog} "$infile" | head -20 | grep "Running /" | cut -d '/' -f 7 | sed -e 's:^[a-z-]*-::' -e 's:_:.:' -e 's:-branch::' | tail -1)
date=$(${catprog} "$infile" | head -1 | sed -e 's:Test Run By [a-zA-Z]* on ::')
date=$(date -d "${date}" "+%Y-%m-%d %H:%M:%S")

echo "Adding to DB: $target, $version, $date, $tool"

# Add an entry in the testrun table for this sum file

echo "Adding the test run into the testruns control table."
mysql -u"$user" -p"$passwd" --local -e "INSERT INTO dejagnu.testruns VALUES('${tool}','${date}','${version}','svn','${total}','${target}','${build_machine}');" dejagnu

# Make the temp file copy
if test x"${uncomp}" != x; then
  rm -f tmp.sum
  ${catprog} "$infile" > tmp.sum
fi

# convert the sum file to an xml file so it can be imported
echo "Converting the sum file to XML for importing into MySQL."
bash "$(dirname "$0")/sum2xml.sh" "$infile"

# import the the xml file into MySQL. Note that we add the testrun index which is
# retreived from the database earlier in this script.
echo "Adding the sum file into the testruns control file."
mysql -u"$user" -p"$passwd" --local -e "LOAD XML LOCAL INFILE '${outfile}' INTO TABLE dejagnu.test ROWS IDENTIFIED BY '<test>' SET testrun = '${total}';" dejagnu
