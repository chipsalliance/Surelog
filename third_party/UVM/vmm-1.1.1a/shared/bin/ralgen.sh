#!/bin/sh -h
# -*- sh -*-
# -*- ksh -*-
#
#	Shell file to invoke an OS-specific binary
#

## 
## -------------------------------------------------------------
##    Copyright 2004-2008 Synopsys, Inc.
##    All Rights Reserved Worldwide
## 
##    Licensed under the Apache License, Version 2.0 (the
##    "License"); you may not use this file except in
##    compliance with the License.  You may obtain a copy of
##    the License at
## 
##        http://www.apache.org/licenses/LICENSE-2.0
## 
##    Unless required by applicable law or agreed to in
##    writing, software distributed under the License is
##    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##    CONDITIONS OF ANY KIND, either express or implied.  See
##    the License for the specific language governing
##    permissions and limitations under the License.
## -------------------------------------------------------------
## 

ARCH=`/bin/uname` 2>&1
RNAME=`/bin/uname -r`;
MNAME=`/bin/uname -m`;


Unsup () {
   echo "Unsupported achitecture \"$ARCH\".";
   echo "Please visit http://synopsysoc.org to use the web-based version of this tool.";
   exit 1;
}


case $ARCH in
   *SunOS)
      case $RNAME in
	5.[89]*|5.10)
	    ARCH=sunos5;
            ;;
         *)
            Unsup;
            ;;
      esac
      ;;

   HP-UX)
      case $RNAME in
        B.11.*)
	    ARCH=hp32;
            ;;
        *)
            Unsup;
            ;;
       esac
       ;;

   Linux)
      if [ -f /etc/redhat-release ]; then
	 ARCH="linux"
      elif [ -f /etc/SuSE-release ]; then
         ARCH="suse32"
      else
         Unsup
      fi
      ;;

   AIX)
      VER=`/bin/uname -v`;
      case ${VER}.${RNAME} in
        5.1|4.3|5.3)
            ARCH=rs6000;
            ;;
        *)
            Unsup;
            ;;
      esac
      ;;

   *) # not a recognized response.
      Unsup;
      ;;
esac

DIR=`echo $0 | /bin/sed -e 's#[^/]*$#'$ARCH'#' `;
BIN=`/bin/basename $0`;

if [ -d $DIR ]; then
   if [ -x $DIR/$BIN ]; then
      argv=`echo $* | sed 's/[ \t]\+-ext_ud[ \t]\+/ -e /g' \
                    | sed 's/[ \t]\+-gen_c[ \t]\+/ -g /g' \
                    | sed 's/[ \t]\+-top_path[ \t]\+/ -p /g' \
                    | sed 's/[ \t]\+-top_domain[ \t]\+/ -d /g'`
      $DIR/$BIN $argv
   else
      ARCH="$ARCH\" for command \"$BIN";
      Unsup;
   fi
else
   Unsup;
fi

