#!/bin/sh

#*********************************************************************************
# Copyright (c) 2021 Wavious LLC
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
#
#*********************************************************************************

###################################
# Tool Related
###################################

#DUMP="/simulation2/${USER}/sims/"
DUMP="./"
LOCAL="FALSE"

ROOTDIR="../.."
export RTL="$ROOTDIR/rtl"
export sw="$ROOTDIR/sw"
VERIF="$ROOTDIR/verif"

#----Agent PKG
APB_PKG="${VERIF}/sv/agents/APB/wav_APB_pkg.sv"

#---REG TEST PKG
WDDR_PKG="${VERIF}/sv/wddr_pkg.sv"
WDDR_TEST_PKG="${VERIF}/tests/wddr_test_pkg.sv"

#---Denali
DENALI="/cad/tools/cadence/VIPCAT11.30.070/tools.lnx86/denali_64bit"

###################################
# Paths/Env variables
###################################
TESTCASE="NONE"
#SEED="1"
SEED="Z"
PROBE=""
CLN_BUILD="FALSE"
NO_BUILD="FALSE"
NO_RUN="FALSE"
UVM_DEBUG="+UVM_VERBOSITY=UVM_MEDIUM"

GUI_ARG="-c"
BUILDCMN="FALSE"
COV="FALSE"
COVERAGE=""
LOGS_DIR=${VERIF}/run

EXTRA_CMD=""

WORK_LIB_XRUN=""
PROFILE_CMD=""

SAVE_CMD_XRUN="-access rwc -input input.tcl"
NO_BUILD_XRUN=""
SIMULATOR="$1"
SW=""
MM=""
DFIMC=""
NOSB=""
LP4="+WPHY_ANA_ASSERT_EN=0"
LOG=""
WAVE_START="350"
WAVE_NAME="waves_wddr"
WAVE_DEPTH="all"
UVM_TO="5000000"

###################################
# Help
###################################
usage_txt=$'\nUsage:simulate.sh [options]

------- Debug and Help and Etc -------
-v            Enable coverage generation.
-h            Print help/usage

------- Required args -------
-e            Extra Arguments passed

------- Build control -------
-c            Clean the work area, do not run sim
-nb           Do not build model

------- Run control -------
-nr           Do not run the simulation
-timeout      time in ns for timeout

------- Dump control -------
-nosave       No dump
-wavst        waves dump start time in "us"
-wavnm        waves dump name
-wavdp        waves dump depth in hierarchy from tb_top

------- Logging -------
-log         log name
-local       save log/shm in local dir

------- Defines -------
-dfimc         Dfimc VIP added to environment
-lp4           Lpddr4 Memory Model added to environment
-mm            Wavious Memory Model driver added to environment

'
####################################
# RTL files
###################################

DUMP_SPICE_STIM=""
IS_GLS="+define+UNIT_DELAY +notimingcheck "
RTL_FILES="+define+ARM_UD_MODEL +define+ARM_UD_DP=#0 \
    -f ${ROOTDIR}/verif/flist/ddr_phy.f              \
    -f ${ROOTDIR}/verif/flist/ddr_phy.behav.f"

###################################
# Switches
###################################
while test $# -gt 0
do
    case "$1" in
        -t)
            echo "$0: ---> Setting testcase to '$2'"
            TESTCASE="$2"
            LOG="$2.log"
            shift
            ;;
        -x)
            echo "$0: ---> Setting seed to $2"
            SEED="$2"
            shift
            ;;
        -nosave)
            echo "$0: ---> No probing"
            SAVE_CMD_XRUN=""
            ;;
        -local)
            echo "$0: ---> Dumping log/shm in local directory"
            DUMP=""
            LOCAL="TRUE"
            ;;
        -log)
            echo "$0: ---> Saving log to $2.log"
            LOG="$2.log"
            shift
            ;;
        -wavst)
            echo "$0: ---> Waves: dump start from $2 us"
            WAVE_START="$2"
            shift
            ;;
        -wavnm)
            echo "$0: ---> Waves: dump name $2"
            WAVE_NAME="$2"
            shift
            ;;
        -wavdp)
            echo "$0: ---> Waves: dump depth $2"
            WAVE_DEPTH="$2"
            shift
            ;;
        -timeout)
            echo "$0: ---> UVM Timeout : $2 ns"
            UVM_TO="$2"
            shift
            ;;
        -e)
            echo "$0: ---> Setting extra commands $2"
            EXTRA_CMD="$2"
            shift
            ;;
        -c)
            echo "$0: ---> Clean build"
            CLN_BUILD="TRUE"
            ;;
        -nb)
            echo "$0: ---> not building"
            NO_BUILD="TRUE"
            DUMP=""
            ;;
        -nr)
            echo "$0: ---> not running"
            NO_RUN="TRUE"
            ;;
        -ud)
            UVM_DEBUG="+UVM_VERBOSITY=UVM_DEBUG +UVM_PHASE_TRACE +UVM_OBJECTION_TRACE +UVM_CONFIG_DB_TRACE"
            echo "$0: ---> Add $UVM_DEBUG to vsim."
            ;;
        -uh)
            UVM_DEBUG="+UVM_VERBOSITY=UVM_HIGH +UVM_CONFIG_DB_TRACE"
            echo "$0: ---> Add $UVM_DEBUG to vsim."
            ;;
        -sw)
            echo "$0: ---> SW Testing '$2'"
            SW="+define+$2"
            shift
            ;;
        -mm)
            echo "$0: ---> MM VIP added to verif env"
            MM="+define+MM +define+NOSB"
            ;;
        -nosb)
            echo "$0: ---> DFIMC VIP No SB"
            NOSB="+define+NOSB"
            ;;
        -dfimc)
            echo "$0: ---> DFIMC VIP added to verif env"
            DFIMC="+define+DFIMC"
            ;;
        -lp4)
            echo "$0: ---> LPDDR4 VIP added to verif env"
            LP4="+define+LPDDR4"
            ;;
        -v)
            echo "$0: ---> Enabling coverage collection"
            COV="TRUE"
            ;;
        -h)
            echo "$0: $usage_txt"
            exit 0
            ;;
        -worklib)
            WORK_LIB_XRUN="-r work_wddr -xmlibdirname $2"
            shift
            ;;
        -s)
            echo "$0: ---> blah"
            SIMULATOR="$2"
            shift
            ;;
        -phy_spice)
            echo "Dumping DQ Spice VCD"
            DUMP_SPICE_STIM="+define+DUMP_SPICE_VCD +define+DDR_SPICE_VCD_DDR_1X32"
            ;;
        -dq_spice)
            echo "Dumping DQ Spice VCD"
            DUMP_SPICE_STIM="+define+DUMP_SPICE_VCD +define+DDR_SPICE_VCD_DDR_DQ +define+DDR_SPICE_PRINT_DDR_DQ"
            ;;
        -ca_spice)
            echo "Dumping CA Spice VCD"
            DUMP_SPICE_STIM="+define+DUMP_SPICE_VCD +define+DDR_SPICE_VCD_DDR_CA +define+DDR_SPICE_PRINT_DDR_CA"
            ;;
    esac
    shift
done

if [ "$CLN_BUILD" == "TRUE" ]
then
    printf "\n\n$0: ---> Cleaning...\n"
    $SIMULATOR -clean
    exit 0
fi

#On by default
DFE_FAST_SIM="+define+WCL_DFE_FAST_SIM"
QWAVE_NAME="wav_${TB_BASE_NAME}_wave.db"

PROFILE_CMD=""

###########################################
# RUN
###########################################

if [ "$NO_BUILD" == "TRUE" -a "$NO_RUN" == "TRUE" ]
then
    printf "\n\n$0: **** HELP ****  Both build and run were turned off.\n\n"
    echo "$usage_txt"
    exit 0
fi

if [ "$SEED" == "Z" ]
then
    SEED=`perl -e 'printf "%d\n", rand(2**31-1);'`
fi

if [ "$COV" == "TRUE" ]
then
    #COVERAGE=" -covoverwrite -coverage all -covdut wmu_wcl_umb_top -covtest $TESTCASE$SEED "
    COVERAGE="-coverage all -covtest $TESTCASE$SEED -covdut ddr_phy_1x32"
fi

###########################
# XRUN
###########################

function xrun_cmd {

$SIMULATOR $*                                                                     \
    -parse -lowmem  -verbose \
    +incdir+../../../../UVM/uvm-1.2/src \
    ../../../../UVM/uvm-1.2/src/uvm_pkg.sv \
    ../../../../UVM/uvm-1.2/src/uvm_macros.svh \
    $APB_PKG                                                                      \
    $WDDR_PKG                                                                     \
    ${RTL}/wddr/ddr_global_pkg.sv                                                 \
    ${RTL}/mcu_ibex/wav_mcu_pkg.sv                                                \
    -stop_on_build_error -sv -64bit -disable_sem2009 -licqueue                    \
    -top wddr_tb_top  +define+no_warning -warn_multiple_driver                    \
    +define+no_warning $IS_GLS $DUMP_SPICE_STIM                                 \
    -uvm -ALLOWREDEFINITION +UVM_TIMEOUT=$UVM_TO                                  \
    +define+NOTBV=true +nowarn+FUNTSK +nowarn+UEXPSC +nowarn+ENUMERR              \
    +UVM_VERBOSITY=UVM_FULL +define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR              \
    $SW $MM $NOSB $DFIMC $LP4 +MVP_FORCE_PLL $COVERAGE                            \
    $EXTRA_CMD                                                                    \
    +define+LPK                                                                   \
    +define+DENALI_SV_NC +define+DENALI_UVM                   \
    -timescale=1ns/1ps                                    \
    +incdir+${VERIF}                                                              \
    +incdir+${VERIF}/run                                                          \
    +incdir+${VERIF}/tb_top                                                       \
    +incdir+${VERIF}/tests                                                        \
    +incdir+${VERIF}/sv                                                           \
    +incdir+${VERIF}/sv/agents                                                    \
    +incdir+${VERIF}/sv/register                                                  \
    +incdir+${VERIF}/sv/sequences                                                 \
    +incdir+${VERIF}/sv/sequences/dt                                              \
    +incdir+${VERIF}/sv/sequences/regs                                            \
                                                           \
      $WORK_LIB_XRUN                                   \
    $RTL_FILES                                                                    \
    ${VERIF}/sv/agents/mm/wav_mm.sv                                               \
    ${VERIF}/sv/agents/APB/apb_to_ahb.v                                           \
    ${VERIF}/tb_top/wddr_tb_top.sv
}

###########################

if [ "$NO_BUILD" == "FALSE" ]
then
    printf "\n\n$0: ---> Building...\n"
    xrun_cmd -elaborate -l $DUMP./logs/xelab_wddr.log

    BLD_ERRS=`grep ": \*E" $DUMP./logs/xelab_wddr.log`

    if [ "$BLD_ERRS" != "" ]; then
        printf "\n\n"
        echo $BLD_ERRS
        printf "\n\n$0: ---> Build FAILED : Exiting.  Advise that you look at $DUMP./logs/xelab_wddr.log for errors.\n\n"
        exit
    else
        printf "\n\n$0: ---> Build PASSED.\n\n"
    fi
fi

if [ "$NO_RUN" == "FALSE" ]
then
    printf "\n\n$0: ---> Running...\n"
    xrun_cmd -l $DUMP./logs/xrun_$LOG +UVM_TESTNAME=$TESTCASE
    printf "\n\n$0: ---> Sim is done.\n"
    echo "======================================="
    egrep "** Error|UVM_WARNING :|UVM_ERROR|UVM_FATAL|I3C TOP NOTE|CAN TEST|I3C TEST|SWIRE TEST|TEST CASE STATUS|\*E" $DUMP./logs/xrun$SEED.log
    echo "======================================="

fi
