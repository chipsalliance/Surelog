#!/bin/bash
 #########################################################################################
 # (C) Copyright 2015 AMIQ Consulting
 #
 # Licensed under the Apache License, Version 2.0 (the "License");
 # you may not use this file except in compliance with the License.
 # You may obtain a copy of the License at
 #
 # http://www.apache.org/licenses/LICENSE-2.0
 #
 # Unless required by applicable law or agreed to in writing, software
 # distributed under the License is distributed on an "AS IS" BASIS,
 # WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 # See the License for the specific language governing permissions and
 # limitations under the License.
 #
 # NAME:        run_svaunit.sh
 # PROJECT:     svaunit
 # Description: Script example to compile and run simulation with different simulators
 # Usage:  run_svaunit.sh [-t[est] <name>]                                                          --> specify a particular test to run (default: ${default_test})"
 #                        [-s[eed] <value>]                                                         --> specify a particular seed for the simulation (default: ${default_seed})"
 #                        [-i]                                                                      --> run in interactive mode"
 #                        [-tool          { ius | questa | vcs} ]                                   --> specify what simulator to use (default: ${default_tool})"
 #                        [-in_reg]                                                                 --> specify if the current invocation is for running a test in regression"
 #                        [-reg]                                                                    --> starts a regression"
 #                        [-uvm           { uvm1.1 | uvm1.2} ]                                      --> specify the UVM version(default: ${default_compile_option})""
 #                        [-bit[32|64]                                                              --> specify what architecture to use: 32 or 64 bits (default: ${default_arch_bits} bits)"
 #                        [-c[ompile] {yes|no|only}]                                                --> specify if to compile the SVAUnit (default: ${default_compile_option})"
 #                        [-verbosity {UVM_NONE|UVM_LOW|UVM_MEDIUM|UVM_HIGH|UVM_FULL|UVM_DEBUG }]   --> specify the verbosity of a message (default: ${default_uvm_verbosity})"
 #                        [-f[ile] <name> ]                                                         --> specify the file with an example  (default: ${FILE})"
 #
 #         run_svaunit.sh  -h[elp]                                                                  --> print this message"
 # Example of using : ./run_svaunit.sh -tool ius -uvm uvm1.2 -f examples/ex_basic/files.f -top top -test amiq_svaunit_ex_basic_test -i -c yes  
 # Example of using : ./run_svaunit.sh -reg
 #########################################################################################

##########################################################################################
#  Setting the variables
##########################################################################################
# Setting the SCRIPT_DIR variable used to find out where the script is stored
SCRIPT_DIR=`dirname $0`
SCRIPT_DIR=`cd ${SCRIPT_DIR}&& pwd`

# Setting the PROJ_HOME variable used to find out where the current project is stored
export PROJ_HOME=`cd ${SCRIPT_DIR}/../ && pwd`

# Set variables with default value
default_run_mode="batch"
default_tool=ius
default_seed=1;
default_test=apb_ts
default_arch_bits=64
default_compile_option=yes
default_in_regression=no
default_uvm_version="uvm1.1"
default_top_name="apb_top"
default_uvm_verbosity=UVM_MEDIUM
default_regression_file=apb_unit_tests.vsif
default_file_name="examples/apb_tests/apb_files.f"


run_mode=${default_run_mode}
tool=${default_tool}
seed=${default_seed}
test=${default_test}
ARCH_BITS=${default_arch_bits}
compile_option=${default_compile_option}
in_regression=${default_in_regression}
uvm_version=${default_uvm_version}
top_name=${default_top_name}
uvm_verbosity=${default_uvm_verbosity}
regression_file=${default_regression_file}
file_name=${default_file_name}


export TOP_MODULE_NAME=${top_name}
export TOP_FILE_NAME=${TOP_MODULE_NAME}.sv

##########################################################################################
#  Methods
##########################################################################################

help() {
    echo "Usage:  run_svaunit.sh [-t[est] <name>]                                                          --> specify a particular test to run (default: ${default_test})"
    echo "                       [-s[eed] <value>]                                                         --> specify a particular seed for the simulation (default: ${default_seed})"
    echo "                       [-i]                                                                      --> run in interactive mode"
    echo "                       [-tool   { ius | questa | vcs} ]                                          --> specify what simulator to use (default: ${default_tool})"
    echo "                       [-reg]                                                                    --> starts a regression"
    echo "                       [-in_reg]                                                                 --> specify if the current invocation is for running a test in regression"
    echo "                       [-uvm           { uvm1.1 | uvm1.2} ]                                      --> specify the UVM version(default: ${default_compile_option})"
    echo "                       [-bit[32|64]                                                              --> specify what architecture to use: 32 or 64 bits (default: ${default_arch_bits} bits)"
    echo "                       [-c[ompile] {yes|no|only}]                                                --> specify if to compile the SVAUnit (default: ${default_compile_option})"
    echo "                       [-verbosity {UVM_NONE|UVM_LOW|UVM_MEDIUM|UVM_HIGH|UVM_FULL|UVM_DEBUG }]   --> specify the verbosity of a message (default: ${default_uvm_verbosity})"
    echo "                       [-f[ile] <name> ]                                                         --> specify the file with an example  (default: ${default_file_name})"
    echo ""
    echo "        run_svaunit.sh  -h[elp]                                                                  --> print this message"
    echo "Example: ./run_svaunit.sh -tool ius -uvm uvm1.2 -f examples/ex_basic/files.f -top top -test amiq_svaunit_ex_basic_test -i -c yes"
}

compile_with_ius() {
    if [ "$uvm_version" = "uvm1.1" ]; then
        COMPILE_EXTRA_OPTIONS=" ${COMPILE_EXTRA_OPTIONS} +define+UVM_DEPRECATED_REPORTING"
    else
        COMPILE_EXTRA_OPTIONS=" ${COMPILE_EXTRA_OPTIONS} -uvmhome CDNS-1.2"
    fi
    
    echo "Compilling with EXTRA_OPTIONS: ${EXTRA_OPTIONS} "
    
    rm -rf cov_work INCA_libs irun.key irun.log
    irun ${COMPILE_EXTRA_OPTIONS} -f ${PROJ_HOME}/sim/options_ius.f -c 
}

compile_with_questa() {
    if [ "$uvm_version" = "uvm1.1" ]; then
        COMPILE_EXTRA_OPTIONS=" ${COMPILE_EXTRA_OPTIONS} +define+UVM_DEPRECATED_REPORTING"
    else
        export UVM_HOME=${UVM_HOME12}
        COMPILE_EXTRA_OPTIONS=" ${COMPILE_EXTRA_OPTIONS} +nowarnTSCALE+incdir+${UVM_HOME}/src ${UVM_HOME}/src/uvm_pkg.sv "
    fi
    
    echo "Compilling with EXTRA_OPTIONS: ${EXTRA_OPTIONS} "
    
    rm -rf work
    vlib work
    vlog ${COMPILE_EXTRA_OPTIONS} -f ${PROJ_HOME}/sim/options_questa.f 
}

compile_with_vcs() {
    echo "Currently, for VCS, compilation and test run are done in one command..."
}

compile() {
     case ${tool} in
        ius)
            echo "Selected tool: IUS..."
            compile_with_ius;
        ;;
        questa)
            echo "Selected tool: Questa..."
            compile_with_questa;
        ;;
        vcs)
            echo "Selected tool: VCS..."
            compile_with_vcs;
        ;;
        *)
            echo "Illegal option for tool: $tool"
            exit 1;
        ;;
    esac
}


# Compile and run with IUS
run_with_ius_test() {
    EXTRA_OPTIONS=" ${EXTRA_OPTIONS} "
    
    if [ "$run_mode" = "interactive" ]; then
        rm -rf ncsim_cmds.tcl
        touch ncsim_cmds.tcl

            echo "database -open waves -into waves.shm -default"                                              >> ncsim_cmds.tcl
            echo "probe -create ${top_name}  -depth all -tasks -functions -uvm -packed 4k -unpacked 16k -all -dynamic" >> ncsim_cmds.tcl
            echo "simvision input  ${PROJ_HOME}/sim/irun_variables.tcl"                                       >> ncsim_cmds.tcl

        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -gui -input ncsim_cmds.tcl -input ${PROJ_HOME}/sim/irun_variables.tcl"
    else
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -input  ${PROJ_HOME}/sim/irun_variables.tcl -run -exit "
    fi
    
    if [ "$in_regression" = "no" ]; then
        LIB_LOCATION=INCA_libs
    else
        LIB_LOCATION=${BRUN_CHAIN_DIR}/INCA_libs
    fi

    if [ "$compile_option" = "no" ]; then
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -R -nclibdirname ${LIB_LOCATION} "
    fi
    
    if [ "$uvm_version" = "uvm1.1" ]; then
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} +define+UVM_DEPRECATED_REPORTING"
    else
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -uvmhome CDNS-1.2"
    fi

    echo "Running with EXTRA_OPTIONS: ${EXTRA_OPTIONS} "

    irun -f ${PROJ_HOME}/sim/options_ius.f -svseed ${seed} +UVM_TESTNAME=${test}  ${EXTRA_OPTIONS} +UVM_NO_RELNOTES +UVM_VERBOSITY=${uvm_verbosity} 
}

# Compile and run with QUESTA
run_with_questa_test() {
    EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -assertdebug -assertcover -sva"
    if [ "$run_mode" = "interactive" ]; then
        rm -rf vsim_cmds.do
        touch vsim_cmds.do
    
        echo "add wave -position insertpoint sim:/${top_name}/*"     >> vsim_cmds.do
    
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS}  -do vsim_cmds.do -i "
    else
        rm -rf vsim_cmds.do
        touch vsim_cmds.do
    
        echo "coverage save -onexit ${PWD}/${test}.ucdb;" >> vsim_cmds.do
        echo "run -all;"                                  >> vsim_cmds.do
        echo "exit;"                                      >> vsim_cmds.do
    
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS}  -do vsim_cmds.do -c "
    fi
    
    if [ "$in_regression" = "no" ]; then
        LIB_LOCATION=work
    else
        LIB_LOCATION=work
    fi
    EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -lib ${LIB_LOCATION} "
    
    if [ "$uvm_version" = "uvm1.1" ]; then
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} +define+UVM_DEPRECATED_REPORTING"
    else
        export UVM_HOME=${UVM_HOME12}
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -sv_lib ${UVM_HOME}/lib/uvm_dpi64 "
    fi
    
    echo "Running with EXTRA_OPTIONS: ${EXTRA_OPTIONS}"
    
    vsim -${ARCH_BITS} -novopt ${top_name} -sv_seed ${seed} +UVM_TESTNAME=${test} +UVM_NO_RELNOTES +UVM_VERBOSITY=${uvm_verbosity} +nowarnTSCALE ${EXTRA_OPTIONS} 
}

# Compile and run with VCS
run_with_vcs_test() {

    if [ "$run_mode" = "interactive" ]; then
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -R -gui "
    else
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -R "
    fi

    if [ ${ARCH_BITS} == 64 ]; then
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} -full64 "
    fi
    
    if [ "$uvm_version" = "uvm1.1" ]; then
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} +define+UVM_DEPRECATED_REPORTING "
    else
        export VCS_UVM_HOME=${UVM_HOME12}/src
        EXTRA_OPTIONS=" ${EXTRA_OPTIONS} "
    fi
    
    echo "Running with EXTRA_OPTIONS: ${EXTRA_OPTIONS}"
    
    rm -rf csrc simv simv.daidir ucli.key vc_hdrs.h
    vcs -ntb_opts uvm  -f ${PROJ_HOME}/sim/options_vcs.f +ntb_random_seed=${seed} +UVM_TESTNAME=${test} +UVM_NO_RELNOTES +UVM_VERBOSITY=${uvm_verbosity} ${EXTRA_OPTIONS}
}

# Start regression
start_vmanager() {
      vmanager -pre " setup; compute vm_manager.start_session(\"${PROJ_HOME}/examples/apb_tests/vm/$regression_file\", \"\") "
      exit 1
}

##########################################################################################
#  Extract options
##########################################################################################
while [ $# -gt 0 ]; do
   case `echo $1 | tr "[A-Z]" "[a-z]"` in
      -h|-help)
                help
                exit 0
                ;;
      -c|-compile)
                compile_option=$2
                ;;
      -tool)
                tool=$2
                ;;
      -t|-test)
                test=$2
                ;;
      -reg)
                start_vmanager
                in_regression=yes
                ;;
      -s|seed)
                seed=$2
                ;;
      -top)
                top_name=$2
                ;;
      -i)
                run_mode=interactive
                ;;
      -f|file)
                file_name=$2
                ;;
      -verbosity)
                uvm_verbosity=$2
                ;;
      -bit)
                ARCH_BITS=$2
                shift
                ;;
      -uvm)
                uvm_version=$2
                ;;
      -in_reg)
                in_regression=yes
                ;;
    esac
    shift
done

export ARCH_BITS=${ARCH_BITS}
export top_name=${top_name}
if [ -f "$file_name" ];
then
   export file_name=${file_name}
else
   export file_name=${PROJ_HOME}/${file_name}
fi

##########################################################################################
#  Verify that the simulator is one of IUS, QUESTA or VCS
##########################################################################################
case $tool in
    ius)
        echo "Selected tool: IUS..."
    ;;
    vcs)
        echo "Selected tool: VCS..."
    ;;
    questa)
        echo "Selected tool: Questa..."
    ;;
    *)
        echo "Illegal option for tool: $tool"
        exit 1;
    ;;
esac


##########################################################################################
#  Verify that the UVM_VERSION option is one of uvm1.1 or uvm1.2
##########################################################################################
case $uvm_version in
    uvm1.1)
        echo "Selected UVM1.1"
    ;;
    uvm1.2)
        echo "Selected UVM1.2"
    ;;
    *)
        echo "Illegal option for UVM version: $uvm_version"
        exit 1;
    ;;
esac

##########################################################################################
#  Verify that the compile_option option is one of yes or no
##########################################################################################
case $compile_option in
    yes)
        compile
        ;;
    no)
        ;;
    only)
        compile
        exit 0
        ;;
    *)
        echo "ERROR:"
        echo "-c[ompile] option must be called with \"yes\" or \"no\" or \"only\" - current value: ${compile_option}"
        exit 1
    ;;
esac

sim_dir=`pwd`
echo "Start running ${test} test in ${sim_dir}";

run_with_${tool}_test
