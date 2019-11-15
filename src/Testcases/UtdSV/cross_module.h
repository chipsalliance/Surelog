/*
* ========== Copyright Header Begin ==========================================
* 
* OpenSPARC T1 Processor File: cross_module.h
* Copyright (c) 2006 Sun Microsystems, Inc.  All Rights Reserved.
* DO NOT ALTER OR REMOVE COPYRIGHT NOTICES.
* 
* The above named program is free software; you can redistribute it and/or
* modify it under the terms of the GNU General Public
* License version 2 as published by the Free Software Foundation.
* 
* The above named program is distributed in the hope that it will be 
* useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
* General Public License for more details.
* 
* You should have received a copy of the GNU General Public
* License along with this work; if not, write to the Free Software
* Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA.
* 
* ========== Copyright Header End ============================================
*/
`define MONITOR_SIGNAL                 155
`define FLOAT_X                        154
`define FLOAT_I                        153
`define REG_WRITE_BACK                 152
/*
`define     PC                         32
`define     NPC                        33
`define     Y                          34
`define     CCR                        35
`define     FPRS                       36
`define     FSR                        37
`define     ASI                        38
`define     TICK                       39
`define     GSR                        40
`define     TICK_CMPR                  41
`define     STICK                      42
`define     STICK_CMPR                 43
`define     PSTATE                     44
`define     TL                         45
`define     PIL                        46

`define     TPC1                       47
`define     TPC2                       48
`define     TPC3                       49
`define     TPC4                       50
`define     TPC5                       51 
`define     TPC6                       52

`define     TNPC1                      57  
`define     TNPC2                      58
`define     TNPC3                      59
`define     TNPC4                      60
`define     TNPC5                      61
`define     TNPC6                      62

`define     TSTATE1                    67
`define     TSTATE2                    68
`define     TSTATE3                    69
`define     TSTATE4                    70
`define     TSTATE5                    71
`define     TSTATE6                    72

`define     TT1                        77
`define     TT2                        78
`define     TT3                        79
`define     TT4                        80
`define     TT5                        81
`define     TT6                        82

`define     TBA                        87
`define     VER                        88
`define     CWP                        89
`define     CANSAVE                    90
`define     CANRESTORE                 91
`define     OTHERWIN                   92
`define     WSTATE                     93
`define     CLEANWIN                   94
`define     SOFTINT                    95
`define     ECACHE_ERROR_ENABLE        96
`define     ASYNCHRONOUS_FAULT_STATUS  97
`define     ASYNCHRONOUS_FAULT_ADDRESS 98
`define     OUT_INTR_DATA0             99
`define     OUT_INTR_DATA1             100
`define     OUT_INTR_DATA2             101
`define     INTR_DISPATCH_STATUS       102
`define     IN_INTR_DATA0              103
`define     IN_INTR_DATA1              104
`define     IN_INTR_DATA2              105
`define     INTR_RECEIVE               106
`define     GL                         107
`define     HPSTATE                    108
`define     HTSTATE1                   109
`define     HTSTATE2                   110
`define     HTSTATE3                   111
`define     HTSTATE4                   112
`define     HTSTATE5                   113
`define     HTSTATE6                   114
`define     HTSTATE7                   115
`define     HTSTATE8                   116
`define     HTSTATE9                   117
`define     HTSTATE10                  118
`define     HTBA                       119
`define     HINTP                      120
`define     HSTICK_CMPR                121
`define     MID                        122
`define     ISFSR                      123
`define     DSFSR                      124
`define     SFAR                       125
*/
`define PLI_QUIT                1    /* None */
`define PLI_SSTEP               2    /* %1 th id */
`define PLI_READ_TH_REG         3    /* %1 th id, %2 win num, %3 reg num */
`define PLI_READ_TH_CTL_REG     4    /* %1 th id, %2 reg num */
`define PLI_READ_TH_FP_REG_I    5    /* %1 th id, %2 reg num */
`define PLI_READ_TH_FP_REG_X    6    /* %1 th id, %2 reg num */
`define PLI_RTL_DATA            7
`define PLI_RTL_CYCLE           8  
`define PLI_WRITE_TH_XCC_REG    9
`define PLI_FORCE_TRAP_TYPE            15
`define PLI_RESET_TLB_ENTRY     16
`define PLI_RETRY               30
`define PLI_WRITE_TH_REG_HI     10
`define PLI_WRITE_TH_REG        11
`define PLI_WRITE_TH_CTL_REG    12    /* %1 th id, %2 reg num, %3-%10 value */
`define CMD_BUFSIZE 10240
//define all cross module
`ifdef CIOP
`define TOP_MOD      ciop_top
`define TOP_SHELL    ciop_top_shell
`define TOP_MOD_INST `TOP_MOD.ciop
`define TOP_DESIGN   `TOP_MOD.ciop
`define TOP_MEMORY   `TOP_MOD.ciop
`else
`define TOP_MOD      cmp_top
`define TOP_SHELL    cmp_top_shell
`define TOP_MOD_INST `TOP_MOD.iop
`define TOP_DESIGN   `TOP_MOD.iop
`define TOP_MEMORY   `TOP_MOD.iop
`endif

`define MONITOR_PATH `TOP_MOD.monitor
`define PC_CMP       `TOP_MOD.monitor.pc_cmp
`define SAS_SEND     `TOP_MOD.sas_tasks.send_cmd
`define SAS_DEF      `TOP_MOD.sas_tasks.sas_def
`define SAS_TASKS    `TOP_MOD.sas_tasks
//sctag path
`define SCPATH0      `TOP_MEMORY.sctag0
`define SCPATH1      `TOP_MEMORY.sctag1
`define SCPATH2      `TOP_MEMORY.sctag2
`define SCPATH3      `TOP_MEMORY.sctag3
`define SCPATH4      `TOP_MEMORY.sctag4
`define SCPATH5      `TOP_MEMORY.sctag5
`define SCPATH6      `TOP_MEMORY.sctag6
`define SCPATH7      `TOP_MEMORY.sctag7
//sctdata path
`define SCDPATH0      `TOP_MEMORY.scdata0
`define SCDPATH1      `TOP_MEMORY.scdata1
`define SCDPATH2      `TOP_MEMORY.scdata2
`define SCDPATH3      `TOP_MEMORY.scdata3
`define CPX_INVALID_TIME 50

`ifdef GATE_SIM_SPARC

`define SPARC_REG0   `TOP_DESIGN.sparc0.exu_irf
`define SPARC_REG1   `TOP_DESIGN.sparc1.exu_irf
`define SPARC_REG2   `TOP_DESIGN.sparc2.exu_irf
`define SPARC_REG3   `TOP_DESIGN.sparc3.exu_irf
`define SPARC_REG4   `TOP_DESIGN.sparc4.exu_irf
`define SPARC_REG5   `TOP_DESIGN.sparc5.exu_irf
`define SPARC_REG6   `TOP_DESIGN.sparc6.exu_irf
`define SPARC_REG7   `TOP_DESIGN.sparc7.exu_irf

`define FLOATPATH0   `TOP_DESIGN.sparc0
`define FLOATPATH1   `TOP_DESIGN.sparc1
`define FLOATPATH2   `TOP_DESIGN.sparc2
`define FLOATPATH3   `TOP_DESIGN.sparc3
`define FLOATPATH4   `TOP_DESIGN.sparc4
`define FLOATPATH5   `TOP_DESIGN.sparc5
`define FLOATPATH6   `TOP_DESIGN.sparc6
`define FLOATPATH7   `TOP_DESIGN.sparc7

`else

`define SPARC_REG0   `TOP_DESIGN.sparc0.exu.irf
`define SPARC_REG1   `TOP_DESIGN.sparc1.exu.irf
`define SPARC_REG2   `TOP_DESIGN.sparc2.exu.irf
`define SPARC_REG3   `TOP_DESIGN.sparc3.exu.irf
`define SPARC_REG4   `TOP_DESIGN.sparc4.exu.irf
`define SPARC_REG5   `TOP_DESIGN.sparc5.exu.irf
`define SPARC_REG6   `TOP_DESIGN.sparc6.exu.irf
`define SPARC_REG7   `TOP_DESIGN.sparc7.exu.irf

`define FLOATPATH0   `TOP_DESIGN.sparc0.ffu
`define FLOATPATH1   `TOP_DESIGN.sparc1.ffu
`define FLOATPATH2   `TOP_DESIGN.sparc2.ffu
`define FLOATPATH3   `TOP_DESIGN.sparc3.ffu
`define FLOATPATH4   `TOP_DESIGN.sparc4.ffu
`define FLOATPATH5   `TOP_DESIGN.sparc5.ffu
`define FLOATPATH6   `TOP_DESIGN.sparc6.ffu
`define FLOATPATH7   `TOP_DESIGN.sparc7.ffu

`endif // ifdef GATE_SIM_SPARC

`define TLUPATH0     `TOP_DESIGN.sparc0.tlu
`define TLUPATH1     `TOP_DESIGN.sparc1.tlu
`define TLUPATH2     `TOP_DESIGN.sparc2.tlu
`define TLUPATH3     `TOP_DESIGN.sparc3.tlu
`define TLUPATH4     `TOP_DESIGN.sparc4.tlu
`define TLUPATH5     `TOP_DESIGN.sparc5.tlu
`define TLUPATH6     `TOP_DESIGN.sparc6.tlu
`define TLUPATH7     `TOP_DESIGN.sparc7.tlu

`define DTLBPATH0     `TOP_DESIGN.sparc0.lsu.dtlb
`define DTLBPATH1     `TOP_DESIGN.sparc1.lsu.dtlb
`define DTLBPATH2     `TOP_DESIGN.sparc2.lsu.dtlb
`define DTLBPATH3     `TOP_DESIGN.sparc3.lsu.dtlb
`define DTLBPATH4     `TOP_DESIGN.sparc4.lsu.dtlb
`define DTLBPATH5     `TOP_DESIGN.sparc5.lsu.dtlb
`define DTLBPATH6     `TOP_DESIGN.sparc6.lsu.dtlb
`define DTLBPATH7     `TOP_DESIGN.sparc7.lsu.dtlb

`define ITLBPATH0     `TOP_DESIGN.sparc0.ifu.itlb
`define ITLBPATH1     `TOP_DESIGN.sparc1.ifu.itlb
`define ITLBPATH2     `TOP_DESIGN.sparc2.ifu.itlb
`define ITLBPATH3     `TOP_DESIGN.sparc3.ifu.itlb
`define ITLBPATH4     `TOP_DESIGN.sparc4.ifu.itlb
`define ITLBPATH5     `TOP_DESIGN.sparc5.ifu.itlb
`define ITLBPATH6     `TOP_DESIGN.sparc6.ifu.itlb
`define ITLBPATH7     `TOP_DESIGN.sparc7.ifu.itlb

//cross reference for pcx and cpx packet.
`define PCXPATH0   `TOP_DESIGN.sparc0
`define PCXPATH1   `TOP_DESIGN.sparc1
`define PCXPATH2   `TOP_DESIGN.sparc2
`define PCXPATH3   `TOP_DESIGN.sparc3
`define PCXPATH4   `TOP_DESIGN.sparc4
`define PCXPATH5   `TOP_DESIGN.sparc5
`define PCXPATH6   `TOP_DESIGN.sparc6
`define PCXPATH7   `TOP_DESIGN.sparc7
//dram 
`define DRAMPATH0  `TOP_MOD.cmp_dram.mem0
`define DRAMPATH1  `TOP_MOD.cmp_dram.mem1
`define DRAMPATH2  `TOP_MOD.cmp_dram.mem2
`define DRAMPATH3  `TOP_MOD.cmp_dram.mem3
`define DCTLPATH0  `TOP_MEMORY.dram02
`define DCTLPATH1  `TOP_MEMORY.dram13

`ifdef GATE_SIM_SPARC
//icv
`define ICVPATH0      `TOP_DESIGN.sparc0.ifu_icv
`define ICVPATH1      `TOP_DESIGN.sparc1.ifu_icv
`define ICVPATH2      `TOP_DESIGN.sparc2.ifu_icv
`define ICVPATH3      `TOP_DESIGN.sparc3.ifu_icv
`define ICVPATH4      `TOP_DESIGN.sparc4.ifu_icv
`define ICVPATH5      `TOP_DESIGN.sparc5.ifu_icv
`define ICVPATH6      `TOP_DESIGN.sparc6.ifu_icv
`define ICVPATH7      `TOP_DESIGN.sparc7.ifu_icv
`else
`define ICVPATH0      `TOP_DESIGN.sparc0.ifu.icv
`define ICVPATH1      `TOP_DESIGN.sparc1.ifu.icv
`define ICVPATH2      `TOP_DESIGN.sparc2.ifu.icv
`define ICVPATH3      `TOP_DESIGN.sparc3.ifu.icv
`define ICVPATH4      `TOP_DESIGN.sparc4.ifu.icv
`define ICVPATH5      `TOP_DESIGN.sparc5.ifu.icv
`define ICVPATH6      `TOP_DESIGN.sparc6.ifu.icv
`define ICVPATH7      `TOP_DESIGN.sparc7.ifu.icv
`endif // ifdef GATE_SIM_SPARC

//ict
`ifdef GATE_SIM_SPARC
`define ICTPATH0      `TOP_DESIGN.sparc0.ifu_ict
`define ICTPATH1      `TOP_DESIGN.sparc1.ifu_ict
`define ICTPATH2      `TOP_DESIGN.sparc2.ifu_ict
`define ICTPATH3      `TOP_DESIGN.sparc3.ifu_ict
`define ICTPATH4      `TOP_DESIGN.sparc4.ifu_ict
`define ICTPATH5      `TOP_DESIGN.sparc5.ifu_ict
`define ICTPATH6      `TOP_DESIGN.sparc6.ifu_ict
`define ICTPATH7      `TOP_DESIGN.sparc7.ifu_ict
`else
`define ICTPATH0      `TOP_DESIGN.sparc0.ifu.ict
`define ICTPATH1      `TOP_DESIGN.sparc1.ifu.ict
`define ICTPATH2      `TOP_DESIGN.sparc2.ifu.ict
`define ICTPATH3      `TOP_DESIGN.sparc3.ifu.ict
`define ICTPATH4      `TOP_DESIGN.sparc4.ifu.ict
`define ICTPATH5      `TOP_DESIGN.sparc5.ifu.ict
`define ICTPATH6      `TOP_DESIGN.sparc6.ifu.ict
`define ICTPATH7      `TOP_DESIGN.sparc7.ifu.ict
`endif
// ifu
`define IFUPATH0      `TOP_DESIGN.sparc0.ifu
`define IFUPATH1      `TOP_DESIGN.sparc1.ifu
`define IFUPATH2      `TOP_DESIGN.sparc2.ifu
`define IFUPATH3      `TOP_DESIGN.sparc3.ifu
`define IFUPATH4      `TOP_DESIGN.sparc4.ifu
`define IFUPATH5      `TOP_DESIGN.sparc5.ifu
`define IFUPATH6      `TOP_DESIGN.sparc6.ifu
`define IFUPATH7      `TOP_DESIGN.sparc7.ifu
//thread
`define TNUM0S `TOP_DESIGN.sparc0.ifu.swl
`define TPC0S  `TOP_DESIGN.sparc0.ifu.fdp
`define TNUM1S `TOP_DESIGN.sparc1.ifu.swl
`define TPC1S  `TOP_DESIGN.sparc1.ifu.fdp
`define TNUM2S `TOP_DESIGN.sparc2.ifu.swl
`define TPC2S  `TOP_DESIGN.sparc2.ifu.fdp
`define TNUM3S `TOP_DESIGN.sparc3.ifu.swl
`define TPC3S  `TOP_DESIGN.sparc3.ifu.fdp
`define TNUM4S `TOP_DESIGN.sparc4.ifu.swl
`define TPC4S  `TOP_DESIGN.sparc4.ifu.fdp
`define TNUM5S `TOP_DESIGN.sparc5.ifu.swl
`define TPC5S  `TOP_DESIGN.sparc5.ifu.fdp
`define TNUM6S `TOP_DESIGN.sparc4.ifu.swl
`define TPC6S  `TOP_DESIGN.sparc4.ifu.fdp
`define TNUM7S `TOP_DESIGN.sparc5.ifu.swl
`define TPC7S  `TOP_DESIGN.sparc5.ifu.fdp

`define STNUM `TOP_DESIGN.sparc0.ifu.dtu.swl
`define STPC  `TOP_DESIGN.sparc0.ifu.fdp
//sas task
`define MONITOR `TOP_MOD.monitor

`define TDPPATH0   `TOP_DESIGN.sparc0.tlu.tdp
`define TDPPATH1   `TOP_DESIGN.sparc1.tlu.tdp
`define TDPPATH2   `TOP_DESIGN.sparc2.tlu.tdp
`define TDPPATH3   `TOP_DESIGN.sparc3.tlu.tdp
`define TDPPATH4   `TOP_DESIGN.sparc4.tlu.tdp
`define TDPPATH5   `TOP_DESIGN.sparc5.tlu.tdp
`define TDPPATH6   `TOP_DESIGN.sparc6.tlu.tdp
`define TDPPATH7   `TOP_DESIGN.sparc7.tlu.tdp

`ifdef GATE_SIM_SPARC
`define DTUPATH0  `TOP_DESIGN.sparc0.ifu_fdp
`define DTUPATH1  `TOP_DESIGN.sparc1.ifu_fdp
`define DTUPATH2  `TOP_DESIGN.sparc2.ifu_fdp
`define DTUPATH3  `TOP_DESIGN.sparc3.ifu_fdp
`define DTUPATH4  `TOP_DESIGN.sparc4.ifu_fdp
`define DTUPATH5  `TOP_DESIGN.sparc5.ifu_fdp
`define DTUPATH6  `TOP_DESIGN.sparc6.ifu_fdp
`define DTUPATH7  `TOP_DESIGN.sparc7.ifu_fdp
`else
`define DTUPATH0  `TOP_DESIGN.sparc0.ifu.fdp
`define DTUPATH1  `TOP_DESIGN.sparc1.ifu.fdp
`define DTUPATH2  `TOP_DESIGN.sparc2.ifu.fdp
`define DTUPATH3  `TOP_DESIGN.sparc3.ifu.fdp
`define DTUPATH4  `TOP_DESIGN.sparc4.ifu.fdp
`define DTUPATH5  `TOP_DESIGN.sparc5.ifu.fdp
`define DTUPATH6  `TOP_DESIGN.sparc6.ifu.fdp
`define DTUPATH7  `TOP_DESIGN.sparc7.ifu.fdp
`endif // ifdef GATE_SIM_SPARC

`define ALUPATH0  `TOP_DESIGN.sparc0.exu.alu
`define ALUPATH1  `TOP_DESIGN.sparc1.exu.alu
`define ALUPATH2  `TOP_DESIGN.sparc2.exu.alu
`define ALUPATH3  `TOP_DESIGN.sparc3.exu.alu
`define ALUPATH4  `TOP_DESIGN.sparc4.exu.alu
`define ALUPATH5  `TOP_DESIGN.sparc5.exu.alu
`define ALUPATH6  `TOP_DESIGN.sparc6.exu.alu
`define ALUPATH7  `TOP_DESIGN.sparc7.exu.alu

`define SPCPATH0 `TOP_DESIGN.sparc0
`define SPCPATH1 `TOP_DESIGN.sparc1
`define SPCPATH2 `TOP_DESIGN.sparc2
`define SPCPATH3 `TOP_DESIGN.sparc3
`define SPCPATH4 `TOP_DESIGN.sparc4
`define SPCPATH5 `TOP_DESIGN.sparc5
`define SPCPATH6 `TOP_DESIGN.sparc6
`define SPCPATH7 `TOP_DESIGN.sparc7

`define REGPATH0 `TOP_DESIGN.sparc0.exu.irf
`define REGPATH1 `TOP_DESIGN.sparc1.exu.irf
`define REGPATH2 `TOP_DESIGN.sparc2.exu.irf
`define REGPATH3 `TOP_DESIGN.sparc3.exu.irf
`define REGPATH4 `TOP_DESIGN.sparc4.exu.irf
`define REGPATH5 `TOP_DESIGN.sparc5.exu.irf
`define REGPATH6 `TOP_DESIGN.sparc6.exu.irf
`define REGPATH7 `TOP_DESIGN.sparc7.exu.irf

// define fetch unit path

`define CCRPATH0 `TOP_DESIGN.sparc0.exu.ecl.ccr
`define CCRPATH1 `TOP_DESIGN.sparc1.exu.ecl.ccr
`define CCRPATH2 `TOP_DESIGN.sparc2.exu.ecl.ccr
`define CCRPATH3 `TOP_DESIGN.sparc3.exu.ecl.ccr
`define CCRPATH4 `TOP_DESIGN.sparc4.exu.ecl.ccr
`define CCRPATH5 `TOP_DESIGN.sparc5.exu.ecl.ccr
`define CCRPATH6 `TOP_DESIGN.sparc6.exu.ecl.ccr
`define CCRPATH7 `TOP_DESIGN.sparc7.exu.ecl.ccr

`define EXUPATH0 `TOP_DESIGN.sparc0.exu
`define EXUPATH1 `TOP_DESIGN.sparc1.exu
`define EXUPATH2 `TOP_DESIGN.sparc2.exu
`define EXUPATH3 `TOP_DESIGN.sparc3.exu
`define EXUPATH4 `TOP_DESIGN.sparc4.exu
`define EXUPATH5 `TOP_DESIGN.sparc5.exu
`define EXUPATH6 `TOP_DESIGN.sparc6.exu
`define EXUPATH7 `TOP_DESIGN.sparc7.exu

//tl register
`define TLPATH0   `TOP_DESIGN.sparc0.tlu.tcl
`define TLPATH1   `TOP_DESIGN.sparc1.tlu.tcl
`define TLPATH2   `TOP_DESIGN.sparc2.tlu.tcl
`define TLPATH3   `TOP_DESIGN.sparc3.tlu.tcl
`define TLPATH4   `TOP_DESIGN.sparc4.tlu.tcl
`define TLPATH5   `TOP_DESIGN.sparc5.tlu.tcl
`define TLPATH6   `TOP_DESIGN.sparc6.tlu.tcl
`define TLPATH7   `TOP_DESIGN.sparc7.tlu.tcl
// 
// modified due to memory macro swp of the tsa
`define TS0PATH0   `TOP_DESIGN.sparc0.tlu.tsa0
`define TS0PATH1   `TOP_DESIGN.sparc1.tlu.tsa0
`define TS0PATH2   `TOP_DESIGN.sparc2.tlu.tsa0
`define TS0PATH3   `TOP_DESIGN.sparc3.tlu.tsa0
`define TS0PATH4   `TOP_DESIGN.sparc4.tlu.tsa0
`define TS0PATH5   `TOP_DESIGN.sparc5.tlu.tsa0
`define TS0PATH6   `TOP_DESIGN.sparc6.tlu.tsa0
`define TS0PATH7   `TOP_DESIGN.sparc7.tlu.tsa0
//
`define TS1PATH0   `TOP_DESIGN.sparc0.tlu.tsa1
`define TS1PATH1   `TOP_DESIGN.sparc1.tlu.tsa1
`define TS1PATH2   `TOP_DESIGN.sparc2.tlu.tsa1
`define TS1PATH3   `TOP_DESIGN.sparc3.tlu.tsa1
`define TS1PATH4   `TOP_DESIGN.sparc4.tlu.tsa1
`define TS1PATH5   `TOP_DESIGN.sparc5.tlu.tsa1
`define TS1PATH6   `TOP_DESIGN.sparc6.tlu.tsa1
`define TS1PATH7   `TOP_DESIGN.sparc7.tlu.tsa1
//interrupt path
`define INTPATH0  `TOP_DESIGN.sparc0.tlu.intdp
`define INTPATH1  `TOP_DESIGN.sparc1.tlu.intdp
`define INTPATH2  `TOP_DESIGN.sparc2.tlu.intdp
`define INTPATH3  `TOP_DESIGN.sparc3.tlu.intdp
`define INTPATH4  `TOP_DESIGN.sparc4.tlu.intdp
`define INTPATH5  `TOP_DESIGN.sparc5.tlu.intdp
`define INTPATH6  `TOP_DESIGN.sparc6.tlu.intdp
`define INTPATH7  `TOP_DESIGN.sparc7.tlu.intdp
// asic
`define ASIPATH0  `TOP_DESIGN.sparc0.lsu.dctl
`define ASIPATH1  `TOP_DESIGN.sparc1.lsu.dctl
`define ASIPATH2  `TOP_DESIGN.sparc2.lsu.dctl
`define ASIPATH3  `TOP_DESIGN.sparc3.lsu.dctl
`define ASIPATH4  `TOP_DESIGN.sparc4.lsu.dctl
`define ASIPATH5  `TOP_DESIGN.sparc5.lsu.dctl
`define ASIPATH6  `TOP_DESIGN.sparc6.lsu.dctl
`define ASIPATH7  `TOP_DESIGN.sparc7.lsu.dctl
`define ASIDPPATH0  `TOP_DESIGN.sparc0.lsu.dctldp
`define ASIDPPATH1  `TOP_DESIGN.sparc1.lsu.dctldp
`define ASIDPPATH2  `TOP_DESIGN.sparc2.lsu.dctldp
`define ASIDPPATH3  `TOP_DESIGN.sparc3.lsu.dctldp
`define ASIDPPATH4  `TOP_DESIGN.sparc4.lsu.dctldp
`define ASIDPPATH5  `TOP_DESIGN.sparc5.lsu.dctldp
`define ASIDPPATH6  `TOP_DESIGN.sparc6.lsu.dctldp
`define ASIDPPATH7  `TOP_DESIGN.sparc7.lsu.dctldp
`define SAS_INTER `TOP_MOD.sas_intf

//pc-cmp
`ifdef GATE_SIM_SPARC
`define INSTPATH0     `TOP_DESIGN.sparc0.ifu_fcl
`define PCPATH0       `TOP_DESIGN.sparc0
`define INSTPATH1     `TOP_DESIGN.sparc1.ifu_fcl
`define PCPATH1       `TOP_DESIGN.sparc1
`define INSTPATH2     `TOP_DESIGN.sparc2.ifu_fcl
`define PCPATH2       `TOP_DESIGN.sparc2
`define INSTPATH3     `TOP_DESIGN.sparc3.ifu_fcl
`define PCPATH3       `TOP_DESIGN.sparc3
`define INSTPATH4     `TOP_DESIGN.sparc4.ifu_fcl
`define PCPATH4       `TOP_DESIGN.sparc4
`define INSTPATH5     `TOP_DESIGN.sparc5.ifu_fcl
`define PCPATH5       `TOP_DESIGN.sparc5
`define INSTPATH6     `TOP_DESIGN.sparc6.ifu_fcl
`define PCPATH6       `TOP_DESIGN.sparc6
`define INSTPATH7     `TOP_DESIGN.sparc7.ifu_fcl
`define PCPATH7       `TOP_DESIGN.sparc7
`else
`define INSTPATH0     `TOP_DESIGN.sparc0.ifu.fcl
`define PCPATH0       `TOP_DESIGN.sparc0.ifu
`define INSTPATH1     `TOP_DESIGN.sparc1.ifu.fcl
`define PCPATH1       `TOP_DESIGN.sparc1.ifu
`define INSTPATH2     `TOP_DESIGN.sparc2.ifu.fcl
`define PCPATH2       `TOP_DESIGN.sparc2.ifu
`define INSTPATH3     `TOP_DESIGN.sparc3.ifu.fcl
`define PCPATH3       `TOP_DESIGN.sparc3.ifu
`define INSTPATH4     `TOP_DESIGN.sparc4.ifu.fcl
`define PCPATH4       `TOP_DESIGN.sparc4.ifu
`define INSTPATH5     `TOP_DESIGN.sparc5.ifu.fcl
`define PCPATH5       `TOP_DESIGN.sparc5.ifu
`define INSTPATH6     `TOP_DESIGN.sparc6.ifu.fcl
`define PCPATH6       `TOP_DESIGN.sparc6.ifu
`define INSTPATH7     `TOP_DESIGN.sparc7.ifu.fcl
`define PCPATH7       `TOP_DESIGN.sparc7.ifu
`endif // GATE_SIM_SPARC 

//dump cache
`ifdef GATE_SIM_SPARC
`define DVLD0 `TOP_DESIGN.sparc0.lsu_dva
`define DVLD1 `TOP_DESIGN.sparc1.lsu_dva
`define DVLD2 `TOP_DESIGN.sparc2.lsu_dva
`define DVLD3 `TOP_DESIGN.sparc3.lsu_dva
`define DVLD4 `TOP_DESIGN.sparc4.lsu_dva
`define DVLD5 `TOP_DESIGN.sparc5.lsu_dva
`define DVLD6 `TOP_DESIGN.sparc6.lsu_dva
`define DVLD7 `TOP_DESIGN.sparc7.lsu_dva
`else
`define DVLD0 `TOP_DESIGN.sparc0.lsu.dva
`define DVLD1 `TOP_DESIGN.sparc1.lsu.dva
`define DVLD2 `TOP_DESIGN.sparc2.lsu.dva
`define DVLD3 `TOP_DESIGN.sparc3.lsu.dva
`define DVLD4 `TOP_DESIGN.sparc4.lsu.dva
`define DVLD5 `TOP_DESIGN.sparc5.lsu.dva
`define DVLD6 `TOP_DESIGN.sparc6.lsu.dva
`define DVLD7 `TOP_DESIGN.sparc7.lsu.dva
`endif // GATE_SIM_SPARC 

`ifdef GATE_SIM_SPARC
`define DTAG0 `TOP_DESIGN.sparc0.lsu_dtag
`define DTAG1 `TOP_DESIGN.sparc1.lsu_dtag
`define DTAG2 `TOP_DESIGN.sparc2.lsu_dtag
`define DTAG3 `TOP_DESIGN.sparc3.lsu_dtag
`define DTAG4 `TOP_DESIGN.sparc4.lsu_dtag
`define DTAG5 `TOP_DESIGN.sparc5.lsu_dtag
`define DTAG6 `TOP_DESIGN.sparc6.lsu_dtag
`define DTAG7 `TOP_DESIGN.sparc7.lsu_dtag
`else
`define DTAG0 `TOP_DESIGN.sparc0.lsu.dtag
`define DTAG1 `TOP_DESIGN.sparc1.lsu.dtag
`define DTAG2 `TOP_DESIGN.sparc2.lsu.dtag
`define DTAG3 `TOP_DESIGN.sparc3.lsu.dtag
`define DTAG4 `TOP_DESIGN.sparc4.lsu.dtag
`define DTAG5 `TOP_DESIGN.sparc5.lsu.dtag
`define DTAG6 `TOP_DESIGN.sparc6.lsu.dtag
`define DTAG7 `TOP_DESIGN.sparc7.lsu.dtag
`endif


`define SDTAG0 `TOP_DESIGN.sparc0.lsu.dtag
`define SDVLD0 `TOP_DESIGN.sparc0.lsu.dva

`define ITAG0 `TOP_MOD.monitor.l_cache_mon0
`define IVLD0 `TOP_MOD.monitor.l_cache_mon0
`define ITAG1 `TOP_MOD.monitor.l_cache_mon1
`define IVLD1 `TOP_MOD.monitor.l_cache_mon1
`define ITAG2 `TOP_MOD.monitor.l_cache_mon2
`define IVLD2 `TOP_MOD.monitor.l_cache_mon2
`define ITAG3 `TOP_MOD.monitor.l_cache_mon3
`define IVLD3 `TOP_MOD.monitor.l_cache_mon3
`define ITAG4 `TOP_MOD.monitor.l_cache_mon4
`define IVLD4 `TOP_MOD.monitor.l_cache_mon4
`define ITAG5 `TOP_MOD.monitor.l_cache_mon5
`define IVLD5 `TOP_MOD.monitor.l_cache_mon5
`define ITAG6 `TOP_MOD.monitor.l_cache_mon6
`define IVLD6 `TOP_MOD.monitor.l_cache_mon6
`define ITAG7 `TOP_MOD.monitor.l_cache_mon7
`define IVLD7 `TOP_MOD.monitor.l_cache_mon7
//define spu path
`define SPUPATH0 `TOP_DESIGN.sparc0.spu
`define SPUPATH1 `TOP_DESIGN.sparc1.spu
`define SPUPATH2 `TOP_DESIGN.sparc2.spu
`define SPUPATH3 `TOP_DESIGN.sparc3.spu
`define SPUPATH4 `TOP_DESIGN.sparc4.spu
`define SPUPATH5 `TOP_DESIGN.sparc5.spu
`define SPUPATH6 `TOP_DESIGN.sparc6.spu
`define SPUPATH7 `TOP_DESIGN.sparc7.spu

//dram path
`define DRAM_PATH0 `DCTLPATH0.dramctl0.dram_dctl.dram_que
`define DRAM_PATH1 `DCTLPATH0.dramctl1.dram_dctl.dram_que
`define DRAM_PATH2 `DCTLPATH1.dramctl0.dram_dctl.dram_que
`define DRAM_PATH3 `DCTLPATH1.dramctl1.dram_dctl.dram_que
//graphic status
//define spu path
`define FFUPATH0 `TOP_DESIGN.sparc0.ffu
`define FFUPATH1 `TOP_DESIGN.sparc1.ffu
`define FFUPATH2 `TOP_DESIGN.sparc2.ffu
`define FFUPATH3 `TOP_DESIGN.sparc3.ffu
`define FFUPATH4 `TOP_DESIGN.sparc4.ffu
`define FFUPATH5 `TOP_DESIGN.sparc5.ffu
`define FFUPATH6 `TOP_DESIGN.sparc6.ffu
`define FFUPATH7 `TOP_DESIGN.sparc7.ffu
//hypervisor
`define TLU_HYPER0 `TOP_DESIGN.sparc0.tlu.tlu_hyperv
`define TLU_HYPER1 `TOP_DESIGN.sparc1.tlu.tlu_hyperv
`define TLU_HYPER2 `TOP_DESIGN.sparc2.tlu.tlu_hyperv
`define TLU_HYPER3 `TOP_DESIGN.sparc3.tlu.tlu_hyperv
`define TLU_HYPER4 `TOP_DESIGN.sparc4.tlu.tlu_hyperv
`define TLU_HYPER5 `TOP_DESIGN.sparc5.tlu.tlu_hyperv
`define TLU_HYPER6 `TOP_DESIGN.sparc6.tlu.tlu_hyperv
`define TLU_HYPER7 `TOP_DESIGN.sparc7.tlu.tlu_hyperv

`ifdef GATE_SIM_SPARC
`define IFQDP0 `TOP_DESIGN.sparc0.ifu_ifqdp
`define IFQDP1 `TOP_DESIGN.sparc1.ifu_ifqdp
`define IFQDP2 `TOP_DESIGN.sparc2.ifu_ifqdp
`define IFQDP3 `TOP_DESIGN.sparc3.ifu_ifqdp
`define IFQDP4 `TOP_DESIGN.sparc4.ifu_ifqdp
`define IFQDP5 `TOP_DESIGN.sparc5.ifu_ifqdp
`define IFQDP6 `TOP_DESIGN.sparc6.ifu_ifqdp
`define IFQDP7 `TOP_DESIGN.sparc7.ifu_ifqdp
`else
`define IFQDP0 `TOP_DESIGN.sparc0.ifu.ifqdp
`define IFQDP1 `TOP_DESIGN.sparc1.ifu.ifqdp
`define IFQDP2 `TOP_DESIGN.sparc2.ifu.ifqdp
`define IFQDP3 `TOP_DESIGN.sparc3.ifu.ifqdp
`define IFQDP4 `TOP_DESIGN.sparc4.ifu.ifqdp
`define IFQDP5 `TOP_DESIGN.sparc5.ifu.ifqdp
`define IFQDP6 `TOP_DESIGN.sparc6.ifu.ifqdp
`define IFQDP7 `TOP_DESIGN.sparc7.ifu.ifqdp
`endif // ifdef GATE_SIM_SPARC
