/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

// ------------------------------------------------------------------------
// Synthesis Defines
// ------------------------------------------------------------------------

//`define DDR_SYNTH                                 // Include/Exclude RTL for synthesis
`ifndef DDR_SYNTH
//`define DDR_DEBUG                                 // Enable debug code
  `define DDR_AHB_SVA                               // Enable AHB SV assertions
//`define WAV_TECH_LIB_BEHAV                        // Enable PLL_dig standard logic behavioral code
//`define DDR_FASTx16_REFCLK                        /  Enable in simulations when Ref clock frequency is x16 times faster than what is expected by PLL.
//`define WLOGIC_NO_PG                              // Disable power ports on Wavious cells
//`define WLOGIC_NO_TIE                             // Tie all tielo/hi signals constants inside the wavious cell models
  `define WPIN_UART_EN                              // Used for analog signals (VREF)
  `define WCHANNEL_EN                               // Enabled channel model in SA
  `define CLIB_FF_TIMING_EN
  `define CLIB_TIMING_CHK
  `define ARM_UD_DP=#0
  `define ARM_UD_MODEL
`else
  `define WLOGIC_NO_PG                              // Disable power ports on Wavious cells
  `define SYNTHESIS                                 // IBEX RISC-V synthesis flag
  `define DDR_ENABLE_RX_SDRLPDE_SMALL
`endif

// ------------------------------------------------------------------------
// IBEX Defines
// ------------------------------------------------------------------------

`ifndef DDR_SYNTH
  `define INC_ASSERT                                // IBEX assertions
  `define CHECK_MISALIGNED                          // IBEX assertions
`endif

// ------------------------------------------------------------------------
// Spice Defines
// ------------------------------------------------------------------------

//`define DDR_SPICE                                 // Enable SPICE features

`ifdef DDR_SPICE
  `define DDR_SPICE_PRINT                           // PRINT_DDR_DQ signals from t_ddr_sanity testcase
  `define DDR_SPICE_PRINT_DDR_DQ                    // PRINT_DDR_DQ signals from t_ddr_sanity testcase
  `define DDR_SPICE_PRINT_DDR_CA                    // PRINT_DDR CA signals from t_ddr_sanity testcase

  `define DDR_SPICE_VCD_DDR_DQ                      // Enable VCD dump for DQ in t_ddr_sanity testcase
                                                    // (cannot be enabled with DDR_SIGNAL_VCD_DDR_CA enabled)
  `define DDR_SPICE_VCD_DDR_CA                      // Enable VCD dump for CA in t_ddr_sanity testcase
                                                    // (cannot be enabled with DDR_SIGNAL_VCD_DDR_DQ enabled)
`endif

// ------------------------------------------------------------------------
// Trace Defines
// ------------------------------------------------------------------------

//`define DDR_TRACE                                 // Enable TRACE VCD dump

// ------------------------------------------------------------------------
// ECO Defines
// ------------------------------------------------------------------------

//`define DDR_ENABLE_RX_SDRLPDE_SMALL               // Enable for synth and disabled for SIMS for now.
  `define DDR_ECO_PHASE_EXTENDER_VLD_PHASES         // Bug fix in phase extension logic to check only valid phases while extending phases.
  `define DDR_ECO_CM_TSTCLK_DRVR_UPSIZE             // Upsize second inverter to D8 on tst clocks.
  `define DDR_ECO_MCWRAP_CMD_AND_DATACS_CON_FIX     // MC wrapper command bus connections and wrdata/rdata_cs connection fix.
  `define DDR_ECO_RXFIFO_RD_FIX
  `define DDR_ECO_RXFIFO_HOLD_FIX                   //delay cell library path needed.

  // ECO POST NETLIST FREEZE
  `define DDR_ECO_AHB_CDIV_EN_DEMET_TYPE
  `define DDR_ECO_ANA_REF_CLK
  `define DDR_ECO_CM_RX_CLK

// ------------------------------------------------------------------------
// Common to SIMULATION and SYNTHESIS
// ------------------------------------------------------------------------
//`define DDR_CLIB                                  // Enable Custom library
//`define DDR_CLIB_WAV8LPU                          // 8LPU Custom library
//`define DDR_CLIB_WAV12FFC
//`define DDR_SLIB_TSMC12FFC                        // 12FFC Stdcell library // FXIME
//`define WAV_SLIB_TSMC12FFC
//`define WAV_SLIB_GF12LPP                          // 12LPP Stdcell library
//`define DDR_SLIB_GF12LPP                          // 12LPP Stdcell library
//`define DDR_CLIB_WAV12LPP                         // 12LPP Custom library
//`define WAV_RAM_GF12LPP                           // 12LPP Memory library
//`define WAV_RAM_TSMC12FFC                         // 12FFC Memory library

// ------------------------------------------------------------------------
// General Defines
// ------------------------------------------------------------------------

//`define DDR_BEHAV                                 // Enable STDCELL behavioral code
//`define DDR_IO_WRAPPER_BEHAV                      // Enable IO wrapper behavioral code
  `define DDR_PI_WRAPPER_BEHAV                      // Enable PI_wrapper behavioral code
//`define DDR_JTAG_BEHAV                            // Enable JTAG behavioral code
//`define DDR_2TO1_BEHAV                            // Enable 2to1 behavioral code
//`define DDR_LPDE_BEHAV                            // Enable LPDE behavioral code
//`define DDR_PAD_TX_BEHAV                          // Enable pad behavioral code
//`define DDR_PAD_RX_BEHAV                          // Enable pad behavioral code
//`define DDR_SA_BEHAV                              // Enable Sense Amp behavioral code
//`define DDR_DIV_2PH_BEHAV                         // Enable Clock Divider behavioral code
//`define DDR_DIV_4PH_BEHAV                         // Enable Clock Divider behavioral code
//`define DDR_CGC_BEHAV                             // Enable Clock gating behavioral code
//`define DDR_DP_PULSE_EXT_BEHAV                    // Enable DP pulse ext behavioral code
//`define DDR_IO_PULL                               // Enable IO pulls
//`define DDR_LATCH_BASED_CDIV                      // Enable latched-based CDIV in component library
  `define DDR_LPDE_SE                               // Enable single-ended LPDE
  `define DDR_PI_MODULE                             // Enable Phase Interpolator block
  `define DDR_PI_CSR_DEC                            // Enable PI decode logic in the CSR wrapper (saves custom area)
//`define DDR_DQS_VREF                              // Enable DQS local VREF module
//`define DDR_DQS_PDA                               // Enable DQS PDA module
  `define DDR_SER_4TO1_NEGEDGE                      // Timing to 4to1 mux is from negative edge
  `define DDR_DP_CGC_RL                             // Enable datapath rest-low vs rest-high cgc
//`define DDR_RCS_PI_SMALL                          // Enable small (T/32) PI
//`define DDR_REN_PI_SMALL                          // Enable small (T/32) PI
  `define DDR_PI_MATCH_EN                           // Enable PI matching cells

// ------------------------------------------------------------------------
// Cadence Memory Controller Defines
// ------------------------------------------------------------------------

//`define CADENCE_MC_LP4                            // Enable Cadence LPDDR4 Memory Controller (default is LPDDR5)
//`define CADENCE_MC_CGC_BEHAV                      // Enable Cadence behavioral CGC

// ------------------------------------------------------------------------
// Analog Model Defines
// ------------------------------------------------------------------------

//`define WPIN_UART_EN                              // Enable analog UART "real" type communication
//`define WPIN_EN

//`define MVP_FORCE_PLL <freq>                      // Command line >> +MVP_FORCE_PLL=%f
                                                    //    Where %f is the freq (in Hz) you want the
                                                    //    VCO0 to generate (400MHz probably). When
                                                    //    you set this plusarg the VCOs will have
                                                    //    no conception of the PLL, they will just
                                                    //    be dumb clock generators. VCO0 will only
                                                    //    ever generate the clock freq you passed
                                                    //    on the plusarg. VCO1/2 will go based on
                                                    //    the band which is the same as what you had
                                                    //    before.

                                                    //    To get the clock outputs:
                                                    //    -Clear the PLL reset (clr_reset)
                                                    //    -Set the respective VCO band (set_band)
                                                    //    -Enable the respective VCO (en_vco)

// ------------------------------------------------------------------------
// DFT - FREQ EN Defines
// ------------------------------------------------------------------------

  `define DDR_FREQ_EN_REFCLK          0
  `define DDR_FREQ_EN_MCUCLK          0
  `define DDR_FREQ_EN_AHBEXTCLK       1
  `define DDR_FREQ_EN_AHBCLK          1
  `define DDR_FREQ_EN_FSW             2
  `define DDR_FREQ_EN_CMN             3
  `define DDR_FREQ_EN_DFICH           4

// ------------------------------------------------------------------------
// Slice Assignment Defines - (Update $include/ddr_project_vpp.vhh too)
// ------------------------------------------------------------------------

  // DQS
  `define DDR_DQS_RCS_IDX             DQS_WIDTH-1   // 8
  `define DDR_DQS_WCS_IDX             DQS_WIDTH-2   // 7
  `define DDR_DQS_WCK_OE_IDX          DQS_WIDTH-3   // 6
  `define DDR_DQS_RE_IDX              DQS_WIDTH-4   // 5
  `define DDR_DQS_IE_IDX              DQS_WIDTH-5   // 4
  `define DDR_DQS_OE_IDX              DQS_WIDTH-6   // 3
  `define DDR_DQS_REN_IDX             DQS_WIDTH-7   // 2
  `define DDR_DQS_DQS_IDX             DQS_WIDTH-8   // 1
  `define DDR_DQS_WCK_IDX             DQS_WIDTH-9   // 0

  // DQ
  `define DDR_DQ_DBI_IDX              DQ_WIDTH-1
  `define DDR_DQ_DATA_IDX             DQ_WIDTH-2

  // CK
  `define DDR_CA_CK_IDX               DQS_WIDTH-9

  // CA
  `define DDR_CA_CKE_1_IDX            CA_WIDTH-1
  `define DDR_CA_CKE_0_IDX            CA_WIDTH-2
  `define DDR_CA_CS_1_IDX             CA_WIDTH-3
  `define DDR_CA_CS_0_IDX             CA_WIDTH-4
  `define DDR_CA_CA_IDX               CA_WIDTH-5

// ------------------------------------------------------------------------
// TX Egress Path Assignment Defines (DIG)
// ------------------------------------------------------------------------

  `define DDR_DIG_EGRESS_SDR          0
  `define DDR_DIG_EGRESS_DDR_2TO1     1
  `define DDR_DIG_EGRESS_QDR_2TO1     2
  `define DDR_DIG_EGRESS_ODR_2TO1     3
  `define DDR_DIG_EGRESS_QDR_4TO1     4
  `define DDR_DIG_EGRESS_ODR_4TO1     5
  `define DDR_DIG_EGRESS_BSCAN        6

// ------------------------------------------------------------------------
// TX Egress Path Assignment Defines (ANA)
// ------------------------------------------------------------------------

  `define DDR_ANA_EGRESS_BYPASS       0
  `define DDR_ANA_EGRESS_DDR_2TO1     1
  `define DDR_ANA_EGRESS_QDR_2TO1     2
  `define DDR_ANA_EGRESS_ODR_2TO1     3
  `define DDR_ANA_EGRESS_QDR_4TO1     4
  `define DDR_ANA_EGRESS_ODR_4TO1     5

// ------------------------------------------------------------------------
// DGB Mode bus Index
// ------------------------------------------------------------------------

  `define DGB_8TO1_HF_IDX            7
  `define DGB_8TO1_LF_IDX            6
  `define DGB_4TO1_IR_IDX            5
  `define DGB_4TO1_HF_IDX            4
  `define DGB_4TO1_LF_IDX            3
  `define DGB_2TO1_IR_IDX            2
  `define DGB_2TO1_HF_IDX            1
  `define DGB_1TO1_HF_IDX            0

  `define FGB_8TO16_IDX              10
  `define FGB_8TO8_IDX               9
  `define FGB_4TO8_IDX               8
  `define FGB_4TO4_IDX               7
  `define FGB_2TO8_IDX               6
  `define FGB_2TO4_IDX               5
  `define FGB_2TO2_IDX               4
  `define FGB_1TO8_IDX               3
  `define FGB_1TO4_IDX               2
  `define FGB_1TO2_IDX               1
  `define FGB_1TO1_IDX               0

  `define WGB_16TO8_IDX              10
  `define WGB_8TO8_IDX               9
  `define WGB_8TO4_IDX               8
  `define WGB_4TO4_IDX               7
  `define WGB_8TO2_IDX               6
  `define WGB_4TO2_IDX               5
  `define WGB_2TO2_IDX               4
  `define WGB_8TO1_IDX               3
  `define WGB_4TO1_IDX               2
  `define WGB_2TO1_IDX               1
  `define WGB_1TO1_IDX               0

  `define CK2WCK_1TO1_IDX            0
  `define CK2WCK_1TO2_IDX            1
  `define CK2WCK_1TO4_IDX            2

  `define DFIRGB_16TO32_IDX          9
  `define DFIRGB_8TO32_IDX           8
  `define DFIRGB_8TO16_IDX           7
  `define DFIRGB_8TO8_IDX            6
  `define DFIRGB_4TO8_IDX            5
  `define DFIRGB_4TO4_IDX            4
  `define DFIRGB_2TO8_IDX            3
  `define DFIRGB_2TO4_IDX            2
  `define DFIRGB_2TO2_IDX            1
  `define DFIRGB_1TO1_IDX            0

  `define DFIWGB_32TO16_IDX          8
  `define DFIWGB_32TO8_IDX           7
  `define DFIWGB_16TO8_IDX           6
  `define DFIWGB_8TO8_IDX            5
  `define DFIWGB_8TO4_IDX            4
  `define DFIWGB_8TO2_IDX            3
  `define DFIWGB_4TO4_IDX            2
  `define DFIWGB_4TO2_IDX            1
  `define DFIWGB_2TO2_IDX            0

// ------------------------------------------------------------------------
// IRQ
// ------------------------------------------------------------------------

  /* IRQ MAP
  ----------------------------------------------------------------------
  BIT 31    (1)  irq_nm_i       : Non-maskable interrupt (NMI)
  BIT 30:16 (15) irq_fast_i     : Fast, local interrupts
  BIT 11    (1)  irq_external_i : Connected to platform-level interrupt
                                  controller
  BIT 7     (1)  irq_timer_i    : Connected to timer module
  BIT 3     (1)  irq_software_i : Connected to memory-mapped (inter-
                                  processor) interrupt register
  */

  // FAST [30:16]
  `define DDR_IRQ_HOST2MCU_MSG_REQ_IDX      0      // 16
  `define DDR_IRQ_MCU2HOST_MSG_ACK_IDX      1      // 17
  `define DDR_IRQ_IBUF_IDX                  2      // 18
  `define DDR_IRQ_EBUF_IDX                  3      // 19
  `define DDR_IRQ_INIT_START_IDX            4      // 20
  `define DDR_IRQ_INIT_COMPLETE_IDX         5      // 21
  `define DDR_IRQ_LP_REQ                    6      // 22
  `define DDR_IRQ_PLL_IDX                   7      // 23
  `define DDR_IRQ_EXT_0_IDX                 8      // 24
  `define DDR_IRQ_EXT_1_IDX                 9      // 25
  `define DDR_IRQ_CTRLUPD_REQ_IDX           10     // 26
  `define DDR_IRQ_PHYUPD_ACK_IDX            11     // 27
  `define DDR_IRQ_PHYMSTR_ACK_IDX           12     // 28
  `define DDR_IRQ_AHB_ADR_DET_IDX           13     // 29
  `define DDR_IRQ_CH1_IDX                   14     // 30

  `define DDR_INT_IRQ_HOST2MCU_MSG_REQ_IDX  0
  `define DDR_INT_IRQ_MCU2HOST_MSG_ACK_IDX  1
  `define DDR_INT_IRQ_CH0_IBUF_EMPTY_IDX    2
  `define DDR_INT_IRQ_CH0_IBUF_FULL_IDX     3
  `define DDR_INT_IRQ_CH0_EBUF_EMPTY_N_IDX  4
  `define DDR_INT_IRQ_CH0_EBUF_FULL_IDX     5
  `define DDR_INT_IRQ_INIT_START_IDX        6
  `define DDR_INT_IRQ_INIT_COMPLETE_IDX     7
  `define DDR_INT_IRQ_LP_DATA_REQ           8
  `define DDR_INT_IRQ_LP_CTRL_REQ           9
  `define DDR_INT_IRQ_PLL_IDX               10
  `define DDR_INT_IRQ_EXT_0_IDX             11
  `define DDR_INT_IRQ_EXT_1_IDX             12
  `define DDR_INT_IRQ_CTRLUPD_REQ_IDX       13
  `define DDR_INT_IRQ_CTRLUPD_REQ_LOW_IDX   14
  `define DDR_INT_IRQ_PHYUPD_ACK_IDX        15
  `define DDR_INT_IRQ_PHYMSTR_ACK_IDX       16
  `define DDR_INT_IRQ_AHB_ADR_DET_0_IDX     17
  `define DDR_INT_IRQ_AHB_ADR_DET_1_IDX     18
  `define DDR_INT_IRQ_CH1_0_IDX             19
  `define DDR_INT_IRQ_CH1_1_IDX             20
  `define DDR_INT_IRQ_CH0_IBUF_OVERFLOW_IDX 21
  `define DDR_INT_IRQ_CH0_EBUF_OVERFLOW_IDX 22
  `define DDR_INT_IRQ_CH1_IBUF_EMPTY_IDX    23
  `define DDR_INT_IRQ_CH1_IBUF_FULL_IDX     24
  `define DDR_INT_IRQ_CH1_EBUF_EMPTY_N_IDX  25
  `define DDR_INT_IRQ_CH1_EBUF_FULL_IDX     26
  `define DDR_INT_IRQ_CH1_IBUF_OVERFLOW_IDX 27
  `define DDR_INT_IRQ_CH1_EBUF_OVERFLOW_IDX 28

  `define DDR_NUM_IRQ                       29   //NUM of IRQ. Max number of IRQ supported = 32
  `define DDR_IRQ_SYNC_EN                   29'h00000403
  `define DDR_IRQ_EDGE_EN                   29'h1FFFFBFC

// ------------------------------------------------------------------------
// General Purpose Bus (GPB)
// ------------------------------------------------------------------------

  `define DDR_GPB_CSP_PI_EN_IDX             0
  `define DDR_GPB_CSP_DIV_RST_N_IDX         1
  `define DDR_GPB_SWITCH_DONE_IDX           2
