//===================================================================
//
// Created by sbridges on November/11/2020 at 05:25:06
//
// mvp_pll_addr_defines.vh
//
//===================================================================



`define MVP_PLL_CORE_OVERRIDES                                                 'h00000000
`define MVP_PLL_CORE_OVERRIDES__CORE_GFCM_SEL_MUX                                       6
`define MVP_PLL_CORE_OVERRIDES__CORE_GFCM_SEL                                           5
`define MVP_PLL_CORE_OVERRIDES__CORE_VCO_SEL_MUX                                        4
`define MVP_PLL_CORE_OVERRIDES__CORE_VCO_SEL                                          3:2
`define MVP_PLL_CORE_OVERRIDES__CORE_RESET_MUX                                          1
`define MVP_PLL_CORE_OVERRIDES__CORE_RESET                                              0
`define MVP_PLL_CORE_OVERRIDES___POR                                         32'h00000000

`define MVP_PLL_CORE_SWTICH_VCO                                                'h00000004
`define MVP_PLL_CORE_SWTICH_VCO__CORE_SWITCH_VCO                                        0
`define MVP_PLL_CORE_SWTICH_VCO___POR                                        32'h00000000

`define MVP_PLL_CORE_SWTICH_VCO_HW                                             'h00000008
`define MVP_PLL_CORE_SWTICH_VCO_HW__CORE_SWITCH_VCO_HW_MUX                              1
`define MVP_PLL_CORE_SWTICH_VCO_HW__CORE_SWITCH_VCO_HW                                  0
`define MVP_PLL_CORE_SWTICH_VCO_HW___POR                                     32'h00000000

`define MVP_PLL_CORE_STATUS                                                    'h0000000C
`define MVP_PLL_CORE_STATUS__FSM_STATE                                              24:21
`define MVP_PLL_CORE_STATUS__FREQ_DETECT_CYCLES                                      20:4
`define MVP_PLL_CORE_STATUS__FREQ_DETECT_LOCK                                           3
`define MVP_PLL_CORE_STATUS__CORE_INITIAL_SWITCH_DONE                                   2
`define MVP_PLL_CORE_STATUS__CORE_FASTLOCK_READY                                        1
`define MVP_PLL_CORE_STATUS__CORE_READY                                                 0
`define MVP_PLL_CORE_STATUS___POR                                            32'h00000000

`define MVP_PLL_CORE_STATUS_INT                                                'h00000010
`define MVP_PLL_CORE_STATUS_INT__VCO2_FLL_THRESHOLD                                     8
`define MVP_PLL_CORE_STATUS_INT__VCO2_FLL_LOCKED                                        7
`define MVP_PLL_CORE_STATUS_INT__VCO1_FLL_THRESHOLD                                     6
`define MVP_PLL_CORE_STATUS_INT__VCO1_FLL_LOCKED                                        5
`define MVP_PLL_CORE_STATUS_INT__VCO0_FLL_THRESHOLD                                     4
`define MVP_PLL_CORE_STATUS_INT__VCO0_FLL_LOCKED                                        3
`define MVP_PLL_CORE_STATUS_INT__INITIAL_SWITCH_DONE                                    2
`define MVP_PLL_CORE_STATUS_INT__CORE_LOCKED                                            1
`define MVP_PLL_CORE_STATUS_INT__LOSS_OF_LOCK                                           0
`define MVP_PLL_CORE_STATUS_INT___POR                                        32'h00000000

`define MVP_PLL_CORE_STATUS_INT_EN                                             'h00000014
`define MVP_PLL_CORE_STATUS_INT_EN__VCO2_FLL_THRESHOLD_INT_EN                           8
`define MVP_PLL_CORE_STATUS_INT_EN__VCO2_FLL_LOCKED_INT_EN                              7
`define MVP_PLL_CORE_STATUS_INT_EN__VCO1_FLL_THRESHOLD_INT_EN                           6
`define MVP_PLL_CORE_STATUS_INT_EN__VCO1_FLL_LOCKED_INT_EN                              5
`define MVP_PLL_CORE_STATUS_INT_EN__VCO0_FLL_THRESHOLD_INT_EN                           4
`define MVP_PLL_CORE_STATUS_INT_EN__VCO0_FLL_LOCKED_INT_EN                              3
`define MVP_PLL_CORE_STATUS_INT_EN__INITIAL_SWITCH_DONE_INT_EN                          2
`define MVP_PLL_CORE_STATUS_INT_EN__CORE_LOCKED_INT_EN                                  1
`define MVP_PLL_CORE_STATUS_INT_EN__LOSS_OF_LOCK_INT_EN                                 0
`define MVP_PLL_CORE_STATUS_INT_EN___POR                                     32'h00000000

`define MVP_PLL_VCO0_BAND                                                      'h00000018
`define MVP_PLL_VCO0_BAND__VCO0_FINE_MUX                                               14
`define MVP_PLL_VCO0_BAND__VCO0_FINE                                                 13:8
`define MVP_PLL_VCO0_BAND__RESERVED0                                                    7
`define MVP_PLL_VCO0_BAND__VCO0_BAND_MUX                                                6
`define MVP_PLL_VCO0_BAND__VCO0_BAND                                                  5:0
`define MVP_PLL_VCO0_BAND___POR                                              32'h00005F40

`define MVP_PLL_VCO0_CONTROL                                                   'h0000001C
`define MVP_PLL_VCO0_CONTROL__VCO0_BYP_CLK_SEL                                          2
`define MVP_PLL_VCO0_CONTROL__VCO0_ENA_MUX                                              1
`define MVP_PLL_VCO0_CONTROL__VCO0_ENA                                                  0
`define MVP_PLL_VCO0_CONTROL___POR                                           32'h00000000

`define MVP_PLL_VCO0_FLL_CONTROL1                                              'h00000020
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_LOCKED                                         28
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_TOO_SLOW_STATUS                                27
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_TOO_FAST_STATUS                                26
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_FLL_PERSISTENT_MODE                            25
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_FLL_BYPASS_FINE                                24
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_FLL_BYPASS_BAND                                23
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_LOCKED_COUNT_THRESHOLD                      22:19
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_USE_DEMETED_CHECK                              18
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_DELAY_COUNT                                 17:14
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_FINE_START                                   13:8
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_BAND_START                                    7:2
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_FLL_MANUAL_MODE                                 1
`define MVP_PLL_VCO0_FLL_CONTROL1__VCO0_FLL_ENABLE                                      0
`define MVP_PLL_VCO0_FLL_CONTROL1___POR                                      32'h02A49F7C

`define MVP_PLL_VCO0_FLL_CONTROL2                                              'h00000024
`define MVP_PLL_VCO0_FLL_CONTROL2__VCO0_FLL_RANGE                                   28:24
`define MVP_PLL_VCO0_FLL_CONTROL2__VCO0_FLL_VCO_COUNT_TARGET                         23:8
`define MVP_PLL_VCO0_FLL_CONTROL2__VCO0_FLL_REFCLK_COUNT                              7:0
`define MVP_PLL_VCO0_FLL_CONTROL2___POR                                      32'h0400D008

`define MVP_PLL_VCO0_FLL_CONTROL3                                              'h00000028
`define MVP_PLL_VCO0_FLL_CONTROL3__VCO0_FLL_BAND_THRESH                               5:0
`define MVP_PLL_VCO0_FLL_CONTROL3___POR                                      32'h0000003C

`define MVP_PLL_VCO0_FLL_BAND_STATUS                                           'h0000002C
`define MVP_PLL_VCO0_FLL_BAND_STATUS__VCO0_FINE_PREV_STATUS                         23:18
`define MVP_PLL_VCO0_FLL_BAND_STATUS__VCO0_FINE_STATUS                              17:12
`define MVP_PLL_VCO0_FLL_BAND_STATUS__VCO0_BAND_PREV_STATUS                          11:6
`define MVP_PLL_VCO0_FLL_BAND_STATUS__VCO0_BAND_STATUS                                5:0
`define MVP_PLL_VCO0_FLL_BAND_STATUS___POR                                   32'h00000000

`define MVP_PLL_VCO0_FLL_COUNT_STATUS                                          'h00000030
`define MVP_PLL_VCO0_FLL_COUNT_STATUS__VCO0_VCO_COUNT                                15:0
`define MVP_PLL_VCO0_FLL_COUNT_STATUS___POR                                  32'h00000000

`define MVP_PLL_VCO0_INT_FRAC_SETTINGS                                         'h00000034
`define MVP_PLL_VCO0_INT_FRAC_SETTINGS__VCO0_FRAC_EN_AUTO                              26
`define MVP_PLL_VCO0_INT_FRAC_SETTINGS__VCO0_FRAC_EN                                   25
`define MVP_PLL_VCO0_INT_FRAC_SETTINGS__VCO0_FRAC                                    24:9
`define MVP_PLL_VCO0_INT_FRAC_SETTINGS__VCO0_INT                                      8:0
`define MVP_PLL_VCO0_INT_FRAC_SETTINGS___POR                                 32'h0400000A

`define MVP_PLL_VCO0_PROP_GAINS                                                'h00000038
`define MVP_PLL_VCO0_PROP_GAINS__VCO0_PROP_GAIN                                       4:0
`define MVP_PLL_VCO0_PROP_GAINS___POR                                        32'h0000000A

`define MVP_PLL_VCO1_BAND                                                      'h0000003C
`define MVP_PLL_VCO1_BAND__VCO1_FINE_MUX                                               14
`define MVP_PLL_VCO1_BAND__VCO1_FINE                                                 13:8
`define MVP_PLL_VCO1_BAND__RESERVED0                                                    7
`define MVP_PLL_VCO1_BAND__VCO1_BAND_MUX                                                6
`define MVP_PLL_VCO1_BAND__VCO1_BAND                                                  5:0
`define MVP_PLL_VCO1_BAND___POR                                              32'h00000000

`define MVP_PLL_VCO1_CONTROL                                                   'h00000040
`define MVP_PLL_VCO1_CONTROL__VCO1_POST_DIV                                           4:3
`define MVP_PLL_VCO1_CONTROL__VCO1_BYP_CLK_SEL                                          2
`define MVP_PLL_VCO1_CONTROL__VCO1_ENA_MUX                                              1
`define MVP_PLL_VCO1_CONTROL__VCO1_ENA                                                  0
`define MVP_PLL_VCO1_CONTROL___POR                                           32'h00000000

`define MVP_PLL_VCO1_FLL_CONTROL1                                              'h00000044
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_LOCKED                                         28
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_TOO_SLOW_STATUS                                27
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_TOO_FAST_STATUS                                26
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_FLL_PERSISTENT_MODE                            25
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_FLL_BYPASS_FINE                                24
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_FLL_BYPASS_BAND                                23
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_LOCKED_COUNT_THRESHOLD                      22:19
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_USE_DEMETED_CHECK                              18
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_DELAY_COUNT                                 17:14
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_FINE_START                                   13:8
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_BAND_START                                    7:2
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_FLL_MANUAL_MODE                                 1
`define MVP_PLL_VCO1_FLL_CONTROL1__VCO1_FLL_ENABLE                                      0
`define MVP_PLL_VCO1_FLL_CONTROL1___POR                                      32'h00249F00

`define MVP_PLL_VCO1_FLL_CONTROL2                                              'h00000048
`define MVP_PLL_VCO1_FLL_CONTROL2__VCO1_FLL_RANGE                                   28:24
`define MVP_PLL_VCO1_FLL_CONTROL2__VCO1_FLL_VCO_COUNT_TARGET                         23:8
`define MVP_PLL_VCO1_FLL_CONTROL2__VCO1_FLL_REFCLK_COUNT                              7:0
`define MVP_PLL_VCO1_FLL_CONTROL2___POR                                      32'h0400D008

`define MVP_PLL_VCO1_FLL_CONTROL3                                              'h0000004C
`define MVP_PLL_VCO1_FLL_CONTROL3__VCO1_FLL_BAND_THRESH                               5:0
`define MVP_PLL_VCO1_FLL_CONTROL3___POR                                      32'h0000003C

`define MVP_PLL_VCO1_FLL_BAND_STATUS                                           'h00000050
`define MVP_PLL_VCO1_FLL_BAND_STATUS__VCO1_FINE_PREV_STATUS                         23:18
`define MVP_PLL_VCO1_FLL_BAND_STATUS__VCO1_FINE_STATUS                              17:12
`define MVP_PLL_VCO1_FLL_BAND_STATUS__VCO1_BAND_PREV_STATUS                          11:6
`define MVP_PLL_VCO1_FLL_BAND_STATUS__VCO1_BAND_STATUS                                5:0
`define MVP_PLL_VCO1_FLL_BAND_STATUS___POR                                   32'h00000000

`define MVP_PLL_VCO1_FLL_COUNT_STATUS                                          'h00000054
`define MVP_PLL_VCO1_FLL_COUNT_STATUS__VCO1_VCO_COUNT                                15:0
`define MVP_PLL_VCO1_FLL_COUNT_STATUS___POR                                  32'h00000000

`define MVP_PLL_VCO1_INT_FRAC_SETTINGS                                         'h00000058
`define MVP_PLL_VCO1_INT_FRAC_SETTINGS__VCO1_FRAC_EN_AUTO                              26
`define MVP_PLL_VCO1_INT_FRAC_SETTINGS__VCO1_FRAC_EN                                   25
`define MVP_PLL_VCO1_INT_FRAC_SETTINGS__VCO1_FRAC                                    24:9
`define MVP_PLL_VCO1_INT_FRAC_SETTINGS__VCO1_INT                                      8:0
`define MVP_PLL_VCO1_INT_FRAC_SETTINGS___POR                                 32'h0400000A

`define MVP_PLL_VCO1_PROP_GAINS                                                'h0000005C
`define MVP_PLL_VCO1_PROP_GAINS__VCO1_PROP_GAIN                                       4:0
`define MVP_PLL_VCO1_PROP_GAINS___POR                                        32'h0000000A

`define MVP_PLL_VCO1_SSC_CONTROLS                                              'h00000060
`define MVP_PLL_VCO1_SSC_CONTROLS__VCO1_SSC_CENTER_SPREAD                              29
`define MVP_PLL_VCO1_SSC_CONTROLS__VCO1_SSC_COUNT_CYCLES                               28
`define MVP_PLL_VCO1_SSC_CONTROLS__VCO1_SSC_AMP                                     27:11
`define MVP_PLL_VCO1_SSC_CONTROLS__VCO1_SSC_STEPSIZE                                 10:1
`define MVP_PLL_VCO1_SSC_CONTROLS__VCO1_SSC_ENABLE                                      0
`define MVP_PLL_VCO1_SSC_CONTROLS___POR                                      32'h00000000

`define MVP_PLL_VCO2_BAND                                                      'h00000064
`define MVP_PLL_VCO2_BAND__VCO2_FINE_MUX                                               14
`define MVP_PLL_VCO2_BAND__VCO2_FINE                                                 13:8
`define MVP_PLL_VCO2_BAND__RESERVED0                                                    7
`define MVP_PLL_VCO2_BAND__VCO2_BAND_MUX                                                6
`define MVP_PLL_VCO2_BAND__VCO2_BAND                                                  5:0
`define MVP_PLL_VCO2_BAND___POR                                              32'h00000000

`define MVP_PLL_VCO2_CONTROL                                                   'h00000068
`define MVP_PLL_VCO2_CONTROL__VCO2_POST_DIV                                           4:3
`define MVP_PLL_VCO2_CONTROL__VCO2_BYP_CLK_SEL                                          2
`define MVP_PLL_VCO2_CONTROL__VCO2_ENA_MUX                                              1
`define MVP_PLL_VCO2_CONTROL__VCO2_ENA                                                  0
`define MVP_PLL_VCO2_CONTROL___POR                                           32'h00000000

`define MVP_PLL_VCO2_FLL_CONTROL1                                              'h0000006C
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_LOCKED                                         28
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_TOO_SLOW_STATUS                                27
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_TOO_FAST_STATUS                                26
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_FLL_PERSISTENT_MODE                            25
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_FLL_BYPASS_FINE                                24
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_FLL_BYPASS_BAND                                23
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_LOCKED_COUNT_THRESHOLD                      22:19
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_USE_DEMETED_CHECK                              18
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_DELAY_COUNT                                 17:14
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_FINE_START                                   13:8
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_BAND_START                                    7:2
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_FLL_MANUAL_MODE                                 1
`define MVP_PLL_VCO2_FLL_CONTROL1__VCO2_FLL_ENABLE                                      0
`define MVP_PLL_VCO2_FLL_CONTROL1___POR                                      32'h00249F00

`define MVP_PLL_VCO2_FLL_CONTROL2                                              'h00000070
`define MVP_PLL_VCO2_FLL_CONTROL2__VCO2_FLL_RANGE                                   28:24
`define MVP_PLL_VCO2_FLL_CONTROL2__VCO2_FLL_VCO_COUNT_TARGET                         23:8
`define MVP_PLL_VCO2_FLL_CONTROL2__VCO2_FLL_REFCLK_COUNT                              7:0
`define MVP_PLL_VCO2_FLL_CONTROL2___POR                                      32'h0400D008

`define MVP_PLL_VCO2_FLL_CONTROL3                                              'h00000074
`define MVP_PLL_VCO2_FLL_CONTROL3__VCO2_FLL_BAND_THRESH                               5:0
`define MVP_PLL_VCO2_FLL_CONTROL3___POR                                      32'h0000003C

`define MVP_PLL_VCO2_FLL_BAND_STATUS                                           'h00000078
`define MVP_PLL_VCO2_FLL_BAND_STATUS__VCO2_FINE_PREV_STATUS                         23:18
`define MVP_PLL_VCO2_FLL_BAND_STATUS__VCO2_FINE_STATUS                              17:12
`define MVP_PLL_VCO2_FLL_BAND_STATUS__VCO2_BAND_PREV_STATUS                          11:6
`define MVP_PLL_VCO2_FLL_BAND_STATUS__VCO2_BAND_STATUS                                5:0
`define MVP_PLL_VCO2_FLL_BAND_STATUS___POR                                   32'h00000000

`define MVP_PLL_VCO2_FLL_COUNT_STATUS                                          'h0000007C
`define MVP_PLL_VCO2_FLL_COUNT_STATUS__VCO2_VCO_COUNT                                15:0
`define MVP_PLL_VCO2_FLL_COUNT_STATUS___POR                                  32'h00000000

`define MVP_PLL_VCO2_INT_FRAC_SETTINGS                                         'h00000080
`define MVP_PLL_VCO2_INT_FRAC_SETTINGS__VCO2_FRAC_EN_AUTO                              26
`define MVP_PLL_VCO2_INT_FRAC_SETTINGS__VCO2_FRAC_EN                                   25
`define MVP_PLL_VCO2_INT_FRAC_SETTINGS__VCO2_FRAC                                    24:9
`define MVP_PLL_VCO2_INT_FRAC_SETTINGS__VCO2_INT                                      8:0
`define MVP_PLL_VCO2_INT_FRAC_SETTINGS___POR                                 32'h0400000A

`define MVP_PLL_VCO2_PROP_GAINS                                                'h00000084
`define MVP_PLL_VCO2_PROP_GAINS__VCO2_PROP_GAIN                                       4:0
`define MVP_PLL_VCO2_PROP_GAINS___POR                                        32'h0000000A

`define MVP_PLL_VCO2_SSC_CONTROLS                                              'h00000088
`define MVP_PLL_VCO2_SSC_CONTROLS__VCO2_SSC_CENTER_SPREAD                              29
`define MVP_PLL_VCO2_SSC_CONTROLS__VCO2_SSC_COUNT_CYCLES                               28
`define MVP_PLL_VCO2_SSC_CONTROLS__VCO2_SSC_AMP                                     27:11
`define MVP_PLL_VCO2_SSC_CONTROLS__VCO2_SSC_STEPSIZE                                 10:1
`define MVP_PLL_VCO2_SSC_CONTROLS__VCO2_SSC_ENABLE                                      0
`define MVP_PLL_VCO2_SSC_CONTROLS___POR                                      32'h00000000

`define MVP_PLL_STATE_MACHINE_CONTROLS                                         'h0000008C
`define MVP_PLL_STATE_MACHINE_CONTROLS__FLL_INITIAL_SETTLE                          24:21
`define MVP_PLL_STATE_MACHINE_CONTROLS__DISABLE_LOCK_DET_AFTER_LOCK                    20
`define MVP_PLL_STATE_MACHINE_CONTROLS__SWITCH_COUNT                                19:16
`define MVP_PLL_STATE_MACHINE_CONTROLS__PRE_LOCKING_COUNT                            15:8
`define MVP_PLL_STATE_MACHINE_CONTROLS__BIAS_SETTLE_COUNT                             7:0
`define MVP_PLL_STATE_MACHINE_CONTROLS___POR                                 32'h00810408

`define MVP_PLL_STATE_MACHINE_CONTROLS2                                        'h00000090
`define MVP_PLL_STATE_MACHINE_CONTROLS2__SWITCH_2_TIME                              23:16
`define MVP_PLL_STATE_MACHINE_CONTROLS2__SWITCH_1_TIME                               15:8
`define MVP_PLL_STATE_MACHINE_CONTROLS2__SWITCH_RESET_TIME                            7:4
`define MVP_PLL_STATE_MACHINE_CONTROLS2__PRE_SWITCH_TIME                              3:0
`define MVP_PLL_STATE_MACHINE_CONTROLS2___POR                                32'h00010311

`define MVP_PLL_INTR_GAINS                                                     'h00000094
`define MVP_PLL_INTR_GAINS__NORMAL_INT_GAIN                                           4:0
`define MVP_PLL_INTR_GAINS___POR                                             32'h0000000F

`define MVP_PLL_INTR_PROP_FL_GAINS                                             'h00000098
`define MVP_PLL_INTR_PROP_FL_GAINS__FL_PROP_GAIN                                      9:5
`define MVP_PLL_INTR_PROP_FL_GAINS__FL_INT_GAIN                                       4:0
`define MVP_PLL_INTR_PROP_FL_GAINS___POR                                     32'h000003DE

`define MVP_PLL_INTR_PROP_GAINS_OVERRIDE                                       'h0000009C
`define MVP_PLL_INTR_PROP_GAINS_OVERRIDE__PROP_GAIN_MUX                                11
`define MVP_PLL_INTR_PROP_GAINS_OVERRIDE__PROP_GAIN                                  10:6
`define MVP_PLL_INTR_PROP_GAINS_OVERRIDE__INT_GAIN_MUX                                  5
`define MVP_PLL_INTR_PROP_GAINS_OVERRIDE__INT_GAIN                                    4:0
`define MVP_PLL_INTR_PROP_GAINS_OVERRIDE___POR                               32'h0000024F

`define MVP_PLL_LOCK_DET_SETTINGS                                              'h000000A0
`define MVP_PLL_LOCK_DET_SETTINGS__LD_RANGE                                         21:16
`define MVP_PLL_LOCK_DET_SETTINGS__LD_REFCLK_CYCLES                                  15:0
`define MVP_PLL_LOCK_DET_SETTINGS___POR                                      32'h00040200

`define MVP_PLL_FASTLOCK_DET_SETTINGS                                          'h000000A4
`define MVP_PLL_FASTLOCK_DET_SETTINGS__FASTLD_RANGE                                 21:16
`define MVP_PLL_FASTLOCK_DET_SETTINGS__FASTLD_REFCLK_CYCLES                          15:0
`define MVP_PLL_FASTLOCK_DET_SETTINGS___POR                                  32'h00080100

`define MVP_PLL_ANALOG_EN_RESET                                                'h000000A8
`define MVP_PLL_ANALOG_EN_RESET__VCO_SEL_MUX                                           16
`define MVP_PLL_ANALOG_EN_RESET__VCO_SEL                                            15:14
`define MVP_PLL_ANALOG_EN_RESET__FBDIV_SEL_MUX                                         13
`define MVP_PLL_ANALOG_EN_RESET__FBDIV_SEL                                           12:4
`define MVP_PLL_ANALOG_EN_RESET__PLL_RESET_MUX                                          3
`define MVP_PLL_ANALOG_EN_RESET__PLL_RESET                                              2
`define MVP_PLL_ANALOG_EN_RESET__PLL_EN_MUX                                             1
`define MVP_PLL_ANALOG_EN_RESET__PLL_EN                                                 0
`define MVP_PLL_ANALOG_EN_RESET___POR                                        32'h00000000

`define MVP_PLL_MODE_DTST_MISC                                                 'h000000AC
`define MVP_PLL_MODE_DTST_MISC__BIAS_SEL                                                8
`define MVP_PLL_MODE_DTST_MISC__DIV16EN                                                 7
`define MVP_PLL_MODE_DTST_MISC__EN_LOCK_DET_MUX                                         6
`define MVP_PLL_MODE_DTST_MISC__EN_LOCK_DET                                             5
`define MVP_PLL_MODE_DTST_MISC__CP_INT_MODE                                             4
`define MVP_PLL_MODE_DTST_MISC__BIAS_LVL                                              3:0
`define MVP_PLL_MODE_DTST_MISC___POR                                         32'h00000008

`define MVP_PLL_PROP_CTRLS                                                     'h000000B0
`define MVP_PLL_PROP_CTRLS__PROP_R_CTRL                                               3:2
`define MVP_PLL_PROP_CTRLS__PROP_C_CTRL                                               1:0
`define MVP_PLL_PROP_CTRLS___POR                                             32'h00000000

`define MVP_PLL_REFCLK_CONTROLS                                                'h000000B4
`define MVP_PLL_REFCLK_CONTROLS__SEL_REFCLK_ALT                                         2
`define MVP_PLL_REFCLK_CONTROLS__PFD_MODE                                             1:0
`define MVP_PLL_REFCLK_CONTROLS___POR                                        32'h00000000

`define MVP_PLL_CLKGATE_DISABLES                                               'h000000B8
`define MVP_PLL_CLKGATE_DISABLES__FORCE_VCO2_CLK_GATE                                   3
`define MVP_PLL_CLKGATE_DISABLES__FORCE_VCO1_CLK_GATE                                   2
`define MVP_PLL_CLKGATE_DISABLES__FORCE_VCO0_CLK_GATE                                   1
`define MVP_PLL_CLKGATE_DISABLES__FORCE_FBCLK_GATE                                      0
`define MVP_PLL_CLKGATE_DISABLES___POR                                       32'h00000000

`define MVP_PLL_DEBUG_BUS_CTRL                                                 'h000000BC
`define MVP_PLL_DEBUG_BUS_CTRL__DEBUG_BUS_CTRL_SEL                                    5:0
`define MVP_PLL_DEBUG_BUS_CTRL___POR                                         32'h00000000

`define MVP_PLL_DEBUG_BUS_STATUS                                               'h000000C0
`define MVP_PLL_DEBUG_BUS_STATUS__DEBUG_BUS_CTRL_STATUS                              31:0
`define MVP_PLL_DEBUG_BUS_STATUS___POR                                       32'h00000000

