#  NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
#  This is an automatically generated file by alain on Sun 21 Mar 2021 10:35:18 AM -10
# 
#  cmd:    swerv -target=default -set iccm_enable 
# 
# To use this in a perf script, use 'require $RV_ROOT/configs/config.pl'
# Reference the hash via $config{name}..


%config = (
            'testbench' => {
                             'assert_on' => '',
                             'clock_period' => '100',
                             'lderr_rollback' => '1',
                             'CPU_TOP' => '`RV_TOP.swerv',
                             'SDVT_AHB' => '1',
                             'datawidth' => '64',
                             'TOP' => 'tb_top',
                             'ext_addrwidth' => '32',
                             'ext_datawidth' => '64',
                             'build_axi4' => '1',
                             'sterr_rollback' => '0',
                             'RV_TOP' => '`TOP.rvtop'
                           },
            'core' => {
                        'fpga_optimize' => 1,
                        'dma_buf_depth' => '4',
                        'dec_instbuf_depth' => '4',
                        'lsu_num_nbload' => '8',
                        'lsu_num_nbload_width' => '3',
                        'lsu_stbuf_depth' => '8'
                      },
            'verilator' => '',
            'nmi_vec' => '0x11110000',
            'icache' => {
                          'icache_tag_low' => '6',
                          'icache_enable' => '1',
                          'icache_ic_depth' => 8,
                          'icache_ic_rows' => '256',
                          'icache_tag_high' => 12,
                          'icache_ic_index' => 8,
                          'icache_tag_depth' => 64,
                          'icache_taddr_high' => 5,
                          'icache_data_cell' => 'ram_256x34',
                          'icache_size' => 16,
                          'icache_tag_cell' => 'ram_64x21'
                        },
            'iccm' => {
                        'iccm_sadr' => '0xee000000',
                        'iccm_size' => 512,
                        'iccm_region' => '0xe',
                        'iccm_bank_bits' => 3,
                        'iccm_rows' => '16384',
                        'iccm_bits' => 19,
                        'iccm_num_banks' => '8',
                        'iccm_index_bits' => 14,
                        'iccm_offset' => '0xe000000',
                        'iccm_reserved' => '0x1000',
                        'iccm_num_banks_8' => '',
                        'iccm_data_cell' => 'ram_16384x39',
                        'iccm_enable' => 1,
                        'iccm_eadr' => '0xee07ffff',
                        'iccm_size_512' => ''
                      },
            'xlen' => 32,
            'numiregs' => '32',
            'bht' => {
                       'bht_hash_string' => '{ghr[3:2] ^ {ghr[3+1], {4-1-2{1\'b0} } },hashin[5:4]^ghr[2-1:0]}',
                       'bht_ghr_pad' => 'fghr[4],3\'b0',
                       'bht_ghr_size' => 5,
                       'bht_addr_lo' => '4',
                       'bht_ghr_pad2' => 'fghr[4:3],2\'b0',
                       'bht_ghr_range' => '4:0',
                       'bht_addr_hi' => 7,
                       'bht_size' => 128,
                       'bht_array_depth' => 16
                     },
            'reset_vec' => '0x80000000',
            'triggers' => [
                            {
                              'poke_mask' => [
                                               '0x081818c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ],
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ],
                              'mask' => [
                                          '0x081818c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ]
                            },
                            {
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ],
                              'poke_mask' => [
                                               '0x081810c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ],
                              'mask' => [
                                          '0x081810c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ]
                            },
                            {
                              'mask' => [
                                          '0x081818c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ],
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ],
                              'poke_mask' => [
                                               '0x081818c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ]
                            },
                            {
                              'mask' => [
                                          '0x081810c7',
                                          '0xffffffff',
                                          '0x00000000'
                                        ],
                              'poke_mask' => [
                                               '0x081810c7',
                                               '0xffffffff',
                                               '0x00000000'
                                             ],
                              'reset' => [
                                           '0x23e00000',
                                           '0x00000000',
                                           '0x00000000'
                                         ]
                            }
                          ],
            'tec_rv_icg' => 'clockhdr',
            'protection' => {
                              'inst_access_enable7' => '0x0',
                              'inst_access_addr3' => '0x00000000',
                              'inst_access_mask4' => '0xffffffff',
                              'data_access_addr2' => '0x00000000',
                              'data_access_enable4' => '0x0',
                              'data_access_addr5' => '0x00000000',
                              'inst_access_enable1' => '0x0',
                              'inst_access_mask0' => '0xffffffff',
                              'inst_access_mask6' => '0xffffffff',
                              'data_access_enable3' => '0x0',
                              'data_access_enable5' => '0x0',
                              'inst_access_mask7' => '0xffffffff',
                              'data_access_enable2' => '0x0',
                              'data_access_enable6' => '0x0',
                              'inst_access_mask1' => '0xffffffff',
                              'inst_access_mask3' => '0xffffffff',
                              'inst_access_addr4' => '0x00000000',
                              'data_access_mask2' => '0xffffffff',
                              'data_access_mask5' => '0xffffffff',
                              'inst_access_enable0' => '0x0',
                              'inst_access_addr7' => '0x00000000',
                              'inst_access_addr1' => '0x00000000',
                              'inst_access_addr0' => '0x00000000',
                              'inst_access_addr6' => '0x00000000',
                              'data_access_addr6' => '0x00000000',
                              'data_access_addr0' => '0x00000000',
                              'data_access_addr1' => '0x00000000',
                              'data_access_enable0' => '0x0',
                              'data_access_addr7' => '0x00000000',
                              'inst_access_mask2' => '0xffffffff',
                              'inst_access_mask5' => '0xffffffff',
                              'data_access_addr4' => '0x00000000',
                              'data_access_mask3' => '0xffffffff',
                              'inst_access_enable6' => '0x0',
                              'data_access_mask1' => '0xffffffff',
                              'inst_access_enable2' => '0x0',
                              'data_access_mask7' => '0xffffffff',
                              'inst_access_enable5' => '0x0',
                              'data_access_mask6' => '0xffffffff',
                              'inst_access_enable3' => '0x0',
                              'data_access_enable1' => '0x0',
                              'data_access_mask0' => '0xffffffff',
                              'inst_access_addr2' => '0x00000000',
                              'inst_access_enable4' => '0x0',
                              'inst_access_addr5' => '0x00000000',
                              'data_access_enable7' => '0x0',
                              'data_access_mask4' => '0xffffffff',
                              'data_access_addr3' => '0x00000000'
                            },
            'physical' => '1',
            'dccm' => {
                        'dccm_eadr' => '0xf004ffff',
                        'dccm_fdata_width' => 39,
                        'dccm_data_width' => 32,
                        'dccm_data_cell' => 'ram_2048x39',
                        'dccm_width_bits' => 2,
                        'dccm_num_banks_8' => '',
                        'dccm_reserved' => '0x1000',
                        'dccm_size_64' => '',
                        'dccm_num_banks' => '8',
                        'dccm_ecc_width' => 7,
                        'dccm_bank_bits' => 3,
                        'dccm_size' => 64,
                        'dccm_sadr' => '0xf0040000',
                        'dccm_byte_width' => '4',
                        'dccm_enable' => '1',
                        'dccm_index_bits' => 11,
                        'dccm_offset' => '0x40000',
                        'lsu_sb_bits' => 16,
                        'dccm_bits' => 16,
                        'dccm_rows' => '2048',
                        'dccm_region' => '0xf'
                      },
            'even_odd_trigger_chains' => 'true',
            'memmap' => {
                          'serialio' => '0xd0580000',
                          'unused_region6' => '0x60000000',
                          'external_prog' => '0xb0000000',
                          'unused_region5' => '0x50000000',
                          'unused_region3' => '0x30000000',
                          'debug_sb_mem' => '0xb0580000',
                          'external_data' => '0xc0580000',
                          'unused_region9' => '0x90000000',
                          'external_data_1' => '0x00000000',
                          'unused_region0' => '0x00000000',
                          'unused_region7' => '0x70000000',
                          'unused_region1' => '0x10000000',
                          'unused_region4' => '0x40000000',
                          'consoleio' => '0xd0580000',
                          'unused_region2' => '0x20000000'
                        },
            'bus' => {
                       'lsu_bus_tag' => 4,
                       'dma_bus_tag' => '1',
                       'ifu_bus_tag' => '3',
                       'sb_bus_tag' => '1'
                     },
            'pic' => {
                       'pic_mpiccfg_mask' => '0x1',
                       'pic_meipt_count' => 8,
                       'pic_meigwctrl_mask' => '0x3',
                       'pic_bits' => 15,
                       'pic_total_int' => 8,
                       'pic_meigwctrl_offset' => '0x4000',
                       'pic_meigwclr_offset' => '0x5000',
                       'pic_region' => '0xf',
                       'pic_meipl_offset' => '0x0000',
                       'pic_total_int_plus1' => 9,
                       'pic_meigwclr_count' => 8,
                       'pic_meipt_mask' => '0x0',
                       'pic_int_words' => 1,
                       'pic_meip_count' => 4,
                       'pic_meie_count' => 8,
                       'pic_meipl_mask' => '0xf',
                       'pic_mpiccfg_count' => 1,
                       'pic_meie_offset' => '0x2000',
                       'pic_meip_offset' => '0x1000',
                       'pic_meigwctrl_count' => 8,
                       'pic_meip_mask' => '0x0',
                       'pic_meie_mask' => '0x1',
                       'pic_base_addr' => '0xf00c0000',
                       'pic_meipl_count' => 8,
                       'pic_size' => 32,
                       'pic_meigwclr_mask' => '0x0',
                       'pic_offset' => '0xc0000',
                       'pic_meipt_offset' => '0x3004',
                       'pic_mpiccfg_offset' => '0x3000'
                     },
            'btb' => {
                       'btb_addr_hi' => 5,
                       'btb_btag_fold' => 1,
                       'btb_array_depth' => 4,
                       'btb_addr_lo' => '4',
                       'btb_index3_lo' => 8,
                       'btb_index1_lo' => '4',
                       'btb_index3_hi' => 9,
                       'btb_index1_hi' => 5,
                       'btb_size' => 32,
                       'btb_index2_hi' => 7,
                       'btb_index2_lo' => 6,
                       'btb_btag_size' => 9
                     },
            'max_mmode_perf_event' => '50',
            'num_mmode_perf_regs' => '4',
            'retstack' => {
                            'ret_stack_size' => '4'
                          },
            'harts' => 1,
            'regwidth' => '32',
            'csr' => {
                       'pmpaddr9' => {
                                       'exists' => 'false'
                                     },
                       'mhpmevent3' => {
                                         'reset' => '0x0',
                                         'exists' => 'true',
                                         'mask' => '0xffffffff'
                                       },
                       'mhpmevent4' => {
                                         'reset' => '0x0',
                                         'exists' => 'true',
                                         'mask' => '0xffffffff'
                                       },
                       'mcpc' => {
                                   'reset' => '0x0',
                                   'number' => '0x7c2',
                                   'mask' => '0x0',
                                   'exists' => 'true'
                                 },
                       'mhpmcounter4' => {
                                           'exists' => 'true',
                                           'mask' => '0xffffffff',
                                           'reset' => '0x0'
                                         },
                       'mitctl0' => {
                                      'number' => '0x7d4',
                                      'reset' => '0x1',
                                      'mask' => '0x00000007',
                                      'exists' => 'true'
                                    },
                       'mgpmc' => {
                                    'mask' => '0x1',
                                    'exists' => 'true',
                                    'reset' => '0x1',
                                    'number' => '0x7d0'
                                  },
                       'mhpmcounter6' => {
                                           'reset' => '0x0',
                                           'exists' => 'true',
                                           'mask' => '0xffffffff'
                                         },
                       'pmpcfg2' => {
                                      'exists' => 'false'
                                    },
                       'mcgc' => {
                                   'exists' => 'true',
                                   'mask' => '0x000001ff',
                                   'number' => '0x7f8',
                                   'reset' => '0x0',
                                   'poke_mask' => '0x000001ff'
                                 },
                       'tselect' => {
                                      'reset' => '0x0',
                                      'mask' => '0x3',
                                      'exists' => 'true'
                                    },
                       'meicpct' => {
                                      'number' => '0xbca',
                                      'reset' => '0x0',
                                      'comment' => 'External claim id/priority capture.',
                                      'exists' => 'true',
                                      'mask' => '0x0'
                                    },
                       'pmpaddr15' => {
                                        'exists' => 'false'
                                      },
                       'pmpaddr10' => {
                                        'exists' => 'false'
                                      },
                       'dmst' => {
                                   'number' => '0x7c4',
                                   'debug' => 'true',
                                   'reset' => '0x0',
                                   'comment' => 'Memory synch trigger: Flush caches in debug mode.',
                                   'mask' => '0x0',
                                   'exists' => 'true'
                                 },
                       'time' => {
                                   'exists' => 'false'
                                 },
                       'meicurpl' => {
                                       'reset' => '0x0',
                                       'number' => '0xbcc',
                                       'mask' => '0xf',
                                       'exists' => 'true',
                                       'comment' => 'External interrupt current priority level.'
                                     },
                       'mhpmcounter3h' => {
                                            'reset' => '0x0',
                                            'mask' => '0xffffffff',
                                            'exists' => 'true'
                                          },
                       'mitbnd1' => {
                                      'mask' => '0xffffffff',
                                      'exists' => 'true',
                                      'number' => '0x7d6',
                                      'reset' => '0xffffffff'
                                    },
                       'mstatus' => {
                                      'reset' => '0x1800',
                                      'mask' => '0x88',
                                      'exists' => 'true'
                                    },
                       'dicago' => {
                                     'reset' => '0x0',
                                     'debug' => 'true',
                                     'number' => '0x7cb',
                                     'exists' => 'true',
                                     'mask' => '0x0',
                                     'comment' => 'Cache diagnostics.'
                                   },
                       'pmpaddr6' => {
                                       'exists' => 'false'
                                     },
                       'mfdc' => {
                                   'mask' => '0x000727ff',
                                   'exists' => 'true',
                                   'reset' => '0x00070040',
                                   'number' => '0x7f9'
                                 },
                       'pmpaddr4' => {
                                       'exists' => 'false'
                                     },
                       'pmpaddr3' => {
                                       'exists' => 'false'
                                     },
                       'mdccmect' => {
                                       'reset' => '0x0',
                                       'number' => '0x7f2',
                                       'mask' => '0xffffffff',
                                       'exists' => 'true'
                                     },
                       'pmpcfg0' => {
                                      'exists' => 'false'
                                    },
                       'miccmect' => {
                                       'number' => '0x7f1',
                                       'reset' => '0x0',
                                       'mask' => '0xffffffff',
                                       'exists' => 'true'
                                     },
                       'mcountinhibit' => {
                                            'exists' => 'false'
                                          },
                       'mimpid' => {
                                     'reset' => '0x6',
                                     'mask' => '0x0',
                                     'exists' => 'true'
                                   },
                       'mhpmcounter5' => {
                                           'mask' => '0xffffffff',
                                           'exists' => 'true',
                                           'reset' => '0x0'
                                         },
                       'mitcnt0' => {
                                      'exists' => 'true',
                                      'mask' => '0xffffffff',
                                      'reset' => '0x0',
                                      'number' => '0x7d2'
                                    },
                       'pmpaddr12' => {
                                        'exists' => 'false'
                                      },
                       'pmpaddr7' => {
                                       'exists' => 'false'
                                     },
                       'pmpcfg3' => {
                                      'exists' => 'false'
                                    },
                       'pmpaddr14' => {
                                        'exists' => 'false'
                                      },
                       'mpmc' => {
                                   'exists' => 'true',
                                   'mask' => '0x2',
                                   'comment' => 'FWHALT',
                                   'reset' => '0x2',
                                   'poke_mask' => '0x2',
                                   'number' => '0x7c6'
                                 },
                       'pmpcfg1' => {
                                      'exists' => 'false'
                                    },
                       'mie' => {
                                  'reset' => '0x0',
                                  'exists' => 'true',
                                  'mask' => '0x70000888'
                                },
                       'pmpaddr0' => {
                                       'exists' => 'false'
                                     },
                       'mhpmcounter4h' => {
                                            'exists' => 'true',
                                            'mask' => '0xffffffff',
                                            'reset' => '0x0'
                                          },
                       'mip' => {
                                  'reset' => '0x0',
                                  'poke_mask' => '0x70000888',
                                  'exists' => 'true',
                                  'mask' => '0x0'
                                },
                       'mhpmcounter6h' => {
                                            'mask' => '0xffffffff',
                                            'exists' => 'true',
                                            'reset' => '0x0'
                                          },
                       'meipt' => {
                                    'comment' => 'External interrupt priority threshold.',
                                    'exists' => 'true',
                                    'mask' => '0xf',
                                    'number' => '0xbc9',
                                    'reset' => '0x0'
                                  },
                       'mitcnt1' => {
                                      'mask' => '0xffffffff',
                                      'exists' => 'true',
                                      'number' => '0x7d5',
                                      'reset' => '0x0'
                                    },
                       'dicad0' => {
                                     'comment' => 'Cache diagnostics.',
                                     'mask' => '0xffffffff',
                                     'exists' => 'true',
                                     'number' => '0x7c9',
                                     'debug' => 'true',
                                     'reset' => '0x0'
                                   },
                       'meicidpl' => {
                                       'number' => '0xbcb',
                                       'reset' => '0x0',
                                       'comment' => 'External interrupt claim id priority level.',
                                       'exists' => 'true',
                                       'mask' => '0xf'
                                     },
                       'mitbnd0' => {
                                      'number' => '0x7d3',
                                      'reset' => '0xffffffff',
                                      'exists' => 'true',
                                      'mask' => '0xffffffff'
                                    },
                       'pmpaddr11' => {
                                        'exists' => 'false'
                                      },
                       'misa' => {
                                   'mask' => '0x0',
                                   'exists' => 'true',
                                   'reset' => '0x40001104'
                                 },
                       'dicad1' => {
                                     'number' => '0x7ca',
                                     'reset' => '0x0',
                                     'debug' => 'true',
                                     'comment' => 'Cache diagnostics.',
                                     'exists' => 'true',
                                     'mask' => '0x3'
                                   },
                       'dicawics' => {
                                       'number' => '0x7c8',
                                       'debug' => 'true',
                                       'reset' => '0x0',
                                       'comment' => 'Cache diagnostics.',
                                       'mask' => '0x0130fffc',
                                       'exists' => 'true'
                                     },
                       'pmpaddr1' => {
                                       'exists' => 'false'
                                     },
                       'pmpaddr2' => {
                                       'exists' => 'false'
                                     },
                       'instret' => {
                                      'exists' => 'false'
                                    },
                       'pmpaddr5' => {
                                       'exists' => 'false'
                                     },
                       'mhpmcounter3' => {
                                           'reset' => '0x0',
                                           'mask' => '0xffffffff',
                                           'exists' => 'true'
                                         },
                       'mhpmevent6' => {
                                         'mask' => '0xffffffff',
                                         'exists' => 'true',
                                         'reset' => '0x0'
                                       },
                       'mvendorid' => {
                                        'reset' => '0x45',
                                        'exists' => 'true',
                                        'mask' => '0x0'
                                      },
                       'mhpmcounter5h' => {
                                            'reset' => '0x0',
                                            'exists' => 'true',
                                            'mask' => '0xffffffff'
                                          },
                       'pmpaddr8' => {
                                       'exists' => 'false'
                                     },
                       'marchid' => {
                                      'reset' => '0x0000000b',
                                      'mask' => '0x0',
                                      'exists' => 'true'
                                    },
                       'pmpaddr13' => {
                                        'exists' => 'false'
                                      },
                       'mhpmevent5' => {
                                         'reset' => '0x0',
                                         'exists' => 'true',
                                         'mask' => '0xffffffff'
                                       },
                       'mitctl1' => {
                                      'mask' => '0x00000007',
                                      'exists' => 'true',
                                      'reset' => '0x1',
                                      'number' => '0x7d7'
                                    },
                       'cycle' => {
                                    'exists' => 'false'
                                  },
                       'dcsr' => {
                                   'mask' => '0x00008c04',
                                   'exists' => 'true',
                                   'reset' => '0x40000003',
                                   'poke_mask' => '0x00008dcc'
                                 },
                       'micect' => {
                                     'exists' => 'true',
                                     'mask' => '0xffffffff',
                                     'number' => '0x7f0',
                                     'reset' => '0x0'
                                   },
                       'mcounteren' => {
                                         'exists' => 'false'
                                       }
                     },
            'target' => 'default'
          );
1;
