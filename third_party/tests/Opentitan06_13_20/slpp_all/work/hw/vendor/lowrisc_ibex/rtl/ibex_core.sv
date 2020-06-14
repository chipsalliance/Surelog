// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0





// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions












































































































































/**
 * Top level module of the ibex RISC-V core
 */
module ibex_core #(
    parameter bit          PMPEnable                = 1'b0,
    parameter int unsigned PMPGranularity           = 0,
    parameter int unsigned PMPNumRegions            = 4,
    parameter int unsigned MHPMCounterNum           = 0,
    parameter int unsigned MHPMCounterWidth         = 40,
    parameter bit          RV32E                    = 1'b0,
    parameter bit          RV32M                    = 1'b1,
    parameter bit          RV32B                    = 1'b0,
    parameter bit          BranchTargetALU          = 1'b0,
    parameter bit          WritebackStage           = 1'b0,
    parameter              MultiplierImplementation = "fast",
    parameter bit          ICache                   = 1'b0,
    parameter bit          ICacheECC                = 1'b0,
    parameter bit          DbgTriggerEn             = 1'b0,
    parameter bit          SecureIbex               = 1'b0,
    parameter int unsigned DmHaltAddr               = 32'h1A110800,
    parameter int unsigned DmExceptionAddr          = 32'h1A110808
) (
    // Clock and Reset
    input  logic        clk_i,
    input  logic        rst_ni,

    input  logic        test_en_i,     // enable all clock gates for testing

    input  logic [31:0] hart_id_i,
    input  logic [31:0] boot_addr_i,

    // Instruction memory interface
    output logic        instr_req_o,
    input  logic        instr_gnt_i,
    input  logic        instr_rvalid_i,
    output logic [31:0] instr_addr_o,
    input  logic [31:0] instr_rdata_i,
    input  logic        instr_err_i,

    // Data memory interface
    output logic        data_req_o,
    input  logic        data_gnt_i,
    input  logic        data_rvalid_i,
    output logic        data_we_o,
    output logic [3:0]  data_be_o,
    output logic [31:0] data_addr_o,
    output logic [31:0] data_wdata_o,
    input  logic [31:0] data_rdata_i,
    input  logic        data_err_i,

    // Interrupt inputs
    input  logic        irq_software_i,
    input  logic        irq_timer_i,
    input  logic        irq_external_i,
    input  logic [14:0] irq_fast_i,
    input  logic        irq_nm_i,       // non-maskeable interrupt

    // Debug Interface
    input  logic        debug_req_i,

    // RISC-V Formal Interface
    // Does not comply with the coding standards of _i/_o suffixes, but follows
    // the convention of RISC-V Formal Interface Specification.


























    // CPU Control Signals
    input  logic        fetch_enable_i,
    output logic        core_sleep_o
);

  import ibex_pkg::*;

  localparam int unsigned PMP_NUM_CHAN      = 2;
  localparam bit          DataIndTiming     = SecureIbex;
  localparam bit          DummyInstructions = SecureIbex;
  // Speculative branch option, trades-off performance against timing.
  // Setting this to 1 eases branch target critical paths significantly but reduces performance
  // by ~3% (based on Coremark/MHz score).
  // Set by default in the max PMP config which has the tightest budget for branch target timing.
  localparam bit          SpecBranch        = PMPEnable & (PMPNumRegions == 16);

  // IF/ID signals
  logic        dummy_instr_id;
  logic        instr_valid_id;
  logic        instr_new_id;
  logic [31:0] instr_rdata_id;                 // Instruction sampled inside IF stage
  logic [31:0] instr_rdata_alu_id;             // Instruction sampled inside IF stage (replicated to ease
                                               // fan-out)
  logic [15:0] instr_rdata_c_id;               // Compressed instruction sampled inside IF stage
  logic        instr_is_compressed_id;
  logic        instr_fetch_err;                // Bus error on instr fetch
  logic        instr_fetch_err_plus2;          // Instruction error is misaligned
  logic        illegal_c_insn_id;              // Illegal compressed instruction sent to ID stage
  logic [31:0] pc_if;                          // Program counter in IF stage
  logic [31:0] pc_id;                          // Program counter in ID stage
  logic [31:0] pc_wb;                          // Program counter in WB stage
  logic [33:0] imd_val_d_ex;                   // Intermediate register for multicycle Ops
  logic [33:0] imd_val_q_ex;                   // Intermediate register for multicycle Ops
  logic        imd_val_we_ex;

  logic        data_ind_timing;
  logic        dummy_instr_en;
  logic [2:0]  dummy_instr_mask;
  logic        dummy_instr_seed_en;
  logic [31:0] dummy_instr_seed;
  logic        icache_enable;
  logic        icache_inval;

  logic        instr_first_cycle_id;
  logic        instr_valid_clear;
  logic        pc_set;
  logic        pc_set_spec;
  pc_sel_e     pc_mux_id;                      // Mux selector for next PC
  exc_pc_sel_e exc_pc_mux_id;                  // Mux selector for exception PC
  exc_cause_e  exc_cause;                      // Exception cause

  logic        lsu_load_err;
  logic        lsu_store_err;

  // LSU signals
  logic        lsu_addr_incr_req;
  logic [31:0] lsu_addr_last;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] branch_target_ex;
  logic        branch_decision;

  // Core busy signals
  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;
  logic        core_busy_d, core_busy_q;

  // Register File
  logic [4:0]  rf_raddr_a;
  logic [31:0] rf_rdata_a;
  logic [4:0]  rf_raddr_b;
  logic [31:0] rf_rdata_b;
  logic [4:0]  rf_waddr_wb;
  logic [31:0] rf_wdata_wb;
  // Writeback register write data that can be used on the forwarding path (doesn't factor in memory
  // read data as this is too late for the forwarding path)
  logic [31:0] rf_wdata_fwd_wb;
  logic [31:0] rf_wdata_lsu;
  logic        rf_we_wb;
  logic        rf_we_lsu;

  logic [4:0]  rf_waddr_id;
  logic [31:0] rf_wdata_id;
  logic        rf_we_id;

  // ALU Control
  alu_op_e     alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;

  logic [31:0] bt_a_operand;
  logic [31:0] bt_b_operand;

  logic [31:0] alu_adder_result_ex;    // Used to forward computed address to LSU
  logic [31:0] result_ex;

  // Multiplier Control
  logic        mult_en_ex;
  logic        div_en_ex;
  logic        mult_sel_ex;
  logic        div_sel_ex;
  md_op_e      multdiv_operator_ex;
  logic [1:0]  multdiv_signed_mode_ex;
  logic [31:0] multdiv_operand_a_ex;
  logic [31:0] multdiv_operand_b_ex;
  logic        multdiv_ready_id;

  // CSR control
  logic        csr_access;
  csr_op_e     csr_op;
  logic        csr_op_en;
  csr_num_e    csr_addr;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;
  logic        illegal_csr_insn_id;    // CSR access to non-existent register,
                                       // with wrong priviledge level,
                                       // or missing write permissions

  // Data Memory Control
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic        lsu_req;
  logic [31:0] lsu_wdata;
  logic        lsu_req_done;

  // stall control
  logic        id_in_ready;
  logic        ex_valid;

  logic        lsu_resp_valid;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;          // Id stage asserts a req to instruction core interface

  // Writeback stage
  logic           en_wb;
  wb_instr_type_e instr_type_wb;
  logic           ready_wb;
  logic           rf_write_wb;
  logic           outstanding_load_wb;
  logic           outstanding_store_wb;

  // Interrupts
  logic        irq_pending;
  logic        nmi_mode;
  irqs_t       irqs;
  logic        csr_mstatus_mie;
  logic [31:0] csr_mepc, csr_depc;

  // PMP signals
  logic [33:0] csr_pmp_addr [PMPNumRegions];
  pmp_cfg_t    csr_pmp_cfg  [PMPNumRegions];
  logic        pmp_req_err  [PMP_NUM_CHAN];
  logic        instr_req_out;
  logic        data_req_out;

  logic        csr_save_if;
  logic        csr_save_id;
  logic        csr_save_wb;
  logic        csr_restore_mret_id;
  logic        csr_restore_dret_id;
  logic        csr_save_cause;
  logic        csr_mtvec_init;
  logic [31:0] csr_mtvec;
  logic [31:0] csr_mtval;
  logic        csr_mstatus_tw;
  priv_lvl_e   priv_mode_id;
  priv_lvl_e   priv_mode_if;
  priv_lvl_e   priv_mode_lsu;

  // debug mode and dcsr configuration
  logic        debug_mode;
  dbg_cause_e  debug_cause;
  logic        debug_csr_save;
  logic        debug_single_step;
  logic        debug_ebreakm;
  logic        debug_ebreaku;
  logic        trigger_match;

  // signals relating to instruction movements between pipeline stages
  // used by performance counters and RVFI
  logic        instr_id_done;
  logic        instr_id_done_compressed;
  logic        instr_done_wb;

  logic        perf_iside_wait;
  logic        perf_dside_wait;
  logic        perf_mul_wait;
  logic        perf_div_wait;
  logic        perf_jump;
  logic        perf_branch;
  logic        perf_tbranch;
  logic        perf_load;
  logic        perf_store;

  // for RVFI
  logic        illegal_insn_id, unused_illegal_insn_id; // ID stage sees an illegal instruction

  // RISC-V Formal Interface signals



































  //////////////////////
  // Clock management //
  //////////////////////

  logic        clk;

  logic        clock_en;

  // Before going to sleep, wait for I- and D-side
  // interfaces to finish ongoing operations.
  assign core_busy_d = ctrl_busy | if_busy | lsu_busy;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      core_busy_q <= 1'b0;
    end else begin
      core_busy_q <= core_busy_d;
    end
  end

  assign clock_en     = core_busy_q | debug_req_i | irq_pending | irq_nm_i;
  assign core_sleep_o = ~clock_en;

  // main clock gate of the core
  // generates all clocks except the one for the debug unit which is
  // independent
  prim_clock_gating core_clock_gate_i (
      .clk_i     ( clk_i           ),
      .en_i      ( clock_en        ),
      .test_en_i ( test_en_i       ),
      .clk_o     ( clk             )
  );

  //////////////
  // IF stage //
  //////////////

  ibex_if_stage #(
      .DmHaltAddr        ( DmHaltAddr        ),
      .DmExceptionAddr   ( DmExceptionAddr   ),
      .DummyInstructions ( DummyInstructions ),
      .ICache            ( ICache            ),
      .ICacheECC         ( ICacheECC         )
  ) if_stage_i (
      .clk_i                    ( clk                    ),
      .rst_ni                   ( rst_ni                 ),

      .boot_addr_i              ( boot_addr_i            ),
      .req_i                    ( instr_req_int          ), // instruction request control

      // instruction cache interface
      .instr_req_o              ( instr_req_out          ),
      .instr_addr_o             ( instr_addr_o           ),
      .instr_gnt_i              ( instr_gnt_i            ),
      .instr_rvalid_i           ( instr_rvalid_i         ),
      .instr_rdata_i            ( instr_rdata_i          ),
      .instr_err_i              ( instr_err_i            ),
      .instr_pmp_err_i          ( pmp_req_err[PMP_I]     ),

      // outputs to ID stage
      .instr_valid_id_o         ( instr_valid_id         ),
      .instr_new_id_o           ( instr_new_id           ),
      .instr_rdata_id_o         ( instr_rdata_id         ),
      .instr_rdata_alu_id_o     ( instr_rdata_alu_id     ),
      .instr_rdata_c_id_o       ( instr_rdata_c_id       ),
      .instr_is_compressed_id_o ( instr_is_compressed_id ),
      .instr_fetch_err_o        ( instr_fetch_err        ),
      .instr_fetch_err_plus2_o  ( instr_fetch_err_plus2  ),
      .illegal_c_insn_id_o      ( illegal_c_insn_id      ),
      .dummy_instr_id_o         ( dummy_instr_id         ),
      .pc_if_o                  ( pc_if                  ),
      .pc_id_o                  ( pc_id                  ),

      // control signals
      .instr_valid_clear_i      ( instr_valid_clear      ),
      .pc_set_i                 ( pc_set                 ),
      .pc_set_spec_i            ( pc_set_spec            ),
      .pc_mux_i                 ( pc_mux_id              ),
      .exc_pc_mux_i             ( exc_pc_mux_id          ),
      .exc_cause                ( exc_cause              ),
      .dummy_instr_en_i         ( dummy_instr_en         ),
      .dummy_instr_mask_i       ( dummy_instr_mask       ),
      .dummy_instr_seed_en_i    ( dummy_instr_seed_en    ),
      .dummy_instr_seed_i       ( dummy_instr_seed       ),
      .icache_enable_i          ( icache_enable          ),
      .icache_inval_i           ( icache_inval           ),

      // branch targets
      .branch_target_ex_i       ( branch_target_ex       ),

      // CSRs
      .csr_mepc_i               ( csr_mepc               ), // exception return address
      .csr_depc_i               ( csr_depc               ), // debug return address
      .csr_mtvec_i              ( csr_mtvec              ), // trap-vector base address
      .csr_mtvec_init_o         ( csr_mtvec_init         ),

      // pipeline stalls
      .id_in_ready_i            ( id_in_ready            ),

      .if_busy_o                ( if_busy                )
  );

  // Core is waiting for the ISide when ID/EX stage is ready for a new instruction but none are
  // available
  assign perf_iside_wait = id_in_ready & ~instr_valid_id;

  // Qualify the instruction request with PMP error
  assign instr_req_o = instr_req_out & ~pmp_req_err[PMP_I];

  //////////////
  // ID stage //
  //////////////

  ibex_id_stage #(
      .RV32E           ( RV32E           ),
      .RV32M           ( RV32M           ),
      .RV32B           ( RV32B           ),
      .BranchTargetALU ( BranchTargetALU ),
      .DataIndTiming   ( DataIndTiming   ),
      .SpecBranch      ( SpecBranch      ),
      .WritebackStage  ( WritebackStage  )
  ) id_stage_i (
      .clk_i                        ( clk                      ),
      .rst_ni                       ( rst_ni                   ),

      // Processor Enable
      .fetch_enable_i               ( fetch_enable_i           ),
      .ctrl_busy_o                  ( ctrl_busy                ),
      .illegal_insn_o               ( illegal_insn_id          ),

      // from/to IF-ID pipeline register
      .instr_valid_i                ( instr_valid_id           ),
      .instr_rdata_i                ( instr_rdata_id           ),
      .instr_rdata_alu_i            ( instr_rdata_alu_id       ),
      .instr_rdata_c_i              ( instr_rdata_c_id         ),
      .instr_is_compressed_i        ( instr_is_compressed_id   ),

      // Jumps and branches
      .branch_decision_i            ( branch_decision          ),

      // IF and ID control signals
      .instr_first_cycle_id_o       ( instr_first_cycle_id     ),
      .instr_valid_clear_o          ( instr_valid_clear        ),
      .id_in_ready_o                ( id_in_ready              ),
      .instr_req_o                  ( instr_req_int            ),
      .pc_set_o                     ( pc_set                   ),
      .pc_set_spec_o                ( pc_set_spec              ),
      .pc_mux_o                     ( pc_mux_id                ),
      .exc_pc_mux_o                 ( exc_pc_mux_id            ),
      .exc_cause_o                  ( exc_cause                ),
      .icache_inval_o               ( icache_inval             ),

      .instr_fetch_err_i            ( instr_fetch_err          ),
      .instr_fetch_err_plus2_i      ( instr_fetch_err_plus2    ),
      .illegal_c_insn_i             ( illegal_c_insn_id        ),

      .pc_id_i                      ( pc_id                    ),

      // Stalls
      .ex_valid_i                   ( ex_valid                 ),
      .lsu_resp_valid_i             ( lsu_resp_valid           ),

      .alu_operator_ex_o            ( alu_operator_ex          ),
      .alu_operand_a_ex_o           ( alu_operand_a_ex         ),
      .alu_operand_b_ex_o           ( alu_operand_b_ex         ),

      .imd_val_q_ex_o               ( imd_val_q_ex             ),
      .imd_val_d_ex_i               ( imd_val_d_ex             ),
      .imd_val_we_ex_i              ( imd_val_we_ex            ),

      .bt_a_operand_o               ( bt_a_operand             ),
      .bt_b_operand_o               ( bt_b_operand             ),

      .mult_en_ex_o                 ( mult_en_ex               ),
      .div_en_ex_o                  ( div_en_ex                ),
      .mult_sel_ex_o                ( mult_sel_ex              ),
      .div_sel_ex_o                 ( div_sel_ex               ),
      .multdiv_operator_ex_o        ( multdiv_operator_ex      ),
      .multdiv_signed_mode_ex_o     ( multdiv_signed_mode_ex   ),
      .multdiv_operand_a_ex_o       ( multdiv_operand_a_ex     ),
      .multdiv_operand_b_ex_o       ( multdiv_operand_b_ex     ),
      .multdiv_ready_id_o           ( multdiv_ready_id         ),

      // CSR ID/EX
      .csr_access_o                 ( csr_access               ),
      .csr_op_o                     ( csr_op                   ),
      .csr_op_en_o                  ( csr_op_en                ),
      .csr_save_if_o                ( csr_save_if              ), // control signal to save PC
      .csr_save_id_o                ( csr_save_id              ), // control signal to save PC
      .csr_save_wb_o                ( csr_save_wb              ), // control signal to save PC
      .csr_restore_mret_id_o        ( csr_restore_mret_id      ), // restore mstatus upon MRET
      .csr_restore_dret_id_o        ( csr_restore_dret_id      ), // restore mstatus upon MRET
      .csr_save_cause_o             ( csr_save_cause           ),
      .csr_mtval_o                  ( csr_mtval                ),
      .priv_mode_i                  ( priv_mode_id             ),
      .csr_mstatus_tw_i             ( csr_mstatus_tw           ),
      .illegal_csr_insn_i           ( illegal_csr_insn_id      ),
      .data_ind_timing_i            ( data_ind_timing          ),

      // LSU
      .lsu_req_o                    ( lsu_req                  ), // to load store unit
      .lsu_we_o                     ( lsu_we                   ), // to load store unit
      .lsu_type_o                   ( lsu_type                 ), // to load store unit
      .lsu_sign_ext_o               ( lsu_sign_ext             ), // to load store unit
      .lsu_wdata_o                  ( lsu_wdata                ), // to load store unit
      .lsu_req_done_i               ( lsu_req_done             ), // from load store unit

      .lsu_addr_incr_req_i          ( lsu_addr_incr_req        ),
      .lsu_addr_last_i              ( lsu_addr_last            ),

      .lsu_load_err_i               ( lsu_load_err             ),
      .lsu_store_err_i              ( lsu_store_err            ),

      // Interrupt Signals
      .csr_mstatus_mie_i            ( csr_mstatus_mie          ),
      .irq_pending_i                ( irq_pending              ),
      .irqs_i                       ( irqs                     ),
      .irq_nm_i                     ( irq_nm_i                 ),
      .nmi_mode_o                   ( nmi_mode                 ),

      // Debug Signal
      .debug_mode_o                 ( debug_mode               ),
      .debug_cause_o                ( debug_cause              ),
      .debug_csr_save_o             ( debug_csr_save           ),
      .debug_req_i                  ( debug_req_i              ),
      .debug_single_step_i          ( debug_single_step        ),
      .debug_ebreakm_i              ( debug_ebreakm            ),
      .debug_ebreaku_i              ( debug_ebreaku            ),
      .trigger_match_i              ( trigger_match            ),

      // write data to commit in the register file
      .result_ex_i                  ( result_ex                ),
      .csr_rdata_i                  ( csr_rdata                ),

      .rf_raddr_a_o                 ( rf_raddr_a               ),
      .rf_rdata_a_i                 ( rf_rdata_a               ),
      .rf_raddr_b_o                 ( rf_raddr_b               ),
      .rf_rdata_b_i                 ( rf_rdata_b               ),




      .rf_waddr_id_o                ( rf_waddr_id              ),
      .rf_wdata_id_o                ( rf_wdata_id              ),
      .rf_we_id_o                   ( rf_we_id                 ),

      .rf_waddr_wb_i                ( rf_waddr_wb              ),
      .rf_wdata_fwd_wb_i            ( rf_wdata_fwd_wb          ),
      .rf_write_wb_i                ( rf_write_wb              ),

      .en_wb_o                      ( en_wb                    ),
      .instr_type_wb_o              ( instr_type_wb            ),
      .ready_wb_i                   ( ready_wb                 ),
      .outstanding_load_wb_i        ( outstanding_load_wb      ),
      .outstanding_store_wb_i       ( outstanding_store_wb     ),

      // Performance Counters
      .perf_jump_o                  ( perf_jump                ),
      .perf_branch_o                ( perf_branch              ),
      .perf_tbranch_o               ( perf_tbranch             ),
      .perf_dside_wait_o            ( perf_dside_wait          ),
      .perf_mul_wait_o              ( perf_mul_wait            ),
      .perf_div_wait_o              ( perf_div_wait            ),
      .instr_id_done_o              ( instr_id_done            ),
      .instr_id_done_compressed_o   ( instr_id_done_compressed )
  );

  // for RVFI only
  assign unused_illegal_insn_id = illegal_insn_id;

  ibex_ex_block #(
      .RV32M                    ( RV32M                    ),
      .RV32B                    ( RV32B                    ),
      .BranchTargetALU          ( BranchTargetALU          ),
      .MultiplierImplementation ( MultiplierImplementation )
  ) ex_block_i (
      .clk_i                    ( clk                      ),
      .rst_ni                   ( rst_ni                   ),

      // ALU signal from ID stage
      .alu_operator_i           ( alu_operator_ex          ),
      .alu_operand_a_i          ( alu_operand_a_ex         ),
      .alu_operand_b_i          ( alu_operand_b_ex         ),
      .alu_instr_first_cycle_i  ( instr_first_cycle_id     ),

      // Branch target ALU signal from ID stage
      .bt_a_operand_i           ( bt_a_operand             ),
      .bt_b_operand_i           ( bt_b_operand             ),

      // Multipler/Divider signal from ID stage
      .multdiv_operator_i       ( multdiv_operator_ex      ),
      .mult_en_i                ( mult_en_ex               ),
      .div_en_i                 ( div_en_ex                ),
      .mult_sel_i               ( mult_sel_ex              ),
      .div_sel_i                ( div_sel_ex               ),
      .multdiv_signed_mode_i    ( multdiv_signed_mode_ex   ),
      .multdiv_operand_a_i      ( multdiv_operand_a_ex     ),
      .multdiv_operand_b_i      ( multdiv_operand_b_ex     ),
      .multdiv_ready_id_i       ( multdiv_ready_id         ),
      .data_ind_timing_i        ( data_ind_timing          ),

      // Intermediate value register
      .imd_val_we_o             ( imd_val_we_ex            ),
      .imd_val_d_o              ( imd_val_d_ex             ),
      .imd_val_q_i              ( imd_val_q_ex             ),

      // Outputs
      .alu_adder_result_ex_o    ( alu_adder_result_ex      ), // to LSU
      .result_ex_o              ( result_ex                ), // to ID

      .branch_target_o          ( branch_target_ex         ), // to IF
      .branch_decision_o        ( branch_decision          ), // to ID

      .ex_valid_o               ( ex_valid                 )
  );

  /////////////////////
  // Load/store unit //
  /////////////////////

  assign data_req_o = data_req_out & ~pmp_req_err[PMP_D];

  ibex_load_store_unit load_store_unit_i (
      .clk_i                 ( clk                 ),
      .rst_ni                ( rst_ni              ),

      // data interface
      .data_req_o            ( data_req_out        ),
      .data_gnt_i            ( data_gnt_i          ),
      .data_rvalid_i         ( data_rvalid_i       ),
      .data_err_i            ( data_err_i          ),
      .data_pmp_err_i        ( pmp_req_err[PMP_D]  ),

      .data_addr_o           ( data_addr_o         ),
      .data_we_o             ( data_we_o           ),
      .data_be_o             ( data_be_o           ),
      .data_wdata_o          ( data_wdata_o        ),
      .data_rdata_i          ( data_rdata_i        ),

      // signals to/from ID/EX stage
      .lsu_we_i              ( lsu_we              ),
      .lsu_type_i            ( lsu_type            ),
      .lsu_wdata_i           ( lsu_wdata           ),
      .lsu_sign_ext_i        ( lsu_sign_ext        ),

      .lsu_rdata_o           ( rf_wdata_lsu        ),
      .lsu_rdata_valid_o     ( rf_we_lsu           ),
      .lsu_req_i             ( lsu_req             ),
      .lsu_req_done_o        ( lsu_req_done        ),

      .adder_result_ex_i     ( alu_adder_result_ex ),

      .addr_incr_req_o       ( lsu_addr_incr_req   ),
      .addr_last_o           ( lsu_addr_last       ),


      .lsu_resp_valid_o      ( lsu_resp_valid      ),

      // exception signals
      .load_err_o            ( lsu_load_err        ),
      .store_err_o           ( lsu_store_err       ),

      .busy_o                ( lsu_busy            ),

      .perf_load_o           ( perf_load           ),
      .perf_store_o          ( perf_store          )
  );

  ibex_wb_stage #(
    .WritebackStage ( WritebackStage )
  ) wb_stage_i (
    .clk_i                      ( clk_i                    ),
    .rst_ni                     ( rst_ni                   ),
    .en_wb_i                    ( en_wb                    ),
    .instr_type_wb_i            ( instr_type_wb            ),
    .pc_id_i                    ( pc_id                    ),

    .ready_wb_o                 ( ready_wb                 ),
    .rf_write_wb_o              ( rf_write_wb              ),
    .outstanding_load_wb_o      ( outstanding_load_wb      ),
    .outstanding_store_wb_o     ( outstanding_store_wb     ),
    .pc_wb_o                    ( pc_wb                    ),

    .rf_waddr_id_i              ( rf_waddr_id              ),
    .rf_wdata_id_i              ( rf_wdata_id              ),
    .rf_we_id_i                 ( rf_we_id                 ),

    .rf_wdata_lsu_i             ( rf_wdata_lsu             ),
    .rf_we_lsu_i                ( rf_we_lsu                ),

    .rf_wdata_fwd_wb_o          ( rf_wdata_fwd_wb          ),

    .rf_waddr_wb_o              ( rf_waddr_wb              ),
    .rf_wdata_wb_o              ( rf_wdata_wb              ),
    .rf_we_wb_o                 ( rf_we_wb                 ),

    .lsu_resp_valid_i           ( lsu_resp_valid           ),

    .instr_done_wb_o            ( instr_done_wb            )
  );

  ibex_register_file #(
      .RV32E             (RV32E),
      .DataWidth         (32),
      .DummyInstructions (DummyInstructions)
  ) register_file_i (
      .clk_i            ( clk_i          ),
      .rst_ni           ( rst_ni         ),

      .test_en_i        ( test_en_i      ),
      .dummy_instr_id_i ( dummy_instr_id ),

      // Read port a
      .raddr_a_i        ( rf_raddr_a     ),
      .rdata_a_o        ( rf_rdata_a     ),
      // Read port b
      .raddr_b_i        ( rf_raddr_b     ),
      .rdata_b_o        ( rf_rdata_b     ),
      // write port
      .waddr_a_i        ( rf_waddr_wb    ),
      .wdata_a_i        ( rf_wdata_wb    ),
      .we_a_i           ( rf_we_wb       )
  );

  // Explict INC_ASSERT block to avoid unused signal lint warnings were asserts are not included
  



























  ////////////////////////
  // RF (Register File) //
  ////////////////////////







  /////////////////////////////////////////
  // CSRs (Control and Status Registers) //
  /////////////////////////////////////////

  assign csr_wdata  = alu_operand_a_ex;
  assign csr_addr   = csr_num_e'(csr_access ? alu_operand_b_ex[11:0] : 12'b0);

  ibex_cs_registers #(
      .DbgTriggerEn      ( DbgTriggerEn      ),
      .DataIndTiming     ( DataIndTiming     ),
      .DummyInstructions ( DummyInstructions ),
      .ICache            ( ICache            ),
      .MHPMCounterNum    ( MHPMCounterNum    ),
      .MHPMCounterWidth  ( MHPMCounterWidth  ),
      .PMPEnable         ( PMPEnable         ),
      .PMPGranularity    ( PMPGranularity    ),
      .PMPNumRegions     ( PMPNumRegions     ),
      .RV32E             ( RV32E             ),
      .RV32M             ( RV32M             )
  ) cs_registers_i (
      .clk_i                   ( clk                      ),
      .rst_ni                  ( rst_ni                   ),

      // Hart ID from outside
      .hart_id_i               ( hart_id_i                ),
      .priv_mode_id_o          ( priv_mode_id             ),
      .priv_mode_if_o          ( priv_mode_if             ),
      .priv_mode_lsu_o         ( priv_mode_lsu            ),

      // mtvec
      .csr_mtvec_o             ( csr_mtvec                ),
      .csr_mtvec_init_i        ( csr_mtvec_init           ),
      .boot_addr_i             ( boot_addr_i              ),

      // Interface to CSRs     ( SRAM like                )
      .csr_access_i            ( csr_access               ),
      .csr_addr_i              ( csr_addr                 ),
      .csr_wdata_i             ( csr_wdata                ),
      .csr_op_i                ( csr_op                   ),
      .csr_op_en_i             ( csr_op_en                ),
      .csr_rdata_o             ( csr_rdata                ),

      // Interrupt related control signals
      .irq_software_i          ( irq_software_i           ),
      .irq_timer_i             ( irq_timer_i              ),
      .irq_external_i          ( irq_external_i           ),
      .irq_fast_i              ( irq_fast_i               ),
      .nmi_mode_i              ( nmi_mode                 ),
      .irq_pending_o           ( irq_pending              ),
      .irqs_o                  ( irqs                     ),
      .csr_mstatus_mie_o       ( csr_mstatus_mie          ),
      .csr_mstatus_tw_o        ( csr_mstatus_tw           ),
      .csr_mepc_o              ( csr_mepc                 ),

      // PMP
      .csr_pmp_cfg_o           ( csr_pmp_cfg              ),
      .csr_pmp_addr_o          ( csr_pmp_addr             ),

      // debug
      .csr_depc_o              ( csr_depc                 ),
      .debug_mode_i            ( debug_mode               ),
      .debug_cause_i           ( debug_cause              ),
      .debug_csr_save_i        ( debug_csr_save           ),
      .debug_single_step_o     ( debug_single_step        ),
      .debug_ebreakm_o         ( debug_ebreakm            ),
      .debug_ebreaku_o         ( debug_ebreaku            ),
      .trigger_match_o         ( trigger_match            ),

      .pc_if_i                 ( pc_if                    ),
      .pc_id_i                 ( pc_id                    ),
      .pc_wb_i                 ( pc_wb                    ),

      .data_ind_timing_o       ( data_ind_timing          ),
      .dummy_instr_en_o        ( dummy_instr_en           ),
      .dummy_instr_mask_o      ( dummy_instr_mask         ),
      .dummy_instr_seed_en_o   ( dummy_instr_seed_en      ),
      .dummy_instr_seed_o      ( dummy_instr_seed         ),
      .icache_enable_o         ( icache_enable            ),

      .csr_save_if_i           ( csr_save_if              ),
      .csr_save_id_i           ( csr_save_id              ),
      .csr_save_wb_i           ( csr_save_wb              ),
      .csr_restore_mret_i      ( csr_restore_mret_id      ),
      .csr_restore_dret_i      ( csr_restore_dret_id      ),
      .csr_save_cause_i        ( csr_save_cause           ),
      .csr_mcause_i            ( exc_cause                ),
      .csr_mtval_i             ( csr_mtval                ),
      .illegal_csr_insn_o      ( illegal_csr_insn_id      ),

      // performance counter related signals
      .instr_ret_i             ( instr_id_done            ),
      .instr_ret_compressed_i  ( instr_id_done_compressed ),
      .iside_wait_i            ( perf_iside_wait          ),
      .jump_i                  ( perf_jump                ),
      .branch_i                ( perf_branch              ),
      .branch_taken_i          ( perf_tbranch             ),
      .mem_load_i              ( perf_load                ),
      .mem_store_i             ( perf_store               ),
      .dside_wait_i            ( perf_dside_wait          ),
      .mul_wait_i              ( perf_mul_wait            ),
      .div_wait_i              ( perf_div_wait            )
  );

  // These assertions are in top-level as instr_valid_id required as the enable term
  
  

  if (PMPEnable) begin : g_pmp
    logic [33:0] pmp_req_addr [PMP_NUM_CHAN];
    pmp_req_e    pmp_req_type [PMP_NUM_CHAN];
    priv_lvl_e   pmp_priv_lvl [PMP_NUM_CHAN];

    assign pmp_req_addr[PMP_I] = {2'b00,instr_addr_o[31:0]};
    assign pmp_req_type[PMP_I] = PMP_ACC_EXEC;
    assign pmp_priv_lvl[PMP_I] = priv_mode_if;
    assign pmp_req_addr[PMP_D] = {2'b00,data_addr_o[31:0]};
    assign pmp_req_type[PMP_D] = data_we_o ? PMP_ACC_WRITE : PMP_ACC_READ;
    assign pmp_priv_lvl[PMP_D] = priv_mode_lsu;

    ibex_pmp #(
        .PMPGranularity        ( PMPGranularity ),
        .PMPNumChan            ( PMP_NUM_CHAN   ),
        .PMPNumRegions         ( PMPNumRegions  )
    ) pmp_i (
        .clk_i                 ( clk            ),
        .rst_ni                ( rst_ni         ),
        // Interface to CSRs
        .csr_pmp_cfg_i         ( csr_pmp_cfg    ),
        .csr_pmp_addr_i        ( csr_pmp_addr   ),
        .priv_mode_i           ( pmp_priv_lvl   ),
        // Access checking channels
        .pmp_req_addr_i        ( pmp_req_addr   ),
        .pmp_req_type_i        ( pmp_req_type   ),
        .pmp_req_err_o         ( pmp_req_err    )
    );
  end else begin : g_no_pmp
    // Unused signal tieoff
    priv_lvl_e unused_priv_lvl_if, unused_priv_lvl_ls;
    logic [33:0] unused_csr_pmp_addr [PMPNumRegions];
    pmp_cfg_t    unused_csr_pmp_cfg  [PMPNumRegions];
    assign unused_priv_lvl_if = priv_mode_if;
    assign unused_priv_lvl_ls = priv_mode_lsu;
    assign unused_csr_pmp_addr = csr_pmp_addr;
    assign unused_csr_pmp_cfg = csr_pmp_cfg;

    // Output tieoff
    assign pmp_req_err[PMP_I] = 1'b0;
    assign pmp_req_err[PMP_D] = 1'b0;
  end







































































































































































































































































































endmodule
