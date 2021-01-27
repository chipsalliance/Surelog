module top ();
   middleman #(.invert(1)) mdl1();
   middleman #(.invert(0)) mdl0();
endmodule

/*
module top();
  function automatic logic [5:0] popcnt64 (
    input logic [63:0] in
  );
    logic [5:0] cnt= 0;
    foreach (in[k]) begin
      cnt += 6'(in[k]);
    end
    return cnt;
  endfunction : popcnt64
endmodule
*/

/*

class toto;


typedef bit[16 - 1:0] amiq_eth_length;

   virtual function void do_unpack(uvm_packer packer);
        amiq_eth_length int_ether_type;
        

      
   begin 
      //int __array[] = new[($bits(int_ether_type)+31)/32]; 
      bit [((($bits(int_ether_type) + 31) / 32) * 32) - 1:0] __var; 
      
   end

;

  endfunction

endclass
*/

/*
package ariane_pkg;
   localparam NR_SB_ENTRIES = 8; // number of scoreboard entries
    localparam TRANS_ID_BITS = $clog2(NR_SB_ENTRIES);
endpackage


import ariane_pkg::*;

module shift_reg  #(parameter type dtype,
        paramater Depth) ();

endmodule

module load_store_unit #(
    parameter int unsigned ASID_WIDTH = 1,
    parameter ariane_pkg::ariane_cfg_t ArianeCfg = ariane_pkg::ArianeDefaultConfig
)(
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     flush_i,
    output logic                     no_st_pending_o,
    input  logic                     amo_valid_commit_i,

    input  fu_data_t                 fu_data_i,
    output logic                     lsu_ready_o,              // FU is ready e.g. not busy
    input  logic                     lsu_valid_i,              // Input is valid

    output logic [TRANS_ID_BITS-1:0] load_trans_id_o,          // ID of scoreboard entry at which to write back
    output logic [63:0]              load_result_o,
    output logic                     load_valid_o,
    output exception_t               load_exception_o,         // to WB, signal exception status LD exception

    output logic [TRANS_ID_BITS-1:0] store_trans_id_o,         // ID of scoreboard entry at which to write back
    output logic [63:0]              store_result_o,
    output logic                     store_valid_o,
    output exception_t               store_exception_o,        // to WB, signal exception status ST exception

    input  logic                     commit_i,                 // commit the pending store
    output logic                     commit_ready_o,           // commit queue is ready to accept another commit request

    input  logic                     enable_translation_i,     // enable virtual memory translation
    input  logic                     en_ld_st_translation_i,   // enable virtual memory translation for load/stores

    // icache translation requests
    input  icache_areq_o_t           icache_areq_i,
    output icache_areq_i_t           icache_areq_o,

    input  riscv::priv_lvl_t         priv_lvl_i,               // From CSR register file
    input  riscv::priv_lvl_t         ld_st_priv_lvl_i,         // From CSR register file
    input  logic                     sum_i,                    // From CSR register file
    input  logic                     mxr_i,                    // From CSR register file
    input  logic [43:0]              satp_ppn_i,               // From CSR register file
    input  logic [ASID_WIDTH-1:0]    asid_i,                   // From CSR register file
    input  logic                     flush_tlb_i,
    // Performance counters
    output logic                     itlb_miss_o,
    output logic                     dtlb_miss_o,

    // interface to dcache
    input  dcache_req_o_t [2:0]      dcache_req_ports_i,
    output dcache_req_i_t [2:0]      dcache_req_ports_o,
    // AMO interface
    output amo_req_t                 amo_req_o,
    input  amo_resp_t                amo_resp_i
);
    // data is misaligned
    logic data_misaligned;
    // --------------------------------------
    // 1st register stage - (stall registers)
    // --------------------------------------
    // those are the signals which are always correct
    // e.g.: they keep the value in the stall case
    lsu_ctrl_t lsu_ctrl;

    logic      pop_st;
    logic      pop_ld;

    // ------------------------------
    // Address Generation Unit (AGU)
    // ------------------------------
    // virtual address as calculated by the AGU in the first cycle
    logic [63:0] vaddr_i;
    logic [7:0]  be_i;

    assign vaddr_i = $unsigned($signed(fu_data_i.imm) + $signed(fu_data_i.operand_a));

    logic                     st_valid_i;
    logic                     ld_valid_i;
    logic                     ld_translation_req;
    logic                     st_translation_req;
    logic [63:0]              ld_vaddr;
    logic [63:0]              st_vaddr;
    logic                     translation_req;
    logic                     translation_valid;
    logic [63:0]              mmu_vaddr;
    logic [63:0]              mmu_paddr;
    exception_t               mmu_exception;
    logic                     dtlb_hit;

    logic                     ld_valid;
    logic [TRANS_ID_BITS-1:0] ld_trans_id;
    logic [63:0]              ld_result;
    logic                     st_valid;
    logic [TRANS_ID_BITS-1:0] st_trans_id;
    logic [63:0]              st_result;

    logic [11:0]              page_offset;
    logic                     page_offset_matches;

    exception_t               misaligned_exception;
    exception_t               ld_ex;
    exception_t               st_ex;

    logic [$clog2(ASID_WIDTH * 20)-1:0]    asid_ii;
    
    // ----------------------------
    // Output Pipeline Register
    // ----------------------------
    shift_reg #(
        .dtype ( logic[ $bits(ld_valid) + $bits(ld_trans_id) + $bits(ld_result) + $bits(ld_ex) - 1: 0]),
        .Depth ( NR_LOAD_PIPE_REGS )
    ) i_pipe_reg_load (
        .clk_i,
        .rst_ni,
        .d_i ( {ld_valid, ld_trans_id, ld_result, ld_ex} ),
        .d_o ( {load_valid_o, load_trans_id_o, load_result_o, load_exception_o} )
    );

   
   
endmodule  
*/

/*module keccak_2share #(
  parameter int Width = 1600, // b= {25, 50, 100, 200, 400, 800, 1600}

  // Derived
  localparam int W        = Width/25,
  localparam int L        = $clog2(W),
  localparam int MaxRound = 12 + 2*L,           // Keccak-f only
  localparam int RndW     = $clog2(MaxRound+1) // Representing up to MaxRound
) ();

function automatic box_t iota(box_t state, logic [RndW-1:0] rnd);
   
  endfunction : iota

endmodule
*/
/*
module prim_fifo_async #(
  parameter  int unsigned Width  = 16,
  parameter  int unsigned Depth  = 3,
  localparam int unsigned DepthW = $clog2(Depth+1) // derived parameter representing [0..Depth]
) (
  
);

  localparam int unsigned PTRV_W = $clog2(Depth);
  localparam logic [PTRV_W-1:0] DepthMinus1 = PTRV_W'(Depth - 1);
  localparam int unsigned PTR_WIDTH = PTRV_W+1;

  function automatic [PTR_WIDTH-1:0] dec2gray(input logic [PTR_WIDTH-1:0] decval);
    logic [PTR_WIDTH-1:0] decval_sub;
    logic [PTR_WIDTH-2:0] decval_in;
    logic                 unused_decval_msb;

  endfunction


endmodule
*/

/*
module dut();

   localparam int unsigned TIMEOUT_CNT_W = 5;
   localparam int unsigned OP_W          = 5;

    typedef enum logic [1:0] {
      DUMMY_ADD = 2'b00
    } dummy_instr_e;

    typedef struct packed {
      dummy_instr_e             instr_type;
      logic [OP_W-1:0]          op_b;
      logic [OP_W-1:0]          op_a;
      logic [TIMEOUT_CNT_W-1:0] cnt;
    } lfsr_data_t;
    localparam int unsigned LFSR_OUT_W = $bits(lfsr_data_t);

endmodule;
*/


/*

package prim_util_pkg;
  
  function automatic integer _clog2(integer value);
    integer result;
    value = value - 1;
    for (result = 0; value > 0; result = result + 1) begin
      value = value >> 1;
    end
    return result;
  endfunction

  function automatic integer vbits(integer value);
    return (value == 1) ? 1 : prim_util_pkg::_clog2(value);
  endfunction

endpackage

package flash_ctrl_pkg;

  parameter int DataWidth       = 64;
  parameter int DataByteWidth   = prim_util_pkg::vbits(DataWidth / 8);

endpackage


module top();

  reg [flash_ctrl_pkg::DataByteWidth:0] areg;

endmodule

*/

/*
package pkg;

 typedef enum bit [3:0] {
    SV32 = 4'b0001,
    SV39 = 4'b1000
  } satp_mode_t;

class riscv_page_table_entry#(satp_mode_t MODE = SV39);

  parameter VPN_WIDTH   = (MODE == SV32) ? 10 : 9;

 virtual function void inject_page();
    
      bit [riscv_page_table_entry#(MODE)::VPN_WIDTH-1:0] fault_ppn;  
    
  endfunction

endclass

endpackage


*/

/*
class uvm_object;
endclass

class uvm_event#(type T=uvm_object);


   typedef uvm_event#(T) this_type;


      typedef uvm_event#(T) cb_type;


     static local function bit m_register_cb();


	   return uvm_callbacks#(this_type,cb_type)::m_register_pair(


                                                "uvm_pkg::uvm_event#(T)",


                                               "uvm_pkg::uvm_event_callback#(T)"

 				                                     );


	endfunction : m_register_cb

endclass     

*/
