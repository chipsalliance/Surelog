package top_pkg;

  localparam TL_AW=32;
  localparam TL_DW=32;    // = TL_DBW * 8; TL_DBW must be a power-of-two
  localparam TL_AIW=8;    // a_source, d_source
  localparam TL_DIW=1;    // d_sink
  localparam TL_DUW=16;   // d_user
  localparam TL_DBW=(TL_DW>>3);
  localparam TL_SZW=$clog2($clog2(TL_DBW)+1);
  localparam FLASH_BANKS=2;
  localparam FLASH_PAGES_PER_BANK=256;
  localparam FLASH_WORDS_PER_PAGE=256;
  localparam FLASH_BYTES_PER_WORD=4;
  localparam FLASH_BKW = $clog2(FLASH_BANKS);
  localparam FLASH_PGW = $clog2(FLASH_PAGES_PER_BANK);
  localparam FLASH_WDW = $clog2(FLASH_WORDS_PER_PAGE);
  localparam FLASH_AW = FLASH_BKW + FLASH_PGW + FLASH_WDW;
  localparam FLASH_DW = FLASH_BYTES_PER_WORD * 8;
  
  endpackage

package tlul_pkg;

  typedef struct packed {
    logic                         b_valid;
  } tl_a_op_e;

  typedef struct packed {
    logic                         b_valid;
  } tl_a_user_t;
   
  typedef struct packed {
    logic                         a_valid;
    tl_a_op_e                     a_opcode;
    logic                  [2:0]  a_param;
    logic  [top_pkg::TL_SZW-1:0]  a_size;
    logic  [top_pkg::TL_AIW-1:0]  a_source;
    logic   [top_pkg::TL_AW-1:0]  a_address;
    logic  [top_pkg::TL_DBW-1:0]  a_mask;
    logic   [top_pkg::TL_DW-1:0]  a_data;
    tl_a_user_t                   a_user;

    logic                         d_ready;
  } tl_h2d_t;

endpackage

package hmac_pkg;

  // this currently uses the
  // fully asynchronous implemenation
  localparam int NumAlerts = 1;
  localparam logic [NumAlerts-1:0] AlertAsyncOn = NumAlerts'(1'b1);

  localparam int MsgFifoDepth = 16;

  localparam int NumRound = 64;   // SHA-224, SHA-256

  typedef logic [31:0] sha_word_t;
  localparam int WordByte = $bits(sha_word_t)/8;

endpackage


package flash_ctrl_pkg;
typedef enum logic  {
  PageErase     = 0,
  BankErase     = 1
} flash_erase_op_e;

typedef logic [31:0] sha_word_t;
endpackage


module dut( input  tlul_pkg::tl_h2d_t tl_h_i );
  import flash_ctrl_pkg::*;

  localparam int WordByte = $bits(sha_word_t)/8;

  localparam int DataWidth = top_pkg::FLASH_DW;
  localparam int DataBitWidth = $clog2(DataWidth/8);
  localparam int EraseBitWidth = $bits(flash_erase_op_e);

  localparam int unsigned HashWordBits = $clog2($bits(sha_word_t));

  localparam int unsigned REQFIFO_WIDTH = $bits(tlul_pkg::tl_h2d_t)-2;

  logic [$bits(tl_h_i.a_source)-1:0] err_source;
  logic [$bits(tl_h_i.a_size)-1:0]   err_size;

  
  typedef struct {
    logic valid;
    bit [8:1] data;
    } MyType;

  typedef bit[$bits(MyType):1] MyBits; //same as typedef bit [9:1] MyBits;
  MyBits b;
  

endmodule


module dmi_jtag ();

  typedef struct packed {
    logic [6:0]  address;
    logic [31:0] data;
    logic [1:0]  op;
  } dmi_t;

  logic [$bits(dmi_t)-1:0] dr_d, dr_q;
  
  dmi_t  dmi;
  assign dmi          = dmi_t'(dr_q);
  
  always_comb begin : p_shift

    if (shift_dr) begin
      if (dmi_access) begin
        dr_d = {dmi_tdi, dr_q[$bits(dr_q)-1:1]};
      end
    end

  end

endmodule : dmi_jtag


