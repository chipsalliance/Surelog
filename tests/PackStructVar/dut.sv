package top_pkg;
	localparam int TL_AW=32;
	localparam int TL_DW=32;    // = TL_DBW * 8; TL_DBW must be a power-of-two
	localparam int TL_AIW=8;    // a_source, d_source
	localparam int TL_DIW=1;    // d_sink
	localparam int TL_DUW=16;   // d_user
	localparam int TL_DBW=(TL_DW>>3);
	localparam int TL_SZW=$clog2($clog2(TL_DBW)+1);
	localparam int FLASH_BANKS=2;
	localparam int FLASH_PAGES_PER_BANK=256;
	localparam int FLASH_WORDS_PER_PAGE=256;
	localparam int FLASH_BYTES_PER_WORD=4;
endpackage


package tlul_pkg;

	typedef enum logic [2:0] {
	  AccessAck     = 3'h 0,
	  AccessAckData = 3'h 1
	} tl_d_op_e;
  
  
	typedef struct packed {
	  logic                         d_valid;
	  tl_d_op_e                     d_opcode;
	  logic                  [2:0]  d_param;
	  logic  [top_pkg::TL_SZW-1:0]  d_size;   // Bouncing back a_size
	  logic  [top_pkg::TL_AIW-1:0]  d_source;
	  logic  [top_pkg::TL_DIW-1:0]  d_sink;
	  logic   [top_pkg::TL_DW-1:0]  d_data;
	  logic  [top_pkg::TL_DUW-1:0]  d_user;
	  logic                         d_error;
  
	  logic                         a_ready;
	} tl_h2d_t;
  
  endpackage
  

module flash_ctrl ();
  
	
	tlul_pkg::tl_h2d_t tl_fifo_h2d [2];

	
endmodule

