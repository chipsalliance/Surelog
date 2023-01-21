module GOOD();
endmodule

`define BSG_MAX(x,y) (((x)>(y)) ? (x) : (y))
`define BSG_MIN(x,y) (((x)<(y)) ? (x) : (y))
`define BSG_SAFE_CLOG2(x) ( ((x)==1) ? 1 : $clog2((x)))
`define BSG_SAFE_MINUS(x, y) (((x)<(y))) ? 0 : ((x)-(y))

`define BSG_SIGN_EXTEND(sig, width) \
  ({{`BSG_MAX(width-$bits(sig),0){sig[$bits(sig)-1]}}, sig[0+:`BSG_MIN(width, $bits(sig))]})

`define BSG_EASY(sig, width) \
  {`BSG_MAX(width-$bits(sig),0){1'b1}}

`define BSG_ZERO_EXTEND(sig, width) \
  ({{`BSG_MAX(width-$bits(sig),0){1'b0}}, sig[0+:`BSG_MIN(width, $bits(sig))]})

`define declare_bp_cache_req_s(data_width_mp, paddr_width_mp, cache_name_mp) \
  typedef struct packed                             \
  {                                                 \
    logic hit;                                      \
    logic [data_width_mp-1:0] data;                 \
    int size;                       \
    logic [paddr_width_mp-1:0] addr;                \
    int msg_type;               \
    int subop;                  \
  }  bp_``cache_name_mp``_req_s

`define bp_cache_req_width(data_width_mp, paddr_width_mp) \
  (1+data_width_mp+$bits(bp_cache_req_size_e)+paddr_width_mp+$bits(bp_cache_req_msg_type_e)+$bits(bp_cache_req_wr_subop_e))

`define declare_bp_cache_req_metadata_s(ways_mp, cache_name_mp) \
  typedef struct packed                                   \
  {                                                       \
    logic [`BSG_SAFE_CLOG2(ways_mp)-1:0] hit_or_repl_way; \
    logic dirty;                                          \
  }  bp_``cache_name_mp``_req_metadata_s

`define bp_cache_req_metadata_width(ways_mp) \
  (`BSG_SAFE_CLOG2(ways_mp)+1)

  typedef enum logic [1:0]
  {// write cache block
   e_cache_data_mem_write
   // read cache block
   ,e_cache_data_mem_read
   // write uncached load data
   ,e_cache_data_mem_uncached
  } bp_cache_data_mem_opcode_e;

  // Tag mem pkt opcodes
  typedef enum logic [2:0]
  {// clear all blocks in a set for a given index
   e_cache_tag_mem_set_clear
   // set tag and coherence state for given index and way_id
   ,e_cache_tag_mem_set_tag
   // set coherence state for given index and way_id
   ,e_cache_tag_mem_set_state
   // read tag mem packets for writeback and transfer (Used for UCE)
   ,e_cache_tag_mem_read
  } bp_cache_tag_mem_opcode_e;

  // Stat mem pkt opcodes
  typedef enum logic [1:0]
  {// clear all dirty bits and LRU bits to zero for given index.
   e_cache_stat_mem_set_clear
   // read stat_info for given index.
   ,e_cache_stat_mem_read
   // clear dirty bit for given index and way_id.
   ,e_cache_stat_mem_clear_dirty
  } bp_cache_stat_mem_opcode_e;

`define declare_bp_cache_data_mem_pkt_s(sets_mp, ways_mp, block_data_width_mp, fill_width_mp, cache_name_mp) \
  typedef struct packed                                                                     \
  {                                                                                         \
    logic [`BSG_SAFE_CLOG2(sets_mp)-1:0]            index;                                  \
    logic [`BSG_SAFE_CLOG2(ways_mp)-1:0]            way_id;                                 \
    logic [fill_width_mp-1:0]                       data;                                   \
    logic [(block_data_width_mp/fill_width_mp)-1:0] fill_index;                             \
    bp_cache_data_mem_opcode_e                      opcode;                                 \
  }  bp_``cache_name_mp``_data_mem_pkt_s

`define bp_cache_data_mem_pkt_width(sets_mp, ways_mp, block_data_width_mp, fill_width_mp)   \
  (`BSG_SAFE_CLOG2(sets_mp)+`BSG_SAFE_CLOG2(ways_mp)+fill_width_mp                          \
   +(block_data_width_mp/fill_width_mp)+$bits(bp_cache_data_mem_opcode_e))

`define declare_bp_cache_tag_mem_pkt_s(sets_mp, ways_mp, tag_width_mp, cache_name_mp) \
  typedef struct packed                                                          \
  {                                                                              \
    logic [`BSG_SAFE_CLOG2(sets_mp)-1:0]        index;                           \
   logic [`BSG_SAFE_CLOG2(ways_mp)-1:0]        way_id;                          \
    int                             state;                           \
    logic [tag_width_mp-1:0]                    tag;                             \
    int                   opcode;                          \
  }  bp_``cache_name_mp``_tag_mem_pkt_s

`define bp_cache_tag_mem_pkt_width(sets_mp, ways_mp, tag_width_mp) \
  (`BSG_SAFE_CLOG2(sets_mp)+`BSG_SAFE_CLOG2(ways_mp)+$bits(bp_coh_states_e)+tag_width_mp+$bits(bp_cache_tag_mem_opcode_e))

`define declare_bp_cache_tag_info_s(tag_width_mp, cache_name_mp) \
  typedef struct packed {                                                 \
    logic [$bits(bp_coh_states_e)-1:0] state;                             \
    logic [tag_width_mp-1:0]           tag;                               \
  }  bp_``cache_name_mp``_tag_info_s;

`define bp_cache_tag_info_width(tag_width_mp) \
  ($bits(bp_coh_states_e)+tag_width_mp)

`define declare_bp_cache_stat_mem_pkt_s(sets_mp, ways_mp, cache_name_mp)  \
  typedef struct packed                                                   \
  {                                                                       \
    logic [`BSG_SAFE_CLOG2(sets_mp)-1:0]    index;                        \
    logic [`BSG_SAFE_CLOG2(ways_mp)-1:0]    way_id;                       \
    int              opcode;                       \
  }  bp_``cache_name_mp``_stat_mem_pkt_s

`define bp_cache_stat_mem_pkt_width(sets_mp, ways_mp) \
  (`BSG_SAFE_CLOG2(sets_mp)+`BSG_SAFE_CLOG2(ways_mp)+$bits(bp_cache_stat_mem_opcode_e))

`define declare_bp_cache_stat_info_s(ways_mp, cache_name_mp)  \
  typedef struct packed                          \
  {                                              \
    logic [`BSG_SAFE_MINUS(ways_mp, 2):0] lru;   \
    logic [ways_mp-1:0]                   dirty; \
  }  bp_``cache_name_mp``_stat_info_s

// Direct mapped caches need 2-bits in the stat info
`define bp_cache_stat_info_width(ways_mp) \
  (`BSG_MAX(2,2*ways_mp-1))

`define declare_bp_cache_engine_if(addr_width_mp, tag_width_mp, sets_mp, ways_mp, req_data_width_mp, block_data_width_mp, fill_width_mp, cache_name_mp) \
  `declare_bp_cache_req_s(req_data_width_mp, addr_width_mp, cache_name_mp);                              \
  `declare_bp_cache_req_metadata_s(ways_mp, cache_name_mp);                                              \
  `declare_bp_cache_data_mem_pkt_s(sets_mp, ways_mp, block_data_width_mp, fill_width_mp, cache_name_mp); \
  `declare_bp_cache_tag_mem_pkt_s(sets_mp, ways_mp, tag_width_mp, cache_name_mp);                        \
  `declare_bp_cache_tag_info_s(tag_width_mp, cache_name_mp);                                             \
  `declare_bp_cache_stat_mem_pkt_s(sets_mp, ways_mp, cache_name_mp);                                     \
  `declare_bp_cache_stat_info_s(ways_mp, cache_name_mp);



module top();
  parameter dword_width_gp = 48;
  wire [12:0] pc;
  reg [12:0] bp_coh_states_e;
  assign pc = 11;
  parameter int paddr_width_p = 12;
  parameter int assoc_p = 13;
  parameter int sets_p = 14;
  parameter int fill_width_p = 15;
  parameter int block_width_p = 16;
  parameter int  ctag_width_p = 17;
`declare_bp_cache_engine_if(paddr_width_p, ctag_width_p, sets_p, assoc_p, dword_width_gp, block_width_p, fill_width_p, icache);
wire [dword_width_gp-1:0] pc_sext_li = `BSG_SIGN_EXTEND(pc, dword_width_gp);

parameter easy = `BSG_EASY(pc, dword_width_gp);
  
if (easy == 35'b11111111111111111111111111111111111) begin
    GOOD good();
end

  initial $display("easy: %d",easy);
  
endmodule