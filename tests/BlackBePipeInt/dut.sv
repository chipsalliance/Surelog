

  


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























































// Direct mapped caches need 2-bits in the stat info
























/**
*
* bp_common_core_if.svh
*
* bp_core_interface.svh declares the interface between the BlackParrot Front End
* and Back End For simplicity and flexibility, these signals are declared as
* parameterizable structures. Each structure declares its width separately to
* avoid preprocessor ordering issues.
*
* Logically, the BE controls the FE and may command the FE to flush all the states,
* redirect the PC, etc. The FE uses its queue to supply the BE with (possibly
* speculative) instruction/PC pairs and inform the BE of any exceptions that have
* occurred within the unit (e.g., misaligned instruction fetch) so the BE may
* ensure all exceptions are taken precisely.  The BE checks the PC in the
* instruction/PC pairs to make sure that the FE predictions correspond to
* correct architectural execution.
*
* NOTE: VCS can only handle packed unions where each member is the same size. Therefore, we
*         need to do some macro hacking to get parameterized unions to work nicely.
* NOTE: Potentially could make sense to separate two unidirectional interface files. This one
*         is a little overwhelming.
*/




/*
* Clients need only use this macro to declare all parameterized structs for FE<->BE interface.
*/











































































































































































/*
* Declare all fe-be widths at once as localparams
*/




/* Declare width macros so that clients can use structs in ports before struct declaration */



























/* Ensure all members of packed unions have the same size. If parameterized unions are desired,
* examine this code carefully. Else, clients should not have to use these macros
*/


































































/*
* This macro allows users to log to different mediums depending on a parameter
*   print_type_mp - The different outputs as a bitmask
*     0 - stdout ($display without newline)
*     1 - file
*   file_mp - The name of the log file, optional if using stdout
*   str_mp - This is the format string for the print statement. Must be enclosed in parentheses
*
* Example usage -
*  `BP_LOG(0, `BP_LOG_STDOUT, ("I'm a display log %d", 2));
*  `BP_LOG(file, `BP_LOG_FILE, ("I'm a file log %d %d", 1, 2));
*  `BP_LOG(file, `BP_LOG_STDOUT | `BP_LOG_FILE, ("I'm both! %d", 3));
*  `BP_LOG(0, `BP_LOG_NONE, ("I'm neither %d", 4));
*
* In practice, we expect users will set the log level as a module parameter rather than in the
*   macro.
* An obvious enhancement is to add log levels to control verbosity. A less obvious enhancement is
*   to support ordering of logs through a parameter. Perhaps #``delay_mp``
*/
localparam bp_log_none_gp   = 0;
localparam bp_log_stdout_gp = 1;
localparam bp_log_file_gp   = 2;


















/**
*
* bp_common_rv64_instr_defines.svh
* Based off of: https://bitbucket.org/taylor-bsg/bsg_manycore/src/master/v/vanilla_bean/parameters.v
*/




/* RISCV definitions */






















// Some useful RV64 instruction macros






// RV64 Immediate sign extension macros









// I extension


































































// A extension























// M extension















// F extension































// D extension














































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/* verilator lint_on UNUSED */












package bp_common_pkg;




//vector-dot-product accelerator CSR indexes
localparam inputa_ptr_csr_idx_gp = 20'h0_0000;
localparam inputb_ptr_csr_idx_gp = 20'h0_0008; 
localparam input_len_csr_idx_gp  = 20'h0_0010;
localparam start_cmd_csr_idx_gp  = 20'h0_0018;
localparam res_status_csr_idx_gp = 20'h0_0020;
localparam res_ptr_csr_idx_gp    = 20'h0_0028;
localparam res_len_csr_idx_gp    = 20'h0_0030;
localparam operation_csr_idx_gp  = 20'h0_0038;


//loopback accelerator CSR indexes
localparam accel_wr_cnt_csr_idx_gp = 20'h0_0000;






// TODO: These could be parameterizable, but there are some constraints of
//   of bit placement within the local uncached space.
// TL;DR 16MB ought to be enough for anyone
localparam tile_id_width_gp  = 7;
localparam dev_id_width_gp   = 4;
localparam dev_addr_width_gp = 20;

localparam host_dev_gp  = 1;
localparam cfg_dev_gp   = 2;
localparam clint_dev_gp = 3;
localparam cache_dev_gp = 4;

                          // 0x00_0(nnnN)(D)(A_AAAA)
localparam host_dev_base_addr_gp     = 32'h0010_0000;
localparam cfg_dev_base_addr_gp      = 32'h0020_0000;
localparam clint_dev_base_addr_gp    = 32'h0030_0000;
localparam cache_dev_base_addr_gp    = 32'h0040_0000;

// TODO: This is hardcoded for a 32-bit DRAM address, will need to be adjusted
//   for a different address space
localparam boot_base_addr_gp         = 40'h00_0011_0000;
localparam dram_base_addr_gp         = 40'h00_8000_0000;
localparam dram_uc_base_addr_gp      = 40'h01_0000_0000;
localparam coproc_base_addr_gp       = 40'h02_0000_0000;
localparam global_base_addr_gp       = 40'h03_0000_0000;











// Suitably high enough to not run out of configs.
localparam max_cfgs    = 128;
localparam lg_max_cfgs = $clog2(max_cfgs);

// Configuration enums
typedef enum logic [2:0]
{
 e_cfg_enabled               = 3'b000
 ,e_cfg_coherent             = 3'b001
 ,e_cfg_writeback            = 3'b010
 ,e_cfg_word_tracking        = 3'b011
 ,e_cfg_lr_sc                = 3'b100
 ,e_cfg_amo_swap             = 3'b101
 ,e_cfg_amo_fetch_logic      = 3'b110
 ,e_cfg_amo_fetch_arithmetic = 3'b111
} bp_cache_features_e;

typedef enum logic [1:0]
{
 e_div   = 2'b00
 ,e_mul  = 2'b01
 ,e_mulh = 2'b10
} bp_muldiv_support_e;

typedef enum logic [15:0]
{
 e_sacc_none = 0
 ,e_sacc_vdp = 1
 ,e_sacc_scratchpad = 2
} bp_sacc_type_e;

typedef enum logic [15:0]
{
 e_cacc_none = 0
 ,e_cacc_vdp = 1
} bp_cacc_type_e;

typedef enum logic [1:0]
{
 e_cce_uce = 0
 ,e_cce_fsm = 1
 ,e_cce_ucode = 2
 ,e_cce_hybrid = 3
} bp_cce_type_e;

typedef struct packed
{
 // Dimensions of the different complexes
 // Core Complex may be any integer unsigned (though has only been validated up to 4x4)
 // All other Complexes are 1-dimensional
 //                                    [                           ]
 //                                    [        I/O Complex        ]
 //                                    [                           ]
 //
 //  [                               ] [                           ] [                               ]
 //  [ Streaming Accelerator Complex ] [        Core Complex       ] [ Coherent Accelerator Complex  ]
 //  [                               ] [                           ] [                               ]
 //
 //                                    [                           ]
 //                                    [       Memory Complex      ]
 //                                    [                           ]
 //
 integer unsigned cc_x_dim;
 integer unsigned cc_y_dim;
 integer unsigned ic_y_dim;
 integer unsigned mc_y_dim;
 integer unsigned cac_x_dim;
 integer unsigned sac_x_dim;

 // The type of accelerator in the accelerator complexes, selected out of bp_cacc_type_e/bp_sacc_type_e
 // Only supports homogeneous configurations
 integer unsigned cacc_type;
 integer unsigned sacc_type;

 // Number of CCEs/LCEs in the system. Must be consistent within complex dimensions
 integer unsigned num_cce;
 integer unsigned num_lce;

 // Virtual address width
 //   Only tested for SV39 (39-bit virtual address)
 integer unsigned vaddr_width;
 // Physical address width
 //   Only tested for 40-bit physical address
 integer unsigned paddr_width;
 // DRAM address width
 // The max size of the connected DRAM i.e. cached address space
 //   Only tested for 32-bit cacheable address (4 GB space, with 2 GB local I/O)
 integer unsigned daddr_width;
 // Cacheable address width
 // The max size cached by the L1 caches of the system
 integer unsigned caddr_width;
 // Address space ID width
 //   Currently unused, so set to 1 bit
 integer unsigned asid_width;

 // Branch metadata information for the Front End
 // Must be kept consistent with FE
 integer unsigned branch_metadata_fwd_width;
 integer unsigned btb_tag_width;
 integer unsigned btb_idx_width;
 // bht_row_els is a physically-derived parameter. It describes the number
 //   of entries in a single row of the BHT RAM.  There are 2 bits per entry.
 //   The tradeoff here is a wider RAM is most likely higher performance,
 //   but we need to carry that extra metadata throughout the pipeline to
 //   maintain 1r1w throughput without a RMW.
 // Ghist is the global history width, which in our gselect
 // Thus, the true BHT dimensions are (bht_idx_width+ghist_width)x(2*bht_row_els)
 integer unsigned bht_idx_width;
 integer unsigned bht_row_els;
 integer unsigned ghist_width;

 // Capacity of the Instruction/Data TLBs
 integer unsigned itlb_els_4k;
 integer unsigned itlb_els_1g;
 integer unsigned dtlb_els_4k;
 integer unsigned dtlb_els_1g;

 // I$ cache features
 integer unsigned icache_features;
 // I$ parameterizations
 integer unsigned icache_sets;
 integer unsigned icache_assoc;
 integer unsigned icache_block_width;
 integer unsigned icache_fill_width;

 // D$ cache features
 integer unsigned dcache_features;
 // D$ parameterizations
 integer unsigned dcache_sets;
 integer unsigned dcache_assoc;
 integer unsigned dcache_block_width;
 integer unsigned dcache_fill_width;

 // A$ cache features
 integer unsigned acache_features;
 // A$ parameterizations
 integer unsigned acache_sets;
 integer unsigned acache_assoc;
 integer unsigned acache_block_width;
 integer unsigned acache_fill_width;

 // CCE selection and parameters
 // cce_type defined by bp_cce_type_e
 integer unsigned cce_type;
 // Determines the size of the CCE instruction RAM
 integer unsigned cce_pc_width;
 // The width of the coherence protocol beats
 integer unsigned bedrock_data_width;

 // L2 slice parameters (per core)
 // L2 cache features
 integer unsigned l2_features;
 // Number of L2 banks present in the slice
 integer unsigned l2_banks;
 integer unsigned l2_data_width;
 integer unsigned l2_sets;
 integer unsigned l2_assoc;
 integer unsigned l2_block_width;
 integer unsigned l2_fill_width;
 // Number of requests which can be pending in a cache slice
 // Should be 4 < N < 4*l2_banks_p to prevent stalling
 integer unsigned l2_outstanding_reqs;

 // Size of the issue queue
 integer unsigned fe_queue_fifo_els;
 // Size of the cmd queue
 integer unsigned fe_cmd_fifo_els;
 // MULDIV support in the system. It is a bitmask with:
 //   bit 0: div
 //   bit 1: mul
 //   bit 2: mulh
 integer unsigned muldiv_support;
 // Whether to emulate FPU
 //   bit 0: fpu enabled
 integer unsigned fpu_support;
 // Whether to enable the "c" extension.
 // Currently, this only enables support for misaligned 32-bit instructions; full "C" support is not yet implemented.
 integer unsigned compressed_support;

 // Whether the coherence network is on the core clock or on its own clock
 integer unsigned async_coh_clk;
 // Flit width of the coherence network. Has major impact on latency / area of the network
 integer unsigned coh_noc_flit_width;
 // Concentrator ID width of the coherence network. Corresponds to how many nodes can be on a
 //   single wormhole router
 integer unsigned coh_noc_cid_width;
 // Maximum number of flits in a single wormhole message. Determined by protocol and affects
 //   buffer size
 integer unsigned coh_noc_len_width;
 // Maximum credits supported by the network. Correlated to the bandwidth delay product
 integer unsigned coh_noc_max_credits;

 // Whether the memory network is on the core clock or on its own clock
 integer unsigned async_mem_clk;
 // Flit width of the memory network. Has major impact on latency / area of the network
 integer unsigned mem_noc_flit_width;
 // Concentrator ID width of the memory network. Corresponds to how many nodes can be on a
 //   single wormhole router
 integer unsigned mem_noc_cid_width;
 // Maximum number of flits in a single wormhole message. Determined by protocol and affects
 //   buffer size
 integer unsigned mem_noc_len_width;
 // Maximum credits supported by the network. Correlated to the bandwidth delay product
 integer unsigned mem_noc_max_credits;

 // Whether the I/O network is on the core clock or on its own clock
 integer unsigned async_io_clk;
 // Flit width of the I/O network. Has major impact on latency / area of the network
 integer unsigned io_noc_flit_width;
 // Concentrator ID width of the I/O network. Corresponds to how many nodes can be on a
 //   single wormhole router
 integer unsigned io_noc_cid_width;
 // Domain ID width of the I/O network. Corresponds to how many chips compose a multichip chain
 integer unsigned io_noc_did_width;
 // Maximum number of flits in a single wormhole message. Determined by protocol and affects
 //   buffer size
 integer unsigned io_noc_len_width;
 // Maximum credits supported by the network. Correlated to the bandwidth delay product
 integer unsigned io_noc_max_credits;

}  bp_proc_param_s;

localparam bp_proc_param_s bp_default_cfg_p =
 '{cc_x_dim  : 1
   ,cc_y_dim : 1
   ,ic_y_dim : 0
   ,mc_y_dim : 0
   ,cac_x_dim: 0
   ,sac_x_dim: 0
   ,cacc_type: e_cacc_none
   ,sacc_type: e_sacc_none

   ,num_cce: 1
   ,num_lce: 2

   ,vaddr_width: 39
   ,paddr_width: 40
   ,daddr_width: 33
   ,caddr_width: 32
   ,asid_width : 1

   ,branch_metadata_fwd_width: 39
   ,btb_tag_width            : 9
   ,btb_idx_width            : 6
   ,bht_idx_width            : 7
   ,bht_row_els              : 4
   ,ghist_width              : 2

   ,itlb_els_4k : 8
   ,dtlb_els_4k : 8
   ,itlb_els_1g : 0
   ,dtlb_els_1g : 0

   ,dcache_features      : (1 << e_cfg_enabled)
                           | (1 << e_cfg_writeback)
                           | (1 << e_cfg_lr_sc)
                           | (1 << e_cfg_amo_swap)
                           | (1 << e_cfg_amo_fetch_logic)
                           | (1 << e_cfg_amo_fetch_arithmetic)
   ,dcache_sets          : 64
   ,dcache_assoc         : 8
   ,dcache_block_width   : 512
   ,dcache_fill_width    : 64

   ,icache_features      : (1 << e_cfg_enabled)
   ,icache_sets          : 64
   ,icache_assoc         : 8
   ,icache_block_width   : 512
   ,icache_fill_width    : 64

   ,acache_features      : (1 << e_cfg_enabled)
   ,acache_sets          : 64
   ,acache_assoc         : 8
   ,acache_block_width   : 512
   ,acache_fill_width    : 64

   ,cce_type             : e_cce_uce
   ,cce_pc_width         : 8
   ,bedrock_data_width   : 64

   ,l2_features          : (1 << e_cfg_enabled)
                           | (1 << e_cfg_writeback)
                           | (1 << e_cfg_word_tracking)
                           | (1 << e_cfg_amo_swap)
                           | (1 << e_cfg_amo_fetch_logic)
                           | (1 << e_cfg_amo_fetch_arithmetic)
   ,l2_banks            : 2
   ,l2_data_width       : 64
   ,l2_sets             : 128
   ,l2_assoc            : 8
   ,l2_block_width      : 512
   ,l2_fill_width       : 64
   ,l2_outstanding_reqs : 6

   ,fe_queue_fifo_els : 8
   ,fe_cmd_fifo_els   : 4
   ,muldiv_support    : (1 << e_div) | (1 << e_mul) | (1 << e_mulh)
   ,fpu_support       : 1
   ,compressed_support: 1

   ,async_coh_clk       : 0
   ,coh_noc_flit_width  : 128
   ,coh_noc_cid_width   : 2
   ,coh_noc_len_width   : 3
   ,coh_noc_max_credits : 8

   ,async_mem_clk         : 0
   ,mem_noc_flit_width    : 64
   ,mem_noc_cid_width     : 2
   ,mem_noc_len_width     : 4
   ,mem_noc_max_credits   : 8

   ,async_io_clk         : 0
   ,io_noc_flit_width    : 64
   ,io_noc_cid_width     : 2
   ,io_noc_did_width     : 3
   ,io_noc_len_width     : 4
   ,io_noc_max_credits   : 16
   };

// BP_CUSTOM_DEFINES_PATH can be set to a file which has the custom defines below set
// Or, you can override the empty one in bp_common/src/include

 



 

// Custom, tick define-based configuration
localparam bp_proc_param_s bp_custom_cfg_p =
 '{
                                                        
   cc_x_dim: bp_default_cfg_p.cc_x_dim             
   

   ,
                                                        
   cc_y_dim: bp_default_cfg_p.cc_y_dim             
   

   ,
                                                        
   ic_y_dim: bp_default_cfg_p.ic_y_dim             
   

   ,
                                                        
   mc_y_dim: bp_default_cfg_p.mc_y_dim             
   

   ,
                                                        
   cac_x_dim: bp_default_cfg_p.cac_x_dim             
   

   ,
                                                        
   sac_x_dim: bp_default_cfg_p.sac_x_dim             
   

   ,
                                                        
   cacc_type: bp_default_cfg_p.cacc_type             
   

   ,
                                                        
   sacc_type: bp_default_cfg_p.sacc_type             
   


   ,
                                                        
   num_cce: bp_default_cfg_p.num_cce             
   

   ,
                                                        
   num_lce: bp_default_cfg_p.num_lce             
   


   ,
                                                        
   vaddr_width: bp_default_cfg_p.vaddr_width             
   

   ,
                                                        
   paddr_width: bp_default_cfg_p.paddr_width             
   

   ,
                                                        
   daddr_width: bp_default_cfg_p.daddr_width             
   

   ,
                                                        
   caddr_width: bp_default_cfg_p.caddr_width             
   

   ,
                                                        
   asid_width: bp_default_cfg_p.asid_width             
   


   ,
                                                        
   fe_queue_fifo_els: bp_default_cfg_p.fe_queue_fifo_els             
   

   ,
                                                        
   fe_cmd_fifo_els: bp_default_cfg_p.fe_cmd_fifo_els             
   

   ,
                                                        
   muldiv_support: bp_default_cfg_p.muldiv_support             
   

   ,
                                                        
   fpu_support: bp_default_cfg_p.fpu_support             
   

   ,
                                                        
   compressed_support: bp_default_cfg_p.compressed_support             
   


   ,
                                                        
   branch_metadata_fwd_width: bp_default_cfg_p.branch_metadata_fwd_width             
   

   ,
                                                        
   btb_tag_width: bp_default_cfg_p.btb_tag_width             
   

   ,
                                                        
   btb_idx_width: bp_default_cfg_p.btb_idx_width             
   

   ,
                                                        
   bht_idx_width: bp_default_cfg_p.bht_idx_width             
   

   ,
                                                        
   bht_row_els: bp_default_cfg_p.bht_row_els             
   

   ,
                                                        
   ghist_width: bp_default_cfg_p.ghist_width             
   


   ,
                                                        
   itlb_els_4k: bp_default_cfg_p.itlb_els_4k             
   

   ,
                                                        
   itlb_els_1g: bp_default_cfg_p.itlb_els_1g             
   

   ,
                                                        
   dtlb_els_4k: bp_default_cfg_p.dtlb_els_4k             
   

   ,
                                                        
   dtlb_els_1g: bp_default_cfg_p.dtlb_els_1g             
   


   ,
                                                        
   icache_features: bp_default_cfg_p.icache_features             
   

   ,
                                                        
   icache_sets: bp_default_cfg_p.icache_sets             
   

   ,
                                                        
   icache_assoc: bp_default_cfg_p.icache_assoc             
   

   ,
                                                        
   icache_block_width: bp_default_cfg_p.icache_block_width             
   

   ,
                                                        
   icache_fill_width: bp_default_cfg_p.icache_fill_width             
   


   ,
                                                        
   dcache_features: bp_default_cfg_p.dcache_features             
   

   ,
                                                        
   dcache_sets: bp_default_cfg_p.dcache_sets             
   

   ,
                                                        
   dcache_assoc: bp_default_cfg_p.dcache_assoc             
   

   ,
                                                        
   dcache_block_width: bp_default_cfg_p.dcache_block_width             
   

   ,
                                                        
   dcache_fill_width: bp_default_cfg_p.dcache_fill_width             
   


   ,
                                                        
   acache_features: bp_default_cfg_p.acache_features             
   

   ,
                                                        
   acache_sets: bp_default_cfg_p.acache_sets             
   

   ,
                                                        
   acache_assoc: bp_default_cfg_p.acache_assoc             
   

   ,
                                                        
   acache_block_width: bp_default_cfg_p.acache_block_width             
   

   ,
                                                        
   acache_fill_width: bp_default_cfg_p.acache_fill_width             
   


   ,
                                                        
   cce_type: bp_default_cfg_p.cce_type             
   

   ,
                                                        
   cce_pc_width: bp_default_cfg_p.cce_pc_width             
   

   ,
                                                        
   bedrock_data_width: bp_default_cfg_p.bedrock_data_width             
   


   ,
                                                        
   l2_features: bp_default_cfg_p.l2_features             
   

   ,
                                                        
   l2_banks: bp_default_cfg_p.l2_banks             
   

   ,
                                                        
   l2_data_width: bp_default_cfg_p.l2_data_width             
   

   ,
                                                        
   l2_sets: bp_default_cfg_p.l2_sets             
   

   ,
                                                        
   l2_assoc: bp_default_cfg_p.l2_assoc             
   

   ,
                                                        
   l2_block_width: bp_default_cfg_p.l2_block_width             
   

   ,
                                                        
   l2_fill_width: bp_default_cfg_p.l2_fill_width             
   

   ,
                                                        
   l2_outstanding_reqs: bp_default_cfg_p.l2_outstanding_reqs             
   


   ,
                                                        
   async_coh_clk: bp_default_cfg_p.async_coh_clk             
   

   ,
                                                        
   coh_noc_max_credits: bp_default_cfg_p.coh_noc_max_credits             
   

   ,
                                                        
   coh_noc_flit_width: bp_default_cfg_p.coh_noc_flit_width             
   

   ,
                                                        
   coh_noc_cid_width: bp_default_cfg_p.coh_noc_cid_width             
   

   ,
                                                        
   coh_noc_len_width: bp_default_cfg_p.coh_noc_len_width             
   


   ,
                                                        
   async_mem_clk: bp_default_cfg_p.async_mem_clk             
   

   ,
                                                        
   mem_noc_max_credits: bp_default_cfg_p.mem_noc_max_credits             
   

   ,
                                                        
   mem_noc_flit_width: bp_default_cfg_p.mem_noc_flit_width             
   

   ,
                                                        
   mem_noc_cid_width: bp_default_cfg_p.mem_noc_cid_width             
   

   ,
                                                        
   mem_noc_len_width: bp_default_cfg_p.mem_noc_len_width             
   


   ,
                                                        
   async_io_clk: bp_default_cfg_p.async_io_clk             
   

   ,
                                                        
   io_noc_max_credits: bp_default_cfg_p.io_noc_max_credits             
   

   ,
                                                        
   io_noc_flit_width: bp_default_cfg_p.io_noc_flit_width             
   

   ,
                                                        
   io_noc_cid_width: bp_default_cfg_p.io_noc_cid_width             
   

   ,
                                                        
   io_noc_did_width: bp_default_cfg_p.io_noc_did_width             
   

   ,
                                                        
   io_noc_len_width: bp_default_cfg_p.io_noc_len_width             
   

   };








localparam host_base_addr_gp         = (dev_id_width_gp+dev_addr_width_gp)'('h0010_0000);
localparam host_match_addr_gp        = (dev_id_width_gp+dev_addr_width_gp)'('h001?_????);

localparam getchar_base_addr_gp      = (dev_addr_width_gp)'('h0_0000);
localparam getchar_match_addr_gp     = (dev_addr_width_gp)'('h0_0???);

localparam putchar_base_addr_gp      = (dev_addr_width_gp)'('h0_1000);
localparam putchar_match_addr_gp     = (dev_addr_width_gp)'('h0_1???);

localparam finish_base_addr_gp       = (dev_addr_width_gp)'('h0_2000);
localparam finish_match_addr_gp      = (dev_addr_width_gp)'('h0_2???);

localparam putch_core_base_addr_gp   = (dev_addr_width_gp)'('h0_3000);
localparam putch_core_match_addr_gp  = (dev_addr_width_gp)'('h0_3???);

localparam finish_all_addr_gp        = (dev_addr_width_gp)'('h0_4000);

localparam bootrom_base_addr_gp      = (dev_addr_width_gp)'('h1_0000);
localparam bootrom_match_addr_gp     = (dev_addr_width_gp)'('h1_????);

localparam paramrom_base_addr_gp     = (dev_addr_width_gp)'('h2_0000);
localparam paramrom_match_addr_gp    = (dev_addr_width_gp)'('h2_????);





// Default configuration is unicore
localparam bp_proc_param_s bp_unicore_cfg_p = bp_default_cfg_p;

localparam bp_proc_param_s bp_unicore_megaparrot_override_p =
 '{paddr_width : 56
   ,daddr_width: 55
   ,caddr_width: 54

   ,branch_metadata_fwd_width: 42
   ,btb_tag_width            : 9
   ,btb_idx_width            : 8
   ,bht_idx_width            : 8
   ,bht_row_els              : 4
   ,ghist_width              : 2

   ,icache_sets        : 64
   ,icache_assoc       : 8
   ,icache_block_width : 512
   ,icache_fill_width  : 512

   ,dcache_sets        : 64
   ,dcache_assoc       : 8
   ,dcache_block_width : 512
   ,dcache_fill_width  : 512

   ,l2_banks            : 8
   ,l2_data_width       : 512
   ,l2_sets             : 128
   ,l2_assoc            : 8
   ,l2_block_width      : 512
   ,l2_fill_width       : 512
   ,l2_outstanding_reqs : 32

   ,default : "inv"
   };

   localparam bp_proc_param_s bp_unicore_megaparrot_cfg_p =                                                     
     '{
   cc_x_dim: (bp_unicore_megaparrot_override_p.cc_x_dim == "inv") 
                 ? bp_unicore_cfg_p.cc_x_dim           
                 : bp_unicore_megaparrot_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_unicore_megaparrot_override_p.cc_y_dim == "inv") 
                 ? bp_unicore_cfg_p.cc_y_dim           
                 : bp_unicore_megaparrot_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_unicore_megaparrot_override_p.ic_y_dim == "inv") 
                 ? bp_unicore_cfg_p.ic_y_dim           
                 : bp_unicore_megaparrot_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_unicore_megaparrot_override_p.mc_y_dim == "inv") 
                 ? bp_unicore_cfg_p.mc_y_dim           
                 : bp_unicore_megaparrot_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_unicore_megaparrot_override_p.cac_x_dim == "inv") 
                 ? bp_unicore_cfg_p.cac_x_dim           
                 : bp_unicore_megaparrot_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_unicore_megaparrot_override_p.sac_x_dim == "inv") 
                 ? bp_unicore_cfg_p.sac_x_dim           
                 : bp_unicore_megaparrot_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_unicore_megaparrot_override_p.cacc_type == "inv") 
                 ? bp_unicore_cfg_p.cacc_type           
                 : bp_unicore_megaparrot_override_p.cacc_type          
            
       ,
   sacc_type: (bp_unicore_megaparrot_override_p.sacc_type == "inv") 
                 ? bp_unicore_cfg_p.sacc_type           
                 : bp_unicore_megaparrot_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_unicore_megaparrot_override_p.num_cce == "inv") 
                 ? bp_unicore_cfg_p.num_cce           
                 : bp_unicore_megaparrot_override_p.num_cce          
              
       ,
   num_lce: (bp_unicore_megaparrot_override_p.num_lce == "inv") 
                 ? bp_unicore_cfg_p.num_lce           
                 : bp_unicore_megaparrot_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_unicore_megaparrot_override_p.vaddr_width == "inv") 
                 ? bp_unicore_cfg_p.vaddr_width           
                 : bp_unicore_megaparrot_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_unicore_megaparrot_override_p.paddr_width == "inv") 
                 ? bp_unicore_cfg_p.paddr_width           
                 : bp_unicore_megaparrot_override_p.paddr_width          
          
       ,
   daddr_width: (bp_unicore_megaparrot_override_p.daddr_width == "inv") 
                 ? bp_unicore_cfg_p.daddr_width           
                 : bp_unicore_megaparrot_override_p.daddr_width          
          
       ,
   caddr_width: (bp_unicore_megaparrot_override_p.caddr_width == "inv") 
                 ? bp_unicore_cfg_p.caddr_width           
                 : bp_unicore_megaparrot_override_p.caddr_width          
          
       ,
   asid_width: (bp_unicore_megaparrot_override_p.asid_width == "inv") 
                 ? bp_unicore_cfg_p.asid_width           
                 : bp_unicore_megaparrot_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_unicore_megaparrot_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_unicore_cfg_p.fe_queue_fifo_els           
                 : bp_unicore_megaparrot_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_unicore_megaparrot_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_unicore_cfg_p.fe_cmd_fifo_els           
                 : bp_unicore_megaparrot_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_unicore_megaparrot_override_p.muldiv_support == "inv") 
                 ? bp_unicore_cfg_p.muldiv_support           
                 : bp_unicore_megaparrot_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_unicore_megaparrot_override_p.fpu_support == "inv") 
                 ? bp_unicore_cfg_p.fpu_support           
                 : bp_unicore_megaparrot_override_p.fpu_support          
          
       ,
   compressed_support: (bp_unicore_megaparrot_override_p.compressed_support == "inv") 
                 ? bp_unicore_cfg_p.compressed_support           
                 : bp_unicore_megaparrot_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_unicore_megaparrot_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_unicore_cfg_p.branch_metadata_fwd_width           
                 : bp_unicore_megaparrot_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_unicore_megaparrot_override_p.btb_tag_width == "inv") 
                 ? bp_unicore_cfg_p.btb_tag_width           
                 : bp_unicore_megaparrot_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_unicore_megaparrot_override_p.btb_idx_width == "inv") 
                 ? bp_unicore_cfg_p.btb_idx_width           
                 : bp_unicore_megaparrot_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_unicore_megaparrot_override_p.bht_idx_width == "inv") 
                 ? bp_unicore_cfg_p.bht_idx_width           
                 : bp_unicore_megaparrot_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_unicore_megaparrot_override_p.bht_row_els == "inv") 
                 ? bp_unicore_cfg_p.bht_row_els           
                 : bp_unicore_megaparrot_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_unicore_megaparrot_override_p.ghist_width == "inv") 
                 ? bp_unicore_cfg_p.ghist_width           
                 : bp_unicore_megaparrot_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_unicore_megaparrot_override_p.itlb_els_4k == "inv") 
                 ? bp_unicore_cfg_p.itlb_els_4k           
                 : bp_unicore_megaparrot_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_unicore_megaparrot_override_p.itlb_els_1g == "inv") 
                 ? bp_unicore_cfg_p.itlb_els_1g           
                 : bp_unicore_megaparrot_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_unicore_megaparrot_override_p.dtlb_els_4k == "inv") 
                 ? bp_unicore_cfg_p.dtlb_els_4k           
                 : bp_unicore_megaparrot_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_unicore_megaparrot_override_p.dtlb_els_1g == "inv") 
                 ? bp_unicore_cfg_p.dtlb_els_1g           
                 : bp_unicore_megaparrot_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_unicore_megaparrot_override_p.icache_features == "inv") 
                 ? bp_unicore_cfg_p.icache_features           
                 : bp_unicore_megaparrot_override_p.icache_features          
      
       ,
   icache_sets: (bp_unicore_megaparrot_override_p.icache_sets == "inv") 
                 ? bp_unicore_cfg_p.icache_sets           
                 : bp_unicore_megaparrot_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_unicore_megaparrot_override_p.icache_assoc == "inv") 
                 ? bp_unicore_cfg_p.icache_assoc           
                 : bp_unicore_megaparrot_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_unicore_megaparrot_override_p.icache_block_width == "inv") 
                 ? bp_unicore_cfg_p.icache_block_width           
                 : bp_unicore_megaparrot_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_unicore_megaparrot_override_p.icache_fill_width == "inv") 
                 ? bp_unicore_cfg_p.icache_fill_width           
                 : bp_unicore_megaparrot_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_unicore_megaparrot_override_p.dcache_features == "inv") 
                 ? bp_unicore_cfg_p.dcache_features           
                 : bp_unicore_megaparrot_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_unicore_megaparrot_override_p.dcache_sets == "inv") 
                 ? bp_unicore_cfg_p.dcache_sets           
                 : bp_unicore_megaparrot_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_unicore_megaparrot_override_p.dcache_assoc == "inv") 
                 ? bp_unicore_cfg_p.dcache_assoc           
                 : bp_unicore_megaparrot_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_unicore_megaparrot_override_p.dcache_block_width == "inv") 
                 ? bp_unicore_cfg_p.dcache_block_width           
                 : bp_unicore_megaparrot_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_unicore_megaparrot_override_p.dcache_fill_width == "inv") 
                 ? bp_unicore_cfg_p.dcache_fill_width           
                 : bp_unicore_megaparrot_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_unicore_megaparrot_override_p.acache_features == "inv") 
                 ? bp_unicore_cfg_p.acache_features           
                 : bp_unicore_megaparrot_override_p.acache_features          
      
       ,
   acache_sets: (bp_unicore_megaparrot_override_p.acache_sets == "inv") 
                 ? bp_unicore_cfg_p.acache_sets           
                 : bp_unicore_megaparrot_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_unicore_megaparrot_override_p.acache_assoc == "inv") 
                 ? bp_unicore_cfg_p.acache_assoc           
                 : bp_unicore_megaparrot_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_unicore_megaparrot_override_p.acache_block_width == "inv") 
                 ? bp_unicore_cfg_p.acache_block_width           
                 : bp_unicore_megaparrot_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_unicore_megaparrot_override_p.acache_fill_width == "inv") 
                 ? bp_unicore_cfg_p.acache_fill_width           
                 : bp_unicore_megaparrot_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_unicore_megaparrot_override_p.cce_type == "inv") 
                 ? bp_unicore_cfg_p.cce_type           
                 : bp_unicore_megaparrot_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_unicore_megaparrot_override_p.cce_pc_width == "inv") 
                 ? bp_unicore_cfg_p.cce_pc_width           
                 : bp_unicore_megaparrot_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_unicore_megaparrot_override_p.bedrock_data_width == "inv") 
                 ? bp_unicore_cfg_p.bedrock_data_width           
                 : bp_unicore_megaparrot_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_unicore_megaparrot_override_p.l2_features == "inv") 
                 ? bp_unicore_cfg_p.l2_features           
                 : bp_unicore_megaparrot_override_p.l2_features          
          
       ,
   l2_banks: (bp_unicore_megaparrot_override_p.l2_banks == "inv") 
                 ? bp_unicore_cfg_p.l2_banks           
                 : bp_unicore_megaparrot_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_unicore_megaparrot_override_p.l2_data_width == "inv") 
                 ? bp_unicore_cfg_p.l2_data_width           
                 : bp_unicore_megaparrot_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_unicore_megaparrot_override_p.l2_sets == "inv") 
                 ? bp_unicore_cfg_p.l2_sets           
                 : bp_unicore_megaparrot_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_unicore_megaparrot_override_p.l2_assoc == "inv") 
                 ? bp_unicore_cfg_p.l2_assoc           
                 : bp_unicore_megaparrot_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_unicore_megaparrot_override_p.l2_block_width == "inv") 
                 ? bp_unicore_cfg_p.l2_block_width           
                 : bp_unicore_megaparrot_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_unicore_megaparrot_override_p.l2_fill_width == "inv") 
                 ? bp_unicore_cfg_p.l2_fill_width           
                 : bp_unicore_megaparrot_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_unicore_megaparrot_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_unicore_cfg_p.l2_outstanding_reqs           
                 : bp_unicore_megaparrot_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_unicore_megaparrot_override_p.async_coh_clk == "inv") 
                 ? bp_unicore_cfg_p.async_coh_clk           
                 : bp_unicore_megaparrot_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_unicore_megaparrot_override_p.coh_noc_max_credits == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_max_credits           
                 : bp_unicore_megaparrot_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_unicore_megaparrot_override_p.coh_noc_flit_width == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_flit_width           
                 : bp_unicore_megaparrot_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_unicore_megaparrot_override_p.coh_noc_cid_width == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_cid_width           
                 : bp_unicore_megaparrot_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_unicore_megaparrot_override_p.coh_noc_len_width == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_len_width           
                 : bp_unicore_megaparrot_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_unicore_megaparrot_override_p.async_mem_clk == "inv") 
                 ? bp_unicore_cfg_p.async_mem_clk           
                 : bp_unicore_megaparrot_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_unicore_megaparrot_override_p.mem_noc_max_credits == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_max_credits           
                 : bp_unicore_megaparrot_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_unicore_megaparrot_override_p.mem_noc_flit_width == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_flit_width           
                 : bp_unicore_megaparrot_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_unicore_megaparrot_override_p.mem_noc_cid_width == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_cid_width           
                 : bp_unicore_megaparrot_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_unicore_megaparrot_override_p.mem_noc_len_width == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_len_width           
                 : bp_unicore_megaparrot_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_unicore_megaparrot_override_p.async_io_clk == "inv") 
                 ? bp_unicore_cfg_p.async_io_clk           
                 : bp_unicore_megaparrot_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_unicore_megaparrot_override_p.io_noc_max_credits == "inv") 
                 ? bp_unicore_cfg_p.io_noc_max_credits           
                 : bp_unicore_megaparrot_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_unicore_megaparrot_override_p.io_noc_flit_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_flit_width           
                 : bp_unicore_megaparrot_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_unicore_megaparrot_override_p.io_noc_cid_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_cid_width           
                 : bp_unicore_megaparrot_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_unicore_megaparrot_override_p.io_noc_did_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_did_width           
                 : bp_unicore_megaparrot_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_unicore_megaparrot_override_p.io_noc_len_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_len_width           
                 : bp_unicore_megaparrot_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_unicore_tinyparrot_override_p =
 '{paddr_width         : 34

   ,branch_metadata_fwd_width: 28
   ,btb_tag_width            : 6
   ,btb_idx_width            : 4
   ,bht_idx_width            : 5
   ,bht_row_els              : 2
   ,ghist_width              : 2

   ,icache_sets        : 128
   ,icache_assoc       : 1
   ,icache_block_width : 64
   ,icache_fill_width  : 64

   ,dcache_features    : (1 << e_cfg_enabled) | (1 << e_cfg_lr_sc)
   ,dcache_sets        : 128
   ,dcache_assoc       : 1
   ,dcache_block_width : 64
   ,dcache_fill_width  : 64

   // We use L2 for the write buffer support, but not AMO
   ,l2_features : (1 << e_cfg_writeback) | (1 << e_cfg_word_tracking)

   ,default : "inv"
   };

   localparam bp_proc_param_s bp_unicore_tinyparrot_cfg_p =                                                     
     '{
   cc_x_dim: (bp_unicore_tinyparrot_override_p.cc_x_dim == "inv") 
                 ? bp_unicore_cfg_p.cc_x_dim           
                 : bp_unicore_tinyparrot_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_unicore_tinyparrot_override_p.cc_y_dim == "inv") 
                 ? bp_unicore_cfg_p.cc_y_dim           
                 : bp_unicore_tinyparrot_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_unicore_tinyparrot_override_p.ic_y_dim == "inv") 
                 ? bp_unicore_cfg_p.ic_y_dim           
                 : bp_unicore_tinyparrot_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_unicore_tinyparrot_override_p.mc_y_dim == "inv") 
                 ? bp_unicore_cfg_p.mc_y_dim           
                 : bp_unicore_tinyparrot_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_unicore_tinyparrot_override_p.cac_x_dim == "inv") 
                 ? bp_unicore_cfg_p.cac_x_dim           
                 : bp_unicore_tinyparrot_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_unicore_tinyparrot_override_p.sac_x_dim == "inv") 
                 ? bp_unicore_cfg_p.sac_x_dim           
                 : bp_unicore_tinyparrot_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_unicore_tinyparrot_override_p.cacc_type == "inv") 
                 ? bp_unicore_cfg_p.cacc_type           
                 : bp_unicore_tinyparrot_override_p.cacc_type          
            
       ,
   sacc_type: (bp_unicore_tinyparrot_override_p.sacc_type == "inv") 
                 ? bp_unicore_cfg_p.sacc_type           
                 : bp_unicore_tinyparrot_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_unicore_tinyparrot_override_p.num_cce == "inv") 
                 ? bp_unicore_cfg_p.num_cce           
                 : bp_unicore_tinyparrot_override_p.num_cce          
              
       ,
   num_lce: (bp_unicore_tinyparrot_override_p.num_lce == "inv") 
                 ? bp_unicore_cfg_p.num_lce           
                 : bp_unicore_tinyparrot_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_unicore_tinyparrot_override_p.vaddr_width == "inv") 
                 ? bp_unicore_cfg_p.vaddr_width           
                 : bp_unicore_tinyparrot_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_unicore_tinyparrot_override_p.paddr_width == "inv") 
                 ? bp_unicore_cfg_p.paddr_width           
                 : bp_unicore_tinyparrot_override_p.paddr_width          
          
       ,
   daddr_width: (bp_unicore_tinyparrot_override_p.daddr_width == "inv") 
                 ? bp_unicore_cfg_p.daddr_width           
                 : bp_unicore_tinyparrot_override_p.daddr_width          
          
       ,
   caddr_width: (bp_unicore_tinyparrot_override_p.caddr_width == "inv") 
                 ? bp_unicore_cfg_p.caddr_width           
                 : bp_unicore_tinyparrot_override_p.caddr_width          
          
       ,
   asid_width: (bp_unicore_tinyparrot_override_p.asid_width == "inv") 
                 ? bp_unicore_cfg_p.asid_width           
                 : bp_unicore_tinyparrot_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_unicore_tinyparrot_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_unicore_cfg_p.fe_queue_fifo_els           
                 : bp_unicore_tinyparrot_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_unicore_tinyparrot_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_unicore_cfg_p.fe_cmd_fifo_els           
                 : bp_unicore_tinyparrot_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_unicore_tinyparrot_override_p.muldiv_support == "inv") 
                 ? bp_unicore_cfg_p.muldiv_support           
                 : bp_unicore_tinyparrot_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_unicore_tinyparrot_override_p.fpu_support == "inv") 
                 ? bp_unicore_cfg_p.fpu_support           
                 : bp_unicore_tinyparrot_override_p.fpu_support          
          
       ,
   compressed_support: (bp_unicore_tinyparrot_override_p.compressed_support == "inv") 
                 ? bp_unicore_cfg_p.compressed_support           
                 : bp_unicore_tinyparrot_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_unicore_tinyparrot_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_unicore_cfg_p.branch_metadata_fwd_width           
                 : bp_unicore_tinyparrot_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_unicore_tinyparrot_override_p.btb_tag_width == "inv") 
                 ? bp_unicore_cfg_p.btb_tag_width           
                 : bp_unicore_tinyparrot_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_unicore_tinyparrot_override_p.btb_idx_width == "inv") 
                 ? bp_unicore_cfg_p.btb_idx_width           
                 : bp_unicore_tinyparrot_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_unicore_tinyparrot_override_p.bht_idx_width == "inv") 
                 ? bp_unicore_cfg_p.bht_idx_width           
                 : bp_unicore_tinyparrot_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_unicore_tinyparrot_override_p.bht_row_els == "inv") 
                 ? bp_unicore_cfg_p.bht_row_els           
                 : bp_unicore_tinyparrot_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_unicore_tinyparrot_override_p.ghist_width == "inv") 
                 ? bp_unicore_cfg_p.ghist_width           
                 : bp_unicore_tinyparrot_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_unicore_tinyparrot_override_p.itlb_els_4k == "inv") 
                 ? bp_unicore_cfg_p.itlb_els_4k           
                 : bp_unicore_tinyparrot_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_unicore_tinyparrot_override_p.itlb_els_1g == "inv") 
                 ? bp_unicore_cfg_p.itlb_els_1g           
                 : bp_unicore_tinyparrot_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_unicore_tinyparrot_override_p.dtlb_els_4k == "inv") 
                 ? bp_unicore_cfg_p.dtlb_els_4k           
                 : bp_unicore_tinyparrot_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_unicore_tinyparrot_override_p.dtlb_els_1g == "inv") 
                 ? bp_unicore_cfg_p.dtlb_els_1g           
                 : bp_unicore_tinyparrot_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_unicore_tinyparrot_override_p.icache_features == "inv") 
                 ? bp_unicore_cfg_p.icache_features           
                 : bp_unicore_tinyparrot_override_p.icache_features          
      
       ,
   icache_sets: (bp_unicore_tinyparrot_override_p.icache_sets == "inv") 
                 ? bp_unicore_cfg_p.icache_sets           
                 : bp_unicore_tinyparrot_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_unicore_tinyparrot_override_p.icache_assoc == "inv") 
                 ? bp_unicore_cfg_p.icache_assoc           
                 : bp_unicore_tinyparrot_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_unicore_tinyparrot_override_p.icache_block_width == "inv") 
                 ? bp_unicore_cfg_p.icache_block_width           
                 : bp_unicore_tinyparrot_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_unicore_tinyparrot_override_p.icache_fill_width == "inv") 
                 ? bp_unicore_cfg_p.icache_fill_width           
                 : bp_unicore_tinyparrot_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_unicore_tinyparrot_override_p.dcache_features == "inv") 
                 ? bp_unicore_cfg_p.dcache_features           
                 : bp_unicore_tinyparrot_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_unicore_tinyparrot_override_p.dcache_sets == "inv") 
                 ? bp_unicore_cfg_p.dcache_sets           
                 : bp_unicore_tinyparrot_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_unicore_tinyparrot_override_p.dcache_assoc == "inv") 
                 ? bp_unicore_cfg_p.dcache_assoc           
                 : bp_unicore_tinyparrot_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_unicore_tinyparrot_override_p.dcache_block_width == "inv") 
                 ? bp_unicore_cfg_p.dcache_block_width           
                 : bp_unicore_tinyparrot_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_unicore_tinyparrot_override_p.dcache_fill_width == "inv") 
                 ? bp_unicore_cfg_p.dcache_fill_width           
                 : bp_unicore_tinyparrot_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_unicore_tinyparrot_override_p.acache_features == "inv") 
                 ? bp_unicore_cfg_p.acache_features           
                 : bp_unicore_tinyparrot_override_p.acache_features          
      
       ,
   acache_sets: (bp_unicore_tinyparrot_override_p.acache_sets == "inv") 
                 ? bp_unicore_cfg_p.acache_sets           
                 : bp_unicore_tinyparrot_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_unicore_tinyparrot_override_p.acache_assoc == "inv") 
                 ? bp_unicore_cfg_p.acache_assoc           
                 : bp_unicore_tinyparrot_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_unicore_tinyparrot_override_p.acache_block_width == "inv") 
                 ? bp_unicore_cfg_p.acache_block_width           
                 : bp_unicore_tinyparrot_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_unicore_tinyparrot_override_p.acache_fill_width == "inv") 
                 ? bp_unicore_cfg_p.acache_fill_width           
                 : bp_unicore_tinyparrot_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_unicore_tinyparrot_override_p.cce_type == "inv") 
                 ? bp_unicore_cfg_p.cce_type           
                 : bp_unicore_tinyparrot_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_unicore_tinyparrot_override_p.cce_pc_width == "inv") 
                 ? bp_unicore_cfg_p.cce_pc_width           
                 : bp_unicore_tinyparrot_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_unicore_tinyparrot_override_p.bedrock_data_width == "inv") 
                 ? bp_unicore_cfg_p.bedrock_data_width           
                 : bp_unicore_tinyparrot_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_unicore_tinyparrot_override_p.l2_features == "inv") 
                 ? bp_unicore_cfg_p.l2_features           
                 : bp_unicore_tinyparrot_override_p.l2_features          
          
       ,
   l2_banks: (bp_unicore_tinyparrot_override_p.l2_banks == "inv") 
                 ? bp_unicore_cfg_p.l2_banks           
                 : bp_unicore_tinyparrot_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_unicore_tinyparrot_override_p.l2_data_width == "inv") 
                 ? bp_unicore_cfg_p.l2_data_width           
                 : bp_unicore_tinyparrot_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_unicore_tinyparrot_override_p.l2_sets == "inv") 
                 ? bp_unicore_cfg_p.l2_sets           
                 : bp_unicore_tinyparrot_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_unicore_tinyparrot_override_p.l2_assoc == "inv") 
                 ? bp_unicore_cfg_p.l2_assoc           
                 : bp_unicore_tinyparrot_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_unicore_tinyparrot_override_p.l2_block_width == "inv") 
                 ? bp_unicore_cfg_p.l2_block_width           
                 : bp_unicore_tinyparrot_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_unicore_tinyparrot_override_p.l2_fill_width == "inv") 
                 ? bp_unicore_cfg_p.l2_fill_width           
                 : bp_unicore_tinyparrot_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_unicore_tinyparrot_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_unicore_cfg_p.l2_outstanding_reqs           
                 : bp_unicore_tinyparrot_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_unicore_tinyparrot_override_p.async_coh_clk == "inv") 
                 ? bp_unicore_cfg_p.async_coh_clk           
                 : bp_unicore_tinyparrot_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_unicore_tinyparrot_override_p.coh_noc_max_credits == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_max_credits           
                 : bp_unicore_tinyparrot_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_unicore_tinyparrot_override_p.coh_noc_flit_width == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_flit_width           
                 : bp_unicore_tinyparrot_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_unicore_tinyparrot_override_p.coh_noc_cid_width == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_cid_width           
                 : bp_unicore_tinyparrot_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_unicore_tinyparrot_override_p.coh_noc_len_width == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_len_width           
                 : bp_unicore_tinyparrot_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_unicore_tinyparrot_override_p.async_mem_clk == "inv") 
                 ? bp_unicore_cfg_p.async_mem_clk           
                 : bp_unicore_tinyparrot_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_unicore_tinyparrot_override_p.mem_noc_max_credits == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_max_credits           
                 : bp_unicore_tinyparrot_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_unicore_tinyparrot_override_p.mem_noc_flit_width == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_flit_width           
                 : bp_unicore_tinyparrot_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_unicore_tinyparrot_override_p.mem_noc_cid_width == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_cid_width           
                 : bp_unicore_tinyparrot_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_unicore_tinyparrot_override_p.mem_noc_len_width == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_len_width           
                 : bp_unicore_tinyparrot_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_unicore_tinyparrot_override_p.async_io_clk == "inv") 
                 ? bp_unicore_cfg_p.async_io_clk           
                 : bp_unicore_tinyparrot_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_unicore_tinyparrot_override_p.io_noc_max_credits == "inv") 
                 ? bp_unicore_cfg_p.io_noc_max_credits           
                 : bp_unicore_tinyparrot_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_unicore_tinyparrot_override_p.io_noc_flit_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_flit_width           
                 : bp_unicore_tinyparrot_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_unicore_tinyparrot_override_p.io_noc_cid_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_cid_width           
                 : bp_unicore_tinyparrot_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_unicore_tinyparrot_override_p.io_noc_did_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_did_width           
                 : bp_unicore_tinyparrot_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_unicore_tinyparrot_override_p.io_noc_len_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_len_width           
                 : bp_unicore_tinyparrot_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_unicore_miniparrot_override_p =
 '{paddr_width         : 34

   ,branch_metadata_fwd_width: 28
   ,btb_tag_width            : 6
   ,btb_idx_width            : 4
   ,bht_idx_width            : 5
   ,bht_row_els              : 2
   ,ghist_width              : 2

   ,icache_sets        : 512
   ,icache_assoc       : 1
   ,icache_block_width : 64
   ,icache_fill_width  : 64

   ,dcache_features    : (1 << e_cfg_enabled) | (1 << e_cfg_lr_sc)
   ,dcache_sets        : 512
   ,dcache_assoc       : 1
   ,dcache_block_width : 64
   ,dcache_fill_width  : 64

   // We use L2 for the write buffer support
   ,l2_features : (1 << e_cfg_enabled)
                  | (1 << e_cfg_writeback)
                  | (1 << e_cfg_word_tracking)
                  | (1 << e_cfg_amo_swap)
                  | (1 << e_cfg_amo_fetch_logic)
                  | (1 << e_cfg_amo_fetch_arithmetic)

   ,default : "inv"
   };

   localparam bp_proc_param_s bp_unicore_miniparrot_cfg_p =                                                     
     '{
   cc_x_dim: (bp_unicore_miniparrot_override_p.cc_x_dim == "inv") 
                 ? bp_unicore_cfg_p.cc_x_dim           
                 : bp_unicore_miniparrot_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_unicore_miniparrot_override_p.cc_y_dim == "inv") 
                 ? bp_unicore_cfg_p.cc_y_dim           
                 : bp_unicore_miniparrot_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_unicore_miniparrot_override_p.ic_y_dim == "inv") 
                 ? bp_unicore_cfg_p.ic_y_dim           
                 : bp_unicore_miniparrot_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_unicore_miniparrot_override_p.mc_y_dim == "inv") 
                 ? bp_unicore_cfg_p.mc_y_dim           
                 : bp_unicore_miniparrot_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_unicore_miniparrot_override_p.cac_x_dim == "inv") 
                 ? bp_unicore_cfg_p.cac_x_dim           
                 : bp_unicore_miniparrot_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_unicore_miniparrot_override_p.sac_x_dim == "inv") 
                 ? bp_unicore_cfg_p.sac_x_dim           
                 : bp_unicore_miniparrot_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_unicore_miniparrot_override_p.cacc_type == "inv") 
                 ? bp_unicore_cfg_p.cacc_type           
                 : bp_unicore_miniparrot_override_p.cacc_type          
            
       ,
   sacc_type: (bp_unicore_miniparrot_override_p.sacc_type == "inv") 
                 ? bp_unicore_cfg_p.sacc_type           
                 : bp_unicore_miniparrot_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_unicore_miniparrot_override_p.num_cce == "inv") 
                 ? bp_unicore_cfg_p.num_cce           
                 : bp_unicore_miniparrot_override_p.num_cce          
              
       ,
   num_lce: (bp_unicore_miniparrot_override_p.num_lce == "inv") 
                 ? bp_unicore_cfg_p.num_lce           
                 : bp_unicore_miniparrot_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_unicore_miniparrot_override_p.vaddr_width == "inv") 
                 ? bp_unicore_cfg_p.vaddr_width           
                 : bp_unicore_miniparrot_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_unicore_miniparrot_override_p.paddr_width == "inv") 
                 ? bp_unicore_cfg_p.paddr_width           
                 : bp_unicore_miniparrot_override_p.paddr_width          
          
       ,
   daddr_width: (bp_unicore_miniparrot_override_p.daddr_width == "inv") 
                 ? bp_unicore_cfg_p.daddr_width           
                 : bp_unicore_miniparrot_override_p.daddr_width          
          
       ,
   caddr_width: (bp_unicore_miniparrot_override_p.caddr_width == "inv") 
                 ? bp_unicore_cfg_p.caddr_width           
                 : bp_unicore_miniparrot_override_p.caddr_width          
          
       ,
   asid_width: (bp_unicore_miniparrot_override_p.asid_width == "inv") 
                 ? bp_unicore_cfg_p.asid_width           
                 : bp_unicore_miniparrot_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_unicore_miniparrot_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_unicore_cfg_p.fe_queue_fifo_els           
                 : bp_unicore_miniparrot_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_unicore_miniparrot_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_unicore_cfg_p.fe_cmd_fifo_els           
                 : bp_unicore_miniparrot_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_unicore_miniparrot_override_p.muldiv_support == "inv") 
                 ? bp_unicore_cfg_p.muldiv_support           
                 : bp_unicore_miniparrot_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_unicore_miniparrot_override_p.fpu_support == "inv") 
                 ? bp_unicore_cfg_p.fpu_support           
                 : bp_unicore_miniparrot_override_p.fpu_support          
          
       ,
   compressed_support: (bp_unicore_miniparrot_override_p.compressed_support == "inv") 
                 ? bp_unicore_cfg_p.compressed_support           
                 : bp_unicore_miniparrot_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_unicore_miniparrot_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_unicore_cfg_p.branch_metadata_fwd_width           
                 : bp_unicore_miniparrot_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_unicore_miniparrot_override_p.btb_tag_width == "inv") 
                 ? bp_unicore_cfg_p.btb_tag_width           
                 : bp_unicore_miniparrot_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_unicore_miniparrot_override_p.btb_idx_width == "inv") 
                 ? bp_unicore_cfg_p.btb_idx_width           
                 : bp_unicore_miniparrot_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_unicore_miniparrot_override_p.bht_idx_width == "inv") 
                 ? bp_unicore_cfg_p.bht_idx_width           
                 : bp_unicore_miniparrot_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_unicore_miniparrot_override_p.bht_row_els == "inv") 
                 ? bp_unicore_cfg_p.bht_row_els           
                 : bp_unicore_miniparrot_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_unicore_miniparrot_override_p.ghist_width == "inv") 
                 ? bp_unicore_cfg_p.ghist_width           
                 : bp_unicore_miniparrot_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_unicore_miniparrot_override_p.itlb_els_4k == "inv") 
                 ? bp_unicore_cfg_p.itlb_els_4k           
                 : bp_unicore_miniparrot_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_unicore_miniparrot_override_p.itlb_els_1g == "inv") 
                 ? bp_unicore_cfg_p.itlb_els_1g           
                 : bp_unicore_miniparrot_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_unicore_miniparrot_override_p.dtlb_els_4k == "inv") 
                 ? bp_unicore_cfg_p.dtlb_els_4k           
                 : bp_unicore_miniparrot_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_unicore_miniparrot_override_p.dtlb_els_1g == "inv") 
                 ? bp_unicore_cfg_p.dtlb_els_1g           
                 : bp_unicore_miniparrot_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_unicore_miniparrot_override_p.icache_features == "inv") 
                 ? bp_unicore_cfg_p.icache_features           
                 : bp_unicore_miniparrot_override_p.icache_features          
      
       ,
   icache_sets: (bp_unicore_miniparrot_override_p.icache_sets == "inv") 
                 ? bp_unicore_cfg_p.icache_sets           
                 : bp_unicore_miniparrot_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_unicore_miniparrot_override_p.icache_assoc == "inv") 
                 ? bp_unicore_cfg_p.icache_assoc           
                 : bp_unicore_miniparrot_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_unicore_miniparrot_override_p.icache_block_width == "inv") 
                 ? bp_unicore_cfg_p.icache_block_width           
                 : bp_unicore_miniparrot_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_unicore_miniparrot_override_p.icache_fill_width == "inv") 
                 ? bp_unicore_cfg_p.icache_fill_width           
                 : bp_unicore_miniparrot_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_unicore_miniparrot_override_p.dcache_features == "inv") 
                 ? bp_unicore_cfg_p.dcache_features           
                 : bp_unicore_miniparrot_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_unicore_miniparrot_override_p.dcache_sets == "inv") 
                 ? bp_unicore_cfg_p.dcache_sets           
                 : bp_unicore_miniparrot_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_unicore_miniparrot_override_p.dcache_assoc == "inv") 
                 ? bp_unicore_cfg_p.dcache_assoc           
                 : bp_unicore_miniparrot_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_unicore_miniparrot_override_p.dcache_block_width == "inv") 
                 ? bp_unicore_cfg_p.dcache_block_width           
                 : bp_unicore_miniparrot_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_unicore_miniparrot_override_p.dcache_fill_width == "inv") 
                 ? bp_unicore_cfg_p.dcache_fill_width           
                 : bp_unicore_miniparrot_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_unicore_miniparrot_override_p.acache_features == "inv") 
                 ? bp_unicore_cfg_p.acache_features           
                 : bp_unicore_miniparrot_override_p.acache_features          
      
       ,
   acache_sets: (bp_unicore_miniparrot_override_p.acache_sets == "inv") 
                 ? bp_unicore_cfg_p.acache_sets           
                 : bp_unicore_miniparrot_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_unicore_miniparrot_override_p.acache_assoc == "inv") 
                 ? bp_unicore_cfg_p.acache_assoc           
                 : bp_unicore_miniparrot_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_unicore_miniparrot_override_p.acache_block_width == "inv") 
                 ? bp_unicore_cfg_p.acache_block_width           
                 : bp_unicore_miniparrot_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_unicore_miniparrot_override_p.acache_fill_width == "inv") 
                 ? bp_unicore_cfg_p.acache_fill_width           
                 : bp_unicore_miniparrot_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_unicore_miniparrot_override_p.cce_type == "inv") 
                 ? bp_unicore_cfg_p.cce_type           
                 : bp_unicore_miniparrot_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_unicore_miniparrot_override_p.cce_pc_width == "inv") 
                 ? bp_unicore_cfg_p.cce_pc_width           
                 : bp_unicore_miniparrot_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_unicore_miniparrot_override_p.bedrock_data_width == "inv") 
                 ? bp_unicore_cfg_p.bedrock_data_width           
                 : bp_unicore_miniparrot_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_unicore_miniparrot_override_p.l2_features == "inv") 
                 ? bp_unicore_cfg_p.l2_features           
                 : bp_unicore_miniparrot_override_p.l2_features          
          
       ,
   l2_banks: (bp_unicore_miniparrot_override_p.l2_banks == "inv") 
                 ? bp_unicore_cfg_p.l2_banks           
                 : bp_unicore_miniparrot_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_unicore_miniparrot_override_p.l2_data_width == "inv") 
                 ? bp_unicore_cfg_p.l2_data_width           
                 : bp_unicore_miniparrot_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_unicore_miniparrot_override_p.l2_sets == "inv") 
                 ? bp_unicore_cfg_p.l2_sets           
                 : bp_unicore_miniparrot_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_unicore_miniparrot_override_p.l2_assoc == "inv") 
                 ? bp_unicore_cfg_p.l2_assoc           
                 : bp_unicore_miniparrot_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_unicore_miniparrot_override_p.l2_block_width == "inv") 
                 ? bp_unicore_cfg_p.l2_block_width           
                 : bp_unicore_miniparrot_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_unicore_miniparrot_override_p.l2_fill_width == "inv") 
                 ? bp_unicore_cfg_p.l2_fill_width           
                 : bp_unicore_miniparrot_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_unicore_miniparrot_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_unicore_cfg_p.l2_outstanding_reqs           
                 : bp_unicore_miniparrot_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_unicore_miniparrot_override_p.async_coh_clk == "inv") 
                 ? bp_unicore_cfg_p.async_coh_clk           
                 : bp_unicore_miniparrot_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_unicore_miniparrot_override_p.coh_noc_max_credits == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_max_credits           
                 : bp_unicore_miniparrot_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_unicore_miniparrot_override_p.coh_noc_flit_width == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_flit_width           
                 : bp_unicore_miniparrot_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_unicore_miniparrot_override_p.coh_noc_cid_width == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_cid_width           
                 : bp_unicore_miniparrot_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_unicore_miniparrot_override_p.coh_noc_len_width == "inv") 
                 ? bp_unicore_cfg_p.coh_noc_len_width           
                 : bp_unicore_miniparrot_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_unicore_miniparrot_override_p.async_mem_clk == "inv") 
                 ? bp_unicore_cfg_p.async_mem_clk           
                 : bp_unicore_miniparrot_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_unicore_miniparrot_override_p.mem_noc_max_credits == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_max_credits           
                 : bp_unicore_miniparrot_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_unicore_miniparrot_override_p.mem_noc_flit_width == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_flit_width           
                 : bp_unicore_miniparrot_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_unicore_miniparrot_override_p.mem_noc_cid_width == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_cid_width           
                 : bp_unicore_miniparrot_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_unicore_miniparrot_override_p.mem_noc_len_width == "inv") 
                 ? bp_unicore_cfg_p.mem_noc_len_width           
                 : bp_unicore_miniparrot_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_unicore_miniparrot_override_p.async_io_clk == "inv") 
                 ? bp_unicore_cfg_p.async_io_clk           
                 : bp_unicore_miniparrot_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_unicore_miniparrot_override_p.io_noc_max_credits == "inv") 
                 ? bp_unicore_cfg_p.io_noc_max_credits           
                 : bp_unicore_miniparrot_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_unicore_miniparrot_override_p.io_noc_flit_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_flit_width           
                 : bp_unicore_miniparrot_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_unicore_miniparrot_override_p.io_noc_cid_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_cid_width           
                 : bp_unicore_miniparrot_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_unicore_miniparrot_override_p.io_noc_did_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_did_width           
                 : bp_unicore_miniparrot_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_unicore_miniparrot_override_p.io_noc_len_width == "inv") 
                 ? bp_unicore_cfg_p.io_noc_len_width           
                 : bp_unicore_miniparrot_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_1_override_p =
 '{cce_type              : e_cce_fsm
   ,ic_y_dim             : 1
   ,icache_features      : (1 << e_cfg_enabled) | (1 << e_cfg_coherent)
   ,dcache_features      : (1 << e_cfg_enabled)
                           | (1 << e_cfg_coherent)
                           | (1 << e_cfg_writeback)
                           | (1 << e_cfg_lr_sc)
                           | (1 << e_cfg_amo_swap)
                           | (1 << e_cfg_amo_fetch_logic)
                           | (1 << e_cfg_amo_fetch_arithmetic)
   ,l2_features          : (1 << e_cfg_enabled) | (1 << e_cfg_writeback)
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_1_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_1_override_p.cc_x_dim == "inv") 
                 ? bp_default_cfg_p.cc_x_dim           
                 : bp_multicore_1_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_1_override_p.cc_y_dim == "inv") 
                 ? bp_default_cfg_p.cc_y_dim           
                 : bp_multicore_1_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_1_override_p.ic_y_dim == "inv") 
                 ? bp_default_cfg_p.ic_y_dim           
                 : bp_multicore_1_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_1_override_p.mc_y_dim == "inv") 
                 ? bp_default_cfg_p.mc_y_dim           
                 : bp_multicore_1_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_1_override_p.cac_x_dim == "inv") 
                 ? bp_default_cfg_p.cac_x_dim           
                 : bp_multicore_1_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_1_override_p.sac_x_dim == "inv") 
                 ? bp_default_cfg_p.sac_x_dim           
                 : bp_multicore_1_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_1_override_p.cacc_type == "inv") 
                 ? bp_default_cfg_p.cacc_type           
                 : bp_multicore_1_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_1_override_p.sacc_type == "inv") 
                 ? bp_default_cfg_p.sacc_type           
                 : bp_multicore_1_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_1_override_p.num_cce == "inv") 
                 ? bp_default_cfg_p.num_cce           
                 : bp_multicore_1_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_1_override_p.num_lce == "inv") 
                 ? bp_default_cfg_p.num_lce           
                 : bp_multicore_1_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_1_override_p.vaddr_width == "inv") 
                 ? bp_default_cfg_p.vaddr_width           
                 : bp_multicore_1_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_1_override_p.paddr_width == "inv") 
                 ? bp_default_cfg_p.paddr_width           
                 : bp_multicore_1_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_1_override_p.daddr_width == "inv") 
                 ? bp_default_cfg_p.daddr_width           
                 : bp_multicore_1_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_1_override_p.caddr_width == "inv") 
                 ? bp_default_cfg_p.caddr_width           
                 : bp_multicore_1_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_1_override_p.asid_width == "inv") 
                 ? bp_default_cfg_p.asid_width           
                 : bp_multicore_1_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_1_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_default_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_1_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_1_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_default_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_1_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_1_override_p.muldiv_support == "inv") 
                 ? bp_default_cfg_p.muldiv_support           
                 : bp_multicore_1_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_1_override_p.fpu_support == "inv") 
                 ? bp_default_cfg_p.fpu_support           
                 : bp_multicore_1_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_1_override_p.compressed_support == "inv") 
                 ? bp_default_cfg_p.compressed_support           
                 : bp_multicore_1_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_1_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_default_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_1_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_1_override_p.btb_tag_width == "inv") 
                 ? bp_default_cfg_p.btb_tag_width           
                 : bp_multicore_1_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_1_override_p.btb_idx_width == "inv") 
                 ? bp_default_cfg_p.btb_idx_width           
                 : bp_multicore_1_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_1_override_p.bht_idx_width == "inv") 
                 ? bp_default_cfg_p.bht_idx_width           
                 : bp_multicore_1_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_1_override_p.bht_row_els == "inv") 
                 ? bp_default_cfg_p.bht_row_els           
                 : bp_multicore_1_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_1_override_p.ghist_width == "inv") 
                 ? bp_default_cfg_p.ghist_width           
                 : bp_multicore_1_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_1_override_p.itlb_els_4k == "inv") 
                 ? bp_default_cfg_p.itlb_els_4k           
                 : bp_multicore_1_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_1_override_p.itlb_els_1g == "inv") 
                 ? bp_default_cfg_p.itlb_els_1g           
                 : bp_multicore_1_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_1_override_p.dtlb_els_4k == "inv") 
                 ? bp_default_cfg_p.dtlb_els_4k           
                 : bp_multicore_1_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_1_override_p.dtlb_els_1g == "inv") 
                 ? bp_default_cfg_p.dtlb_els_1g           
                 : bp_multicore_1_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_1_override_p.icache_features == "inv") 
                 ? bp_default_cfg_p.icache_features           
                 : bp_multicore_1_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_1_override_p.icache_sets == "inv") 
                 ? bp_default_cfg_p.icache_sets           
                 : bp_multicore_1_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_1_override_p.icache_assoc == "inv") 
                 ? bp_default_cfg_p.icache_assoc           
                 : bp_multicore_1_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_1_override_p.icache_block_width == "inv") 
                 ? bp_default_cfg_p.icache_block_width           
                 : bp_multicore_1_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_1_override_p.icache_fill_width == "inv") 
                 ? bp_default_cfg_p.icache_fill_width           
                 : bp_multicore_1_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_1_override_p.dcache_features == "inv") 
                 ? bp_default_cfg_p.dcache_features           
                 : bp_multicore_1_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_1_override_p.dcache_sets == "inv") 
                 ? bp_default_cfg_p.dcache_sets           
                 : bp_multicore_1_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_1_override_p.dcache_assoc == "inv") 
                 ? bp_default_cfg_p.dcache_assoc           
                 : bp_multicore_1_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_1_override_p.dcache_block_width == "inv") 
                 ? bp_default_cfg_p.dcache_block_width           
                 : bp_multicore_1_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_1_override_p.dcache_fill_width == "inv") 
                 ? bp_default_cfg_p.dcache_fill_width           
                 : bp_multicore_1_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_1_override_p.acache_features == "inv") 
                 ? bp_default_cfg_p.acache_features           
                 : bp_multicore_1_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_1_override_p.acache_sets == "inv") 
                 ? bp_default_cfg_p.acache_sets           
                 : bp_multicore_1_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_1_override_p.acache_assoc == "inv") 
                 ? bp_default_cfg_p.acache_assoc           
                 : bp_multicore_1_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_1_override_p.acache_block_width == "inv") 
                 ? bp_default_cfg_p.acache_block_width           
                 : bp_multicore_1_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_1_override_p.acache_fill_width == "inv") 
                 ? bp_default_cfg_p.acache_fill_width           
                 : bp_multicore_1_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_1_override_p.cce_type == "inv") 
                 ? bp_default_cfg_p.cce_type           
                 : bp_multicore_1_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_1_override_p.cce_pc_width == "inv") 
                 ? bp_default_cfg_p.cce_pc_width           
                 : bp_multicore_1_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_1_override_p.bedrock_data_width == "inv") 
                 ? bp_default_cfg_p.bedrock_data_width           
                 : bp_multicore_1_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_1_override_p.l2_features == "inv") 
                 ? bp_default_cfg_p.l2_features           
                 : bp_multicore_1_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_1_override_p.l2_banks == "inv") 
                 ? bp_default_cfg_p.l2_banks           
                 : bp_multicore_1_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_1_override_p.l2_data_width == "inv") 
                 ? bp_default_cfg_p.l2_data_width           
                 : bp_multicore_1_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_1_override_p.l2_sets == "inv") 
                 ? bp_default_cfg_p.l2_sets           
                 : bp_multicore_1_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_1_override_p.l2_assoc == "inv") 
                 ? bp_default_cfg_p.l2_assoc           
                 : bp_multicore_1_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_1_override_p.l2_block_width == "inv") 
                 ? bp_default_cfg_p.l2_block_width           
                 : bp_multicore_1_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_1_override_p.l2_fill_width == "inv") 
                 ? bp_default_cfg_p.l2_fill_width           
                 : bp_multicore_1_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_1_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_default_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_1_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_1_override_p.async_coh_clk == "inv") 
                 ? bp_default_cfg_p.async_coh_clk           
                 : bp_multicore_1_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_1_override_p.coh_noc_max_credits == "inv") 
                 ? bp_default_cfg_p.coh_noc_max_credits           
                 : bp_multicore_1_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_1_override_p.coh_noc_flit_width == "inv") 
                 ? bp_default_cfg_p.coh_noc_flit_width           
                 : bp_multicore_1_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_1_override_p.coh_noc_cid_width == "inv") 
                 ? bp_default_cfg_p.coh_noc_cid_width           
                 : bp_multicore_1_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_1_override_p.coh_noc_len_width == "inv") 
                 ? bp_default_cfg_p.coh_noc_len_width           
                 : bp_multicore_1_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_1_override_p.async_mem_clk == "inv") 
                 ? bp_default_cfg_p.async_mem_clk           
                 : bp_multicore_1_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_1_override_p.mem_noc_max_credits == "inv") 
                 ? bp_default_cfg_p.mem_noc_max_credits           
                 : bp_multicore_1_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_1_override_p.mem_noc_flit_width == "inv") 
                 ? bp_default_cfg_p.mem_noc_flit_width           
                 : bp_multicore_1_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_1_override_p.mem_noc_cid_width == "inv") 
                 ? bp_default_cfg_p.mem_noc_cid_width           
                 : bp_multicore_1_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_1_override_p.mem_noc_len_width == "inv") 
                 ? bp_default_cfg_p.mem_noc_len_width           
                 : bp_multicore_1_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_1_override_p.async_io_clk == "inv") 
                 ? bp_default_cfg_p.async_io_clk           
                 : bp_multicore_1_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_1_override_p.io_noc_max_credits == "inv") 
                 ? bp_default_cfg_p.io_noc_max_credits           
                 : bp_multicore_1_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_1_override_p.io_noc_flit_width == "inv") 
                 ? bp_default_cfg_p.io_noc_flit_width           
                 : bp_multicore_1_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_1_override_p.io_noc_cid_width == "inv") 
                 ? bp_default_cfg_p.io_noc_cid_width           
                 : bp_multicore_1_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_1_override_p.io_noc_did_width == "inv") 
                 ? bp_default_cfg_p.io_noc_did_width           
                 : bp_multicore_1_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_1_override_p.io_noc_len_width == "inv") 
                 ? bp_default_cfg_p.io_noc_len_width           
                 : bp_multicore_1_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_1_megaparrot_override_p =
 '{paddr_width : 56
   ,daddr_width: 55
   ,caddr_width: 54

   ,branch_metadata_fwd_width: 42
   ,btb_tag_width            : 9
   ,btb_idx_width            : 8
   ,bht_idx_width            : 8
   ,bht_row_els              : 4
   ,ghist_width              : 2

   ,icache_sets        : 64
   ,icache_assoc       : 8
   ,icache_block_width : 512
   ,icache_fill_width  : 512

   ,dcache_sets        : 64
   ,dcache_assoc       : 8
   ,dcache_block_width : 512
   ,dcache_fill_width  : 512

   ,acache_sets        : 64
   ,acache_assoc       : 8
   ,acache_block_width : 512
   ,acache_fill_width  : 512

   ,bedrock_data_width : 512

   ,l2_banks            : 8
   ,l2_data_width       : 512
   ,l2_sets             : 128
   ,l2_assoc            : 8
   ,l2_block_width      : 512
   ,l2_fill_width       : 512
   ,l2_outstanding_reqs : 32

   ,mem_noc_flit_width  : 512
   ,mem_noc_cid_width   : 3

   ,coh_noc_flit_width  : 512

   ,io_noc_flit_width   : 512

   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_1_megaparrot_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_1_megaparrot_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_1_megaparrot_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_1_megaparrot_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_1_megaparrot_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_1_megaparrot_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_1_megaparrot_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_1_megaparrot_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_1_megaparrot_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_1_megaparrot_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_1_megaparrot_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_1_megaparrot_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_1_megaparrot_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_1_megaparrot_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_1_megaparrot_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_1_megaparrot_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_1_megaparrot_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_1_megaparrot_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_1_megaparrot_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_1_megaparrot_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_1_megaparrot_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_1_megaparrot_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_1_megaparrot_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_1_megaparrot_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_1_megaparrot_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_1_megaparrot_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_1_megaparrot_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_1_megaparrot_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_1_megaparrot_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_1_megaparrot_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_1_megaparrot_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_1_megaparrot_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_1_megaparrot_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_1_megaparrot_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_1_megaparrot_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_1_megaparrot_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_1_megaparrot_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_1_megaparrot_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_1_megaparrot_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_1_megaparrot_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_1_megaparrot_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_1_megaparrot_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_1_megaparrot_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_1_megaparrot_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_1_megaparrot_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_1_megaparrot_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_1_megaparrot_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_1_megaparrot_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_1_megaparrot_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_1_megaparrot_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_1_megaparrot_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_1_megaparrot_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_1_megaparrot_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_1_megaparrot_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_1_megaparrot_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_1_megaparrot_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_1_megaparrot_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_1_megaparrot_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_1_megaparrot_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_1_megaparrot_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_1_megaparrot_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_1_megaparrot_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_1_megaparrot_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_1_megaparrot_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_1_megaparrot_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_1_megaparrot_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_1_megaparrot_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_1_megaparrot_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_1_megaparrot_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_1_megaparrot_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_1_megaparrot_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_1_megaparrot_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_1_megaparrot_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_1_megaparrot_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_1_megaparrot_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_1_megaparrot_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_1_megaparrot_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_1_megaparrot_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_1_megaparrot_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_1_megaparrot_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_1_megaparrot_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_1_megaparrot_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_1_megaparrot_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_1_megaparrot_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_1_megaparrot_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_1_megaparrot_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_1_megaparrot_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_1_megaparrot_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_1_megaparrot_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_1_megaparrot_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_1_megaparrot_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_1_megaparrot_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_1_megaparrot_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_1_megaparrot_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_1_megaparrot_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_1_megaparrot_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_1_megaparrot_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_1_megaparrot_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_1_megaparrot_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_1_megaparrot_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_1_megaparrot_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_1_megaparrot_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_1_megaparrot_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_1_megaparrot_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_1_megaparrot_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_1_megaparrot_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_1_megaparrot_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_1_megaparrot_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_1_megaparrot_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_1_megaparrot_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_1_megaparrot_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_1_megaparrot_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_1_megaparrot_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_1_megaparrot_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_1_megaparrot_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_1_megaparrot_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_1_megaparrot_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_1_megaparrot_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_1_megaparrot_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_1_megaparrot_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_1_megaparrot_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_1_megaparrot_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_1_megaparrot_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_1_megaparrot_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_1_megaparrot_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_1_megaparrot_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_1_megaparrot_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_1_megaparrot_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_1_megaparrot_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_1_megaparrot_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_1_megaparrot_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_1_megaparrot_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_1_megaparrot_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_1_megaparrot_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_1_megaparrot_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_1_megaparrot_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_1_megaparrot_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_1_megaparrot_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_1_megaparrot_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_1_megaparrot_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_1_megaparrot_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_1_megaparrot_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_1_megaparrot_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_1_megaparrot_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_1_megaparrot_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_1_miniparrot_override_p =
 '{paddr_width : 34
   ,daddr_width: 33
   ,caddr_width: 32

   ,branch_metadata_fwd_width: 28
   ,btb_tag_width            : 6
   ,btb_idx_width            : 4
   ,bht_idx_width            : 5
   ,bht_row_els              : 2
   ,ghist_width              : 2

   ,icache_sets        : 512
   ,icache_assoc       : 1
   ,icache_block_width : 64
   ,icache_fill_width  : 64

   ,dcache_sets        : 512
   ,dcache_assoc       : 1
   ,dcache_block_width : 64
   ,dcache_fill_width  : 64

   ,acache_sets        : 512
   ,acache_assoc       : 1
   ,acache_block_width : 64
   ,acache_fill_width  : 64

   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_1_miniparrot_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_1_miniparrot_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_1_miniparrot_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_1_miniparrot_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_1_miniparrot_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_1_miniparrot_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_1_miniparrot_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_1_miniparrot_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_1_miniparrot_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_1_miniparrot_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_1_miniparrot_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_1_miniparrot_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_1_miniparrot_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_1_miniparrot_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_1_miniparrot_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_1_miniparrot_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_1_miniparrot_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_1_miniparrot_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_1_miniparrot_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_1_miniparrot_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_1_miniparrot_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_1_miniparrot_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_1_miniparrot_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_1_miniparrot_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_1_miniparrot_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_1_miniparrot_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_1_miniparrot_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_1_miniparrot_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_1_miniparrot_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_1_miniparrot_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_1_miniparrot_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_1_miniparrot_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_1_miniparrot_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_1_miniparrot_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_1_miniparrot_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_1_miniparrot_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_1_miniparrot_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_1_miniparrot_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_1_miniparrot_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_1_miniparrot_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_1_miniparrot_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_1_miniparrot_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_1_miniparrot_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_1_miniparrot_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_1_miniparrot_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_1_miniparrot_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_1_miniparrot_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_1_miniparrot_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_1_miniparrot_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_1_miniparrot_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_1_miniparrot_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_1_miniparrot_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_1_miniparrot_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_1_miniparrot_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_1_miniparrot_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_1_miniparrot_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_1_miniparrot_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_1_miniparrot_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_1_miniparrot_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_1_miniparrot_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_1_miniparrot_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_1_miniparrot_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_1_miniparrot_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_1_miniparrot_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_1_miniparrot_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_1_miniparrot_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_1_miniparrot_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_1_miniparrot_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_1_miniparrot_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_1_miniparrot_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_1_miniparrot_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_1_miniparrot_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_1_miniparrot_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_1_miniparrot_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_1_miniparrot_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_1_miniparrot_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_1_miniparrot_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_1_miniparrot_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_1_miniparrot_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_1_miniparrot_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_1_miniparrot_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_1_miniparrot_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_1_miniparrot_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_1_miniparrot_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_1_miniparrot_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_1_miniparrot_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_1_miniparrot_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_1_miniparrot_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_1_miniparrot_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_1_miniparrot_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_1_miniparrot_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_1_miniparrot_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_1_miniparrot_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_1_miniparrot_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_1_miniparrot_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_1_miniparrot_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_1_miniparrot_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_1_miniparrot_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_1_miniparrot_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_1_miniparrot_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_1_miniparrot_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_1_miniparrot_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_1_miniparrot_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_1_miniparrot_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_1_miniparrot_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_1_miniparrot_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_1_miniparrot_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_1_miniparrot_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_1_miniparrot_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_1_miniparrot_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_1_miniparrot_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_1_miniparrot_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_1_miniparrot_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_1_miniparrot_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_1_miniparrot_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_1_miniparrot_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_1_miniparrot_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_1_miniparrot_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_1_miniparrot_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_1_miniparrot_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_1_miniparrot_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_1_miniparrot_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_1_miniparrot_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_1_miniparrot_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_1_miniparrot_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_1_miniparrot_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_1_miniparrot_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_1_miniparrot_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_1_miniparrot_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_1_miniparrot_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_1_miniparrot_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_1_miniparrot_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_1_miniparrot_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_1_miniparrot_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_1_miniparrot_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_1_miniparrot_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_1_miniparrot_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_1_miniparrot_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_1_miniparrot_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_1_miniparrot_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_1_miniparrot_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_1_miniparrot_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_1_miniparrot_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_1_miniparrot_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_1_miniparrot_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_1_l2e_override_p =
 '{mc_y_dim   : 1
   ,num_cce   : 2
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_1_l2e_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_1_l2e_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_1_l2e_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_1_l2e_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_1_l2e_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_1_l2e_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_1_l2e_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_1_l2e_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_1_l2e_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_1_l2e_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_1_l2e_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_1_l2e_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_1_l2e_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_1_l2e_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_1_l2e_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_1_l2e_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_1_l2e_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_1_l2e_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_1_l2e_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_1_l2e_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_1_l2e_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_1_l2e_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_1_l2e_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_1_l2e_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_1_l2e_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_1_l2e_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_1_l2e_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_1_l2e_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_1_l2e_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_1_l2e_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_1_l2e_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_1_l2e_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_1_l2e_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_1_l2e_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_1_l2e_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_1_l2e_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_1_l2e_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_1_l2e_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_1_l2e_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_1_l2e_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_1_l2e_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_1_l2e_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_1_l2e_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_1_l2e_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_1_l2e_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_1_l2e_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_1_l2e_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_1_l2e_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_1_l2e_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_1_l2e_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_1_l2e_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_1_l2e_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_1_l2e_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_1_l2e_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_1_l2e_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_1_l2e_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_1_l2e_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_1_l2e_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_1_l2e_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_1_l2e_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_1_l2e_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_1_l2e_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_1_l2e_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_1_l2e_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_1_l2e_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_1_l2e_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_1_l2e_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_1_l2e_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_1_l2e_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_1_l2e_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_1_l2e_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_1_l2e_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_1_l2e_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_1_l2e_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_1_l2e_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_1_l2e_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_1_l2e_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_1_l2e_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_1_l2e_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_1_l2e_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_1_l2e_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_1_l2e_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_1_l2e_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_1_l2e_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_1_l2e_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_1_l2e_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_1_l2e_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_1_l2e_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_1_l2e_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_1_l2e_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_1_l2e_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_1_l2e_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_1_l2e_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_1_l2e_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_1_l2e_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_1_l2e_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_1_l2e_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_1_l2e_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_1_l2e_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_1_l2e_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_1_l2e_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_1_l2e_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_1_l2e_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_1_l2e_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_1_l2e_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_1_l2e_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_1_l2e_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_1_l2e_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_1_l2e_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_1_l2e_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_1_l2e_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_1_l2e_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_1_l2e_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_1_l2e_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_1_l2e_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_1_l2e_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_1_l2e_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_1_l2e_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_1_l2e_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_1_l2e_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_1_l2e_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_1_l2e_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_1_l2e_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_1_l2e_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_1_l2e_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_1_l2e_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_1_l2e_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_1_l2e_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_1_l2e_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_1_l2e_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_1_l2e_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_1_l2e_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_1_l2e_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_1_l2e_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_1_l2e_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_1_l2e_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_1_l2e_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_1_l2e_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_1_l2e_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_1_l2e_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_1_l2e_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_1_l2e_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_1_l2e_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_1_l2e_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_1_l2e_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_2_override_p =
 '{cc_x_dim : 2
   ,num_cce : 2
   ,num_lce : 4
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_2_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_2_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_2_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_2_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_2_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_2_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_2_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_2_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_2_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_2_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_2_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_2_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_2_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_2_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_2_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_2_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_2_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_2_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_2_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_2_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_2_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_2_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_2_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_2_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_2_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_2_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_2_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_2_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_2_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_2_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_2_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_2_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_2_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_2_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_2_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_2_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_2_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_2_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_2_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_2_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_2_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_2_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_2_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_2_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_2_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_2_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_2_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_2_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_2_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_2_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_2_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_2_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_2_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_2_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_2_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_2_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_2_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_2_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_2_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_2_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_2_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_2_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_2_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_2_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_2_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_2_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_2_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_2_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_2_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_2_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_2_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_2_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_2_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_2_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_2_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_2_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_2_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_2_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_2_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_2_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_2_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_2_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_2_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_2_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_2_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_2_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_2_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_2_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_2_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_2_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_2_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_2_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_2_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_2_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_2_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_2_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_2_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_2_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_2_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_2_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_2_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_2_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_2_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_2_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_2_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_2_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_2_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_2_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_2_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_2_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_2_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_2_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_2_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_2_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_2_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_2_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_2_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_2_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_2_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_2_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_2_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_2_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_2_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_2_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_2_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_2_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_2_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_2_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_2_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_2_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_2_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_2_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_2_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_2_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_2_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_2_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_2_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_2_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_2_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_2_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_2_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_2_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_2_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_2_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_2_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_2_l2e_override_p =
 '{mc_y_dim   : 1
   ,num_cce   : 4
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_2_l2e_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_2_l2e_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_2_cfg_p.cc_x_dim           
                 : bp_multicore_2_l2e_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_2_l2e_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_2_cfg_p.cc_y_dim           
                 : bp_multicore_2_l2e_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_2_l2e_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_2_cfg_p.ic_y_dim           
                 : bp_multicore_2_l2e_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_2_l2e_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_2_cfg_p.mc_y_dim           
                 : bp_multicore_2_l2e_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_2_l2e_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_2_cfg_p.cac_x_dim           
                 : bp_multicore_2_l2e_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_2_l2e_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_2_cfg_p.sac_x_dim           
                 : bp_multicore_2_l2e_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_2_l2e_override_p.cacc_type == "inv") 
                 ? bp_multicore_2_cfg_p.cacc_type           
                 : bp_multicore_2_l2e_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_2_l2e_override_p.sacc_type == "inv") 
                 ? bp_multicore_2_cfg_p.sacc_type           
                 : bp_multicore_2_l2e_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_2_l2e_override_p.num_cce == "inv") 
                 ? bp_multicore_2_cfg_p.num_cce           
                 : bp_multicore_2_l2e_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_2_l2e_override_p.num_lce == "inv") 
                 ? bp_multicore_2_cfg_p.num_lce           
                 : bp_multicore_2_l2e_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_2_l2e_override_p.vaddr_width == "inv") 
                 ? bp_multicore_2_cfg_p.vaddr_width           
                 : bp_multicore_2_l2e_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_2_l2e_override_p.paddr_width == "inv") 
                 ? bp_multicore_2_cfg_p.paddr_width           
                 : bp_multicore_2_l2e_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_2_l2e_override_p.daddr_width == "inv") 
                 ? bp_multicore_2_cfg_p.daddr_width           
                 : bp_multicore_2_l2e_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_2_l2e_override_p.caddr_width == "inv") 
                 ? bp_multicore_2_cfg_p.caddr_width           
                 : bp_multicore_2_l2e_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_2_l2e_override_p.asid_width == "inv") 
                 ? bp_multicore_2_cfg_p.asid_width           
                 : bp_multicore_2_l2e_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_2_l2e_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_2_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_2_l2e_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_2_l2e_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_2_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_2_l2e_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_2_l2e_override_p.muldiv_support == "inv") 
                 ? bp_multicore_2_cfg_p.muldiv_support           
                 : bp_multicore_2_l2e_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_2_l2e_override_p.fpu_support == "inv") 
                 ? bp_multicore_2_cfg_p.fpu_support           
                 : bp_multicore_2_l2e_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_2_l2e_override_p.compressed_support == "inv") 
                 ? bp_multicore_2_cfg_p.compressed_support           
                 : bp_multicore_2_l2e_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_2_l2e_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_2_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_2_l2e_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_2_l2e_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_2_cfg_p.btb_tag_width           
                 : bp_multicore_2_l2e_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_2_l2e_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_2_cfg_p.btb_idx_width           
                 : bp_multicore_2_l2e_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_2_l2e_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_2_cfg_p.bht_idx_width           
                 : bp_multicore_2_l2e_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_2_l2e_override_p.bht_row_els == "inv") 
                 ? bp_multicore_2_cfg_p.bht_row_els           
                 : bp_multicore_2_l2e_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_2_l2e_override_p.ghist_width == "inv") 
                 ? bp_multicore_2_cfg_p.ghist_width           
                 : bp_multicore_2_l2e_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_2_l2e_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_2_cfg_p.itlb_els_4k           
                 : bp_multicore_2_l2e_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_2_l2e_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_2_cfg_p.itlb_els_1g           
                 : bp_multicore_2_l2e_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_2_l2e_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_2_cfg_p.dtlb_els_4k           
                 : bp_multicore_2_l2e_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_2_l2e_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_2_cfg_p.dtlb_els_1g           
                 : bp_multicore_2_l2e_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_2_l2e_override_p.icache_features == "inv") 
                 ? bp_multicore_2_cfg_p.icache_features           
                 : bp_multicore_2_l2e_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_2_l2e_override_p.icache_sets == "inv") 
                 ? bp_multicore_2_cfg_p.icache_sets           
                 : bp_multicore_2_l2e_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_2_l2e_override_p.icache_assoc == "inv") 
                 ? bp_multicore_2_cfg_p.icache_assoc           
                 : bp_multicore_2_l2e_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_2_l2e_override_p.icache_block_width == "inv") 
                 ? bp_multicore_2_cfg_p.icache_block_width           
                 : bp_multicore_2_l2e_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_2_l2e_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_2_cfg_p.icache_fill_width           
                 : bp_multicore_2_l2e_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_2_l2e_override_p.dcache_features == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_features           
                 : bp_multicore_2_l2e_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_2_l2e_override_p.dcache_sets == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_sets           
                 : bp_multicore_2_l2e_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_2_l2e_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_assoc           
                 : bp_multicore_2_l2e_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_2_l2e_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_block_width           
                 : bp_multicore_2_l2e_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_2_l2e_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_fill_width           
                 : bp_multicore_2_l2e_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_2_l2e_override_p.acache_features == "inv") 
                 ? bp_multicore_2_cfg_p.acache_features           
                 : bp_multicore_2_l2e_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_2_l2e_override_p.acache_sets == "inv") 
                 ? bp_multicore_2_cfg_p.acache_sets           
                 : bp_multicore_2_l2e_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_2_l2e_override_p.acache_assoc == "inv") 
                 ? bp_multicore_2_cfg_p.acache_assoc           
                 : bp_multicore_2_l2e_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_2_l2e_override_p.acache_block_width == "inv") 
                 ? bp_multicore_2_cfg_p.acache_block_width           
                 : bp_multicore_2_l2e_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_2_l2e_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_2_cfg_p.acache_fill_width           
                 : bp_multicore_2_l2e_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_2_l2e_override_p.cce_type == "inv") 
                 ? bp_multicore_2_cfg_p.cce_type           
                 : bp_multicore_2_l2e_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_2_l2e_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_2_cfg_p.cce_pc_width           
                 : bp_multicore_2_l2e_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_2_l2e_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_2_cfg_p.bedrock_data_width           
                 : bp_multicore_2_l2e_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_2_l2e_override_p.l2_features == "inv") 
                 ? bp_multicore_2_cfg_p.l2_features           
                 : bp_multicore_2_l2e_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_2_l2e_override_p.l2_banks == "inv") 
                 ? bp_multicore_2_cfg_p.l2_banks           
                 : bp_multicore_2_l2e_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_2_l2e_override_p.l2_data_width == "inv") 
                 ? bp_multicore_2_cfg_p.l2_data_width           
                 : bp_multicore_2_l2e_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_2_l2e_override_p.l2_sets == "inv") 
                 ? bp_multicore_2_cfg_p.l2_sets           
                 : bp_multicore_2_l2e_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_2_l2e_override_p.l2_assoc == "inv") 
                 ? bp_multicore_2_cfg_p.l2_assoc           
                 : bp_multicore_2_l2e_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_2_l2e_override_p.l2_block_width == "inv") 
                 ? bp_multicore_2_cfg_p.l2_block_width           
                 : bp_multicore_2_l2e_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_2_l2e_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_2_cfg_p.l2_fill_width           
                 : bp_multicore_2_l2e_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_2_l2e_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_2_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_2_l2e_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_2_l2e_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_2_cfg_p.async_coh_clk           
                 : bp_multicore_2_l2e_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_2_l2e_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_2_cfg_p.coh_noc_max_credits           
                 : bp_multicore_2_l2e_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_2_l2e_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_2_cfg_p.coh_noc_flit_width           
                 : bp_multicore_2_l2e_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_2_l2e_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_2_cfg_p.coh_noc_cid_width           
                 : bp_multicore_2_l2e_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_2_l2e_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_2_cfg_p.coh_noc_len_width           
                 : bp_multicore_2_l2e_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_2_l2e_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_2_cfg_p.async_mem_clk           
                 : bp_multicore_2_l2e_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_2_l2e_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_2_cfg_p.mem_noc_max_credits           
                 : bp_multicore_2_l2e_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_2_l2e_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_2_cfg_p.mem_noc_flit_width           
                 : bp_multicore_2_l2e_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_2_l2e_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_2_cfg_p.mem_noc_cid_width           
                 : bp_multicore_2_l2e_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_2_l2e_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_2_cfg_p.mem_noc_len_width           
                 : bp_multicore_2_l2e_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_2_l2e_override_p.async_io_clk == "inv") 
                 ? bp_multicore_2_cfg_p.async_io_clk           
                 : bp_multicore_2_l2e_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_2_l2e_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_max_credits           
                 : bp_multicore_2_l2e_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_2_l2e_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_flit_width           
                 : bp_multicore_2_l2e_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_2_l2e_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_cid_width           
                 : bp_multicore_2_l2e_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_2_l2e_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_did_width           
                 : bp_multicore_2_l2e_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_2_l2e_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_len_width           
                 : bp_multicore_2_l2e_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_3_override_p =
 '{cc_x_dim : 3
   ,num_cce : 3
   ,num_lce : 6
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_3_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_3_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_3_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_3_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_3_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_3_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_3_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_3_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_3_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_3_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_3_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_3_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_3_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_3_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_3_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_3_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_3_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_3_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_3_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_3_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_3_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_3_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_3_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_3_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_3_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_3_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_3_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_3_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_3_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_3_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_3_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_3_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_3_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_3_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_3_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_3_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_3_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_3_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_3_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_3_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_3_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_3_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_3_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_3_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_3_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_3_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_3_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_3_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_3_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_3_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_3_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_3_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_3_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_3_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_3_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_3_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_3_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_3_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_3_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_3_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_3_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_3_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_3_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_3_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_3_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_3_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_3_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_3_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_3_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_3_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_3_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_3_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_3_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_3_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_3_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_3_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_3_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_3_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_3_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_3_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_3_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_3_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_3_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_3_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_3_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_3_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_3_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_3_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_3_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_3_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_3_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_3_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_3_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_3_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_3_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_3_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_3_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_3_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_3_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_3_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_3_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_3_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_3_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_3_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_3_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_3_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_3_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_3_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_3_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_3_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_3_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_3_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_3_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_3_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_3_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_3_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_3_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_3_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_3_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_3_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_3_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_3_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_3_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_3_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_3_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_3_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_3_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_3_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_3_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_3_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_3_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_3_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_3_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_3_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_3_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_3_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_3_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_3_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_3_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_3_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_3_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_3_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_3_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_3_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_3_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_4_override_p =
 '{cc_x_dim : 2
   ,cc_y_dim: 2
   ,num_cce : 4
   ,num_lce : 8
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_4_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_4_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_4_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_4_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_4_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_4_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_4_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_4_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_4_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_4_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_4_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_4_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_4_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_4_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_4_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_4_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_4_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_4_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_4_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_4_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_4_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_4_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_4_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_4_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_4_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_4_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_4_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_4_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_4_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_4_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_4_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_4_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_4_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_4_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_4_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_4_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_4_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_4_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_4_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_4_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_4_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_4_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_4_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_4_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_4_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_4_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_4_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_4_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_4_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_4_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_4_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_4_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_4_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_4_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_4_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_4_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_4_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_4_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_4_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_4_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_4_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_4_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_4_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_4_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_4_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_4_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_4_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_4_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_4_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_4_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_4_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_4_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_4_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_4_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_4_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_4_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_4_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_4_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_4_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_4_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_4_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_4_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_4_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_4_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_4_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_4_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_4_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_4_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_4_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_4_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_4_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_4_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_4_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_4_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_4_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_4_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_4_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_4_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_4_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_4_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_4_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_4_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_4_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_4_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_4_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_4_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_4_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_4_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_4_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_4_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_4_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_4_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_4_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_4_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_4_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_4_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_4_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_4_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_4_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_4_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_4_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_4_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_4_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_4_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_4_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_4_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_4_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_4_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_4_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_4_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_4_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_4_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_4_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_4_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_4_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_4_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_4_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_4_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_4_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_4_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_4_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_4_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_4_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_4_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_4_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_4_l2e_override_p =
 '{mc_y_dim   : 1
   ,num_cce   : 6
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_4_l2e_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_4_l2e_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cc_x_dim           
                 : bp_multicore_4_l2e_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_4_l2e_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cc_y_dim           
                 : bp_multicore_4_l2e_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_4_l2e_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.ic_y_dim           
                 : bp_multicore_4_l2e_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_4_l2e_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.mc_y_dim           
                 : bp_multicore_4_l2e_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_4_l2e_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cac_x_dim           
                 : bp_multicore_4_l2e_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_4_l2e_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.sac_x_dim           
                 : bp_multicore_4_l2e_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_4_l2e_override_p.cacc_type == "inv") 
                 ? bp_multicore_4_cfg_p.cacc_type           
                 : bp_multicore_4_l2e_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_4_l2e_override_p.sacc_type == "inv") 
                 ? bp_multicore_4_cfg_p.sacc_type           
                 : bp_multicore_4_l2e_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_4_l2e_override_p.num_cce == "inv") 
                 ? bp_multicore_4_cfg_p.num_cce           
                 : bp_multicore_4_l2e_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_4_l2e_override_p.num_lce == "inv") 
                 ? bp_multicore_4_cfg_p.num_lce           
                 : bp_multicore_4_l2e_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_4_l2e_override_p.vaddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.vaddr_width           
                 : bp_multicore_4_l2e_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_4_l2e_override_p.paddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.paddr_width           
                 : bp_multicore_4_l2e_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_4_l2e_override_p.daddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.daddr_width           
                 : bp_multicore_4_l2e_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_4_l2e_override_p.caddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.caddr_width           
                 : bp_multicore_4_l2e_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_4_l2e_override_p.asid_width == "inv") 
                 ? bp_multicore_4_cfg_p.asid_width           
                 : bp_multicore_4_l2e_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_4_l2e_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_4_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_4_l2e_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_4_l2e_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_4_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_4_l2e_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_4_l2e_override_p.muldiv_support == "inv") 
                 ? bp_multicore_4_cfg_p.muldiv_support           
                 : bp_multicore_4_l2e_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_4_l2e_override_p.fpu_support == "inv") 
                 ? bp_multicore_4_cfg_p.fpu_support           
                 : bp_multicore_4_l2e_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_4_l2e_override_p.compressed_support == "inv") 
                 ? bp_multicore_4_cfg_p.compressed_support           
                 : bp_multicore_4_l2e_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_4_l2e_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_4_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_4_l2e_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_4_l2e_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_4_cfg_p.btb_tag_width           
                 : bp_multicore_4_l2e_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_4_l2e_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_4_cfg_p.btb_idx_width           
                 : bp_multicore_4_l2e_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_4_l2e_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_4_cfg_p.bht_idx_width           
                 : bp_multicore_4_l2e_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_4_l2e_override_p.bht_row_els == "inv") 
                 ? bp_multicore_4_cfg_p.bht_row_els           
                 : bp_multicore_4_l2e_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_4_l2e_override_p.ghist_width == "inv") 
                 ? bp_multicore_4_cfg_p.ghist_width           
                 : bp_multicore_4_l2e_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_4_l2e_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_4_cfg_p.itlb_els_4k           
                 : bp_multicore_4_l2e_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_4_l2e_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_4_cfg_p.itlb_els_1g           
                 : bp_multicore_4_l2e_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_4_l2e_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_4_cfg_p.dtlb_els_4k           
                 : bp_multicore_4_l2e_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_4_l2e_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_4_cfg_p.dtlb_els_1g           
                 : bp_multicore_4_l2e_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_4_l2e_override_p.icache_features == "inv") 
                 ? bp_multicore_4_cfg_p.icache_features           
                 : bp_multicore_4_l2e_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_4_l2e_override_p.icache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.icache_sets           
                 : bp_multicore_4_l2e_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_4_l2e_override_p.icache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.icache_assoc           
                 : bp_multicore_4_l2e_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_4_l2e_override_p.icache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.icache_block_width           
                 : bp_multicore_4_l2e_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_4_l2e_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.icache_fill_width           
                 : bp_multicore_4_l2e_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_4_l2e_override_p.dcache_features == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_features           
                 : bp_multicore_4_l2e_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_4_l2e_override_p.dcache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_sets           
                 : bp_multicore_4_l2e_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_4_l2e_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_assoc           
                 : bp_multicore_4_l2e_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_4_l2e_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_block_width           
                 : bp_multicore_4_l2e_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_4_l2e_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_fill_width           
                 : bp_multicore_4_l2e_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_4_l2e_override_p.acache_features == "inv") 
                 ? bp_multicore_4_cfg_p.acache_features           
                 : bp_multicore_4_l2e_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_4_l2e_override_p.acache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.acache_sets           
                 : bp_multicore_4_l2e_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_4_l2e_override_p.acache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.acache_assoc           
                 : bp_multicore_4_l2e_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_4_l2e_override_p.acache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.acache_block_width           
                 : bp_multicore_4_l2e_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_4_l2e_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.acache_fill_width           
                 : bp_multicore_4_l2e_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_4_l2e_override_p.cce_type == "inv") 
                 ? bp_multicore_4_cfg_p.cce_type           
                 : bp_multicore_4_l2e_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_4_l2e_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_4_cfg_p.cce_pc_width           
                 : bp_multicore_4_l2e_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_4_l2e_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_4_cfg_p.bedrock_data_width           
                 : bp_multicore_4_l2e_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_4_l2e_override_p.l2_features == "inv") 
                 ? bp_multicore_4_cfg_p.l2_features           
                 : bp_multicore_4_l2e_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_4_l2e_override_p.l2_banks == "inv") 
                 ? bp_multicore_4_cfg_p.l2_banks           
                 : bp_multicore_4_l2e_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_4_l2e_override_p.l2_data_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_data_width           
                 : bp_multicore_4_l2e_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_4_l2e_override_p.l2_sets == "inv") 
                 ? bp_multicore_4_cfg_p.l2_sets           
                 : bp_multicore_4_l2e_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_4_l2e_override_p.l2_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.l2_assoc           
                 : bp_multicore_4_l2e_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_4_l2e_override_p.l2_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_block_width           
                 : bp_multicore_4_l2e_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_4_l2e_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_fill_width           
                 : bp_multicore_4_l2e_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_4_l2e_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_4_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_4_l2e_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_4_l2e_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_coh_clk           
                 : bp_multicore_4_l2e_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_4_l2e_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_max_credits           
                 : bp_multicore_4_l2e_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_4_l2e_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_flit_width           
                 : bp_multicore_4_l2e_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_4_l2e_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_cid_width           
                 : bp_multicore_4_l2e_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_4_l2e_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_len_width           
                 : bp_multicore_4_l2e_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_4_l2e_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_mem_clk           
                 : bp_multicore_4_l2e_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_4_l2e_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_max_credits           
                 : bp_multicore_4_l2e_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_4_l2e_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_flit_width           
                 : bp_multicore_4_l2e_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_4_l2e_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_cid_width           
                 : bp_multicore_4_l2e_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_4_l2e_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_len_width           
                 : bp_multicore_4_l2e_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_4_l2e_override_p.async_io_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_io_clk           
                 : bp_multicore_4_l2e_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_4_l2e_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_max_credits           
                 : bp_multicore_4_l2e_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_4_l2e_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_flit_width           
                 : bp_multicore_4_l2e_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_4_l2e_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_cid_width           
                 : bp_multicore_4_l2e_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_4_l2e_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_did_width           
                 : bp_multicore_4_l2e_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_4_l2e_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_len_width           
                 : bp_multicore_4_l2e_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_6_override_p =
 '{cc_x_dim : 3
   ,cc_y_dim: 2
   ,num_cce : 6
   ,num_lce : 12
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_6_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_6_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_6_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_6_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_6_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_6_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_6_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_6_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_6_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_6_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_6_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_6_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_6_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_6_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_6_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_6_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_6_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_6_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_6_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_6_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_6_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_6_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_6_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_6_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_6_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_6_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_6_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_6_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_6_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_6_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_6_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_6_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_6_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_6_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_6_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_6_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_6_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_6_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_6_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_6_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_6_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_6_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_6_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_6_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_6_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_6_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_6_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_6_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_6_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_6_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_6_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_6_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_6_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_6_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_6_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_6_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_6_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_6_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_6_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_6_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_6_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_6_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_6_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_6_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_6_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_6_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_6_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_6_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_6_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_6_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_6_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_6_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_6_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_6_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_6_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_6_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_6_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_6_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_6_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_6_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_6_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_6_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_6_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_6_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_6_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_6_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_6_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_6_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_6_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_6_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_6_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_6_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_6_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_6_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_6_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_6_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_6_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_6_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_6_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_6_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_6_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_6_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_6_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_6_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_6_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_6_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_6_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_6_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_6_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_6_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_6_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_6_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_6_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_6_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_6_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_6_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_6_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_6_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_6_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_6_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_6_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_6_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_6_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_6_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_6_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_6_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_6_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_6_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_6_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_6_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_6_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_6_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_6_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_6_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_6_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_6_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_6_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_6_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_6_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_6_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_6_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_6_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_6_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_6_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_6_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_8_override_p =
 '{cc_x_dim : 4
   ,cc_y_dim: 2
   ,num_cce : 8
   ,num_lce : 16
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_8_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_8_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_8_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_8_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_8_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_8_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_8_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_8_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_8_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_8_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_8_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_8_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_8_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_8_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_8_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_8_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_8_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_8_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_8_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_8_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_8_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_8_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_8_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_8_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_8_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_8_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_8_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_8_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_8_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_8_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_8_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_8_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_8_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_8_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_8_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_8_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_8_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_8_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_8_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_8_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_8_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_8_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_8_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_8_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_8_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_8_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_8_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_8_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_8_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_8_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_8_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_8_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_8_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_8_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_8_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_8_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_8_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_8_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_8_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_8_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_8_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_8_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_8_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_8_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_8_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_8_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_8_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_8_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_8_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_8_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_8_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_8_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_8_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_8_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_8_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_8_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_8_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_8_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_8_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_8_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_8_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_8_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_8_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_8_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_8_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_8_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_8_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_8_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_8_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_8_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_8_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_8_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_8_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_8_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_8_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_8_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_8_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_8_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_8_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_8_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_8_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_8_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_8_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_8_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_8_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_8_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_8_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_8_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_8_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_8_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_8_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_8_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_8_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_8_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_8_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_8_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_8_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_8_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_8_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_8_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_8_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_8_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_8_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_8_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_8_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_8_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_8_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_8_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_8_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_8_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_8_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_8_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_8_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_8_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_8_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_8_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_8_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_8_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_8_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_8_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_8_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_8_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_8_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_8_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_8_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_12_override_p =
 '{cc_x_dim : 4
   ,cc_y_dim: 3
   ,num_cce : 12
   ,num_lce : 24
   ,l2_banks: 1
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_12_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_12_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_12_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_12_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_12_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_12_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_12_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_12_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_12_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_12_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_12_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_12_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_12_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_12_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_12_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_12_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_12_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_12_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_12_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_12_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_12_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_12_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_12_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_12_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_12_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_12_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_12_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_12_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_12_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_12_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_12_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_12_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_12_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_12_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_12_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_12_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_12_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_12_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_12_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_12_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_12_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_12_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_12_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_12_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_12_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_12_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_12_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_12_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_12_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_12_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_12_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_12_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_12_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_12_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_12_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_12_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_12_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_12_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_12_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_12_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_12_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_12_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_12_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_12_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_12_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_12_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_12_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_12_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_12_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_12_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_12_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_12_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_12_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_12_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_12_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_12_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_12_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_12_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_12_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_12_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_12_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_12_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_12_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_12_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_12_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_12_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_12_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_12_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_12_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_12_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_12_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_12_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_12_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_12_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_12_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_12_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_12_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_12_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_12_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_12_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_12_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_12_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_12_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_12_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_12_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_12_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_12_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_12_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_12_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_12_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_12_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_12_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_12_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_12_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_12_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_12_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_12_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_12_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_12_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_12_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_12_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_12_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_12_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_12_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_12_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_12_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_12_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_12_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_12_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_12_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_12_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_12_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_12_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_12_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_12_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_12_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_12_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_12_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_12_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_12_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_12_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_12_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_12_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_12_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_12_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_16_override_p =
 '{cc_x_dim : 4
   ,cc_y_dim: 4
   ,num_cce : 16
   ,num_lce : 32
   ,l2_banks: 1
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_16_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_16_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_16_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_16_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_16_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_16_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_16_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_16_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_16_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_16_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_16_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_16_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_16_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_16_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_16_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_16_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_16_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_16_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_16_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_16_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_16_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_16_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_16_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_16_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_16_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_16_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_16_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_16_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_16_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_16_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_16_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_16_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_16_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_16_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_16_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_16_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_16_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_16_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_16_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_16_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_16_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_16_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_16_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_16_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_16_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_16_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_16_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_16_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_16_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_16_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_16_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_16_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_16_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_16_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_16_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_16_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_16_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_16_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_16_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_16_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_16_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_16_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_16_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_16_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_16_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_16_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_16_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_16_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_16_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_16_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_16_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_16_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_16_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_16_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_16_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_16_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_16_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_16_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_16_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_16_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_16_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_16_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_16_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_16_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_16_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_16_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_16_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_16_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_16_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_16_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_16_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_16_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_16_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_16_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_16_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_16_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_16_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_16_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_16_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_16_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_16_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_16_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_16_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_16_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_16_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_16_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_16_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_16_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_16_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_16_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_16_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_16_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_16_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_16_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_16_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_16_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_16_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_16_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_16_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_16_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_16_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_16_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_16_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_16_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_16_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_16_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_16_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_16_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_16_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_16_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_16_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_16_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_16_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_16_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_16_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_16_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_16_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_16_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_16_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_16_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_16_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_16_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_16_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_16_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_16_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_1_acc_scratchpad_override_p =
 '{sac_x_dim: 1
   ,sacc_type: e_sacc_scratchpad
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_1_acc_scratchpad_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_1_acc_scratchpad_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_1_acc_scratchpad_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_1_acc_scratchpad_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_1_acc_scratchpad_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_1_acc_scratchpad_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_1_acc_scratchpad_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_1_acc_scratchpad_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_1_acc_scratchpad_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_1_acc_scratchpad_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_1_acc_scratchpad_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_1_acc_scratchpad_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_1_acc_scratchpad_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_1_acc_scratchpad_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_1_acc_scratchpad_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_1_acc_scratchpad_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_1_acc_scratchpad_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_1_acc_scratchpad_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_1_acc_scratchpad_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_1_acc_scratchpad_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_1_acc_scratchpad_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_1_acc_scratchpad_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_1_acc_scratchpad_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_1_acc_scratchpad_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_1_acc_scratchpad_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_1_acc_scratchpad_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_1_acc_scratchpad_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_1_acc_scratchpad_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_1_acc_scratchpad_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_1_acc_scratchpad_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_1_acc_scratchpad_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_1_acc_scratchpad_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_1_acc_scratchpad_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_1_acc_scratchpad_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_1_acc_scratchpad_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_1_acc_scratchpad_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_1_acc_scratchpad_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_1_acc_scratchpad_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_1_acc_scratchpad_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_1_acc_scratchpad_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_1_acc_scratchpad_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_1_acc_scratchpad_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_1_acc_scratchpad_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_1_acc_scratchpad_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_1_acc_scratchpad_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_1_acc_scratchpad_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_1_acc_scratchpad_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_1_acc_scratchpad_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_1_acc_scratchpad_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_1_acc_scratchpad_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_1_acc_scratchpad_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_1_acc_scratchpad_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_1_acc_scratchpad_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_1_acc_scratchpad_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_1_acc_scratchpad_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_1_acc_scratchpad_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_1_acc_scratchpad_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_1_acc_scratchpad_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_1_acc_scratchpad_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_1_acc_scratchpad_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_1_acc_scratchpad_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_1_acc_scratchpad_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_1_acc_scratchpad_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_1_acc_scratchpad_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_1_acc_scratchpad_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_1_acc_scratchpad_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_1_acc_scratchpad_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_1_acc_scratchpad_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_1_acc_scratchpad_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_1_acc_scratchpad_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_1_acc_scratchpad_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_1_acc_scratchpad_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_1_acc_scratchpad_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_1_acc_scratchpad_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_1_acc_scratchpad_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_1_acc_scratchpad_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_1_acc_scratchpad_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_1_acc_scratchpad_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_1_acc_scratchpad_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_1_acc_scratchpad_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_1_acc_scratchpad_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_1_acc_scratchpad_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_1_acc_scratchpad_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_1_acc_scratchpad_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_1_acc_scratchpad_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_1_acc_scratchpad_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_1_acc_scratchpad_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_1_acc_scratchpad_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_1_acc_scratchpad_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_1_acc_scratchpad_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_1_acc_scratchpad_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_1_acc_scratchpad_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_1_acc_scratchpad_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_1_acc_scratchpad_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_1_acc_scratchpad_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_1_acc_scratchpad_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_1_acc_scratchpad_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_1_acc_scratchpad_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_1_acc_scratchpad_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_1_acc_scratchpad_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_1_acc_scratchpad_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_1_acc_scratchpad_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_1_acc_scratchpad_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_1_acc_scratchpad_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_1_acc_scratchpad_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_1_acc_scratchpad_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_1_acc_scratchpad_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_1_acc_scratchpad_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_1_acc_scratchpad_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_1_acc_scratchpad_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_1_acc_scratchpad_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_1_acc_scratchpad_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_1_acc_scratchpad_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_1_acc_scratchpad_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_1_acc_scratchpad_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_1_acc_scratchpad_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_1_acc_scratchpad_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_1_acc_scratchpad_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_1_acc_scratchpad_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_1_acc_scratchpad_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_1_acc_scratchpad_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_1_acc_scratchpad_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_1_acc_scratchpad_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_1_acc_scratchpad_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_1_acc_scratchpad_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_1_acc_scratchpad_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_1_acc_scratchpad_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_1_acc_scratchpad_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_1_acc_scratchpad_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_1_acc_scratchpad_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_1_acc_scratchpad_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_1_acc_scratchpad_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_1_acc_scratchpad_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_1_acc_scratchpad_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_1_acc_scratchpad_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_1_acc_scratchpad_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_1_acc_scratchpad_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_1_acc_scratchpad_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_1_acc_scratchpad_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_1_acc_scratchpad_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_1_acc_scratchpad_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_1_acc_scratchpad_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_1_acc_scratchpad_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_1_acc_scratchpad_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_1_acc_scratchpad_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_1_acc_vdp_override_p =
 '{cac_x_dim : 1
   ,sac_x_dim: 1
   ,cacc_type: e_cacc_vdp
   ,sacc_type: e_sacc_vdp
   ,num_lce  : 3
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_1_acc_vdp_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_1_acc_vdp_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_1_acc_vdp_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_1_acc_vdp_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_1_acc_vdp_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_1_acc_vdp_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_1_acc_vdp_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_1_acc_vdp_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_1_acc_vdp_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_1_acc_vdp_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_1_acc_vdp_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_1_acc_vdp_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_1_acc_vdp_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_1_acc_vdp_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_1_acc_vdp_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_1_acc_vdp_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_1_acc_vdp_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_1_acc_vdp_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_1_acc_vdp_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_1_acc_vdp_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_1_acc_vdp_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_1_acc_vdp_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_1_acc_vdp_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_1_acc_vdp_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_1_acc_vdp_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_1_acc_vdp_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_1_acc_vdp_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_1_acc_vdp_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_1_acc_vdp_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_1_acc_vdp_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_1_acc_vdp_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_1_acc_vdp_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_1_acc_vdp_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_1_acc_vdp_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_1_acc_vdp_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_1_acc_vdp_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_1_acc_vdp_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_1_acc_vdp_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_1_acc_vdp_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_1_acc_vdp_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_1_acc_vdp_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_1_acc_vdp_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_1_acc_vdp_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_1_acc_vdp_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_1_acc_vdp_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_1_acc_vdp_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_1_acc_vdp_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_1_acc_vdp_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_1_acc_vdp_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_1_acc_vdp_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_1_acc_vdp_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_1_acc_vdp_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_1_acc_vdp_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_1_acc_vdp_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_1_acc_vdp_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_1_acc_vdp_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_1_acc_vdp_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_1_acc_vdp_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_1_acc_vdp_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_1_acc_vdp_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_1_acc_vdp_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_1_acc_vdp_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_1_acc_vdp_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_1_acc_vdp_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_1_acc_vdp_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_1_acc_vdp_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_1_acc_vdp_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_1_acc_vdp_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_1_acc_vdp_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_1_acc_vdp_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_1_acc_vdp_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_1_acc_vdp_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_1_acc_vdp_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_1_acc_vdp_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_1_acc_vdp_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_1_acc_vdp_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_1_acc_vdp_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_1_acc_vdp_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_1_acc_vdp_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_1_acc_vdp_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_1_acc_vdp_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_1_acc_vdp_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_1_acc_vdp_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_1_acc_vdp_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_1_acc_vdp_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_1_acc_vdp_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_1_acc_vdp_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_1_acc_vdp_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_1_acc_vdp_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_1_acc_vdp_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_1_acc_vdp_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_1_acc_vdp_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_1_acc_vdp_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_1_acc_vdp_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_1_acc_vdp_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_1_acc_vdp_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_1_acc_vdp_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_1_acc_vdp_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_1_acc_vdp_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_1_acc_vdp_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_1_acc_vdp_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_1_acc_vdp_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_1_acc_vdp_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_1_acc_vdp_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_1_acc_vdp_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_1_acc_vdp_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_1_acc_vdp_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_1_acc_vdp_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_1_acc_vdp_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_1_acc_vdp_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_1_acc_vdp_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_1_acc_vdp_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_1_acc_vdp_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_1_acc_vdp_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_1_acc_vdp_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_1_acc_vdp_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_1_acc_vdp_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_1_acc_vdp_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_1_acc_vdp_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_1_acc_vdp_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_1_acc_vdp_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_1_acc_vdp_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_1_acc_vdp_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_1_acc_vdp_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_1_acc_vdp_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_1_acc_vdp_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_1_acc_vdp_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_1_acc_vdp_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_1_acc_vdp_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_1_acc_vdp_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_1_acc_vdp_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_1_acc_vdp_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_1_acc_vdp_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_1_acc_vdp_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_1_acc_vdp_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_1_acc_vdp_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_1_acc_vdp_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_1_acc_vdp_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_1_acc_vdp_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_1_acc_vdp_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_1_acc_vdp_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_1_acc_vdp_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_1_acc_vdp_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_1_acc_vdp_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_1_acc_vdp_override_p.io_noc_len_width          
     
       }
;


localparam bp_proc_param_s bp_multicore_4_acc_scratchpad_override_p =
 '{sac_x_dim : 1
   ,sacc_type: e_sacc_scratchpad
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_4_acc_scratchpad_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_4_acc_scratchpad_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cc_x_dim           
                 : bp_multicore_4_acc_scratchpad_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_4_acc_scratchpad_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cc_y_dim           
                 : bp_multicore_4_acc_scratchpad_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_4_acc_scratchpad_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.ic_y_dim           
                 : bp_multicore_4_acc_scratchpad_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_4_acc_scratchpad_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.mc_y_dim           
                 : bp_multicore_4_acc_scratchpad_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_4_acc_scratchpad_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cac_x_dim           
                 : bp_multicore_4_acc_scratchpad_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_4_acc_scratchpad_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.sac_x_dim           
                 : bp_multicore_4_acc_scratchpad_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_4_acc_scratchpad_override_p.cacc_type == "inv") 
                 ? bp_multicore_4_cfg_p.cacc_type           
                 : bp_multicore_4_acc_scratchpad_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_4_acc_scratchpad_override_p.sacc_type == "inv") 
                 ? bp_multicore_4_cfg_p.sacc_type           
                 : bp_multicore_4_acc_scratchpad_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_4_acc_scratchpad_override_p.num_cce == "inv") 
                 ? bp_multicore_4_cfg_p.num_cce           
                 : bp_multicore_4_acc_scratchpad_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_4_acc_scratchpad_override_p.num_lce == "inv") 
                 ? bp_multicore_4_cfg_p.num_lce           
                 : bp_multicore_4_acc_scratchpad_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_4_acc_scratchpad_override_p.vaddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.vaddr_width           
                 : bp_multicore_4_acc_scratchpad_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_4_acc_scratchpad_override_p.paddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.paddr_width           
                 : bp_multicore_4_acc_scratchpad_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_4_acc_scratchpad_override_p.daddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.daddr_width           
                 : bp_multicore_4_acc_scratchpad_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_4_acc_scratchpad_override_p.caddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.caddr_width           
                 : bp_multicore_4_acc_scratchpad_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_4_acc_scratchpad_override_p.asid_width == "inv") 
                 ? bp_multicore_4_cfg_p.asid_width           
                 : bp_multicore_4_acc_scratchpad_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_4_acc_scratchpad_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_4_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_4_acc_scratchpad_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_4_acc_scratchpad_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_4_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_4_acc_scratchpad_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_4_acc_scratchpad_override_p.muldiv_support == "inv") 
                 ? bp_multicore_4_cfg_p.muldiv_support           
                 : bp_multicore_4_acc_scratchpad_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_4_acc_scratchpad_override_p.fpu_support == "inv") 
                 ? bp_multicore_4_cfg_p.fpu_support           
                 : bp_multicore_4_acc_scratchpad_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_4_acc_scratchpad_override_p.compressed_support == "inv") 
                 ? bp_multicore_4_cfg_p.compressed_support           
                 : bp_multicore_4_acc_scratchpad_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_4_acc_scratchpad_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_4_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_4_acc_scratchpad_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_4_acc_scratchpad_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_4_cfg_p.btb_tag_width           
                 : bp_multicore_4_acc_scratchpad_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_4_acc_scratchpad_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_4_cfg_p.btb_idx_width           
                 : bp_multicore_4_acc_scratchpad_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_4_acc_scratchpad_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_4_cfg_p.bht_idx_width           
                 : bp_multicore_4_acc_scratchpad_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_4_acc_scratchpad_override_p.bht_row_els == "inv") 
                 ? bp_multicore_4_cfg_p.bht_row_els           
                 : bp_multicore_4_acc_scratchpad_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_4_acc_scratchpad_override_p.ghist_width == "inv") 
                 ? bp_multicore_4_cfg_p.ghist_width           
                 : bp_multicore_4_acc_scratchpad_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_4_acc_scratchpad_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_4_cfg_p.itlb_els_4k           
                 : bp_multicore_4_acc_scratchpad_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_4_acc_scratchpad_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_4_cfg_p.itlb_els_1g           
                 : bp_multicore_4_acc_scratchpad_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_4_acc_scratchpad_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_4_cfg_p.dtlb_els_4k           
                 : bp_multicore_4_acc_scratchpad_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_4_acc_scratchpad_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_4_cfg_p.dtlb_els_1g           
                 : bp_multicore_4_acc_scratchpad_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_4_acc_scratchpad_override_p.icache_features == "inv") 
                 ? bp_multicore_4_cfg_p.icache_features           
                 : bp_multicore_4_acc_scratchpad_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_4_acc_scratchpad_override_p.icache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.icache_sets           
                 : bp_multicore_4_acc_scratchpad_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_4_acc_scratchpad_override_p.icache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.icache_assoc           
                 : bp_multicore_4_acc_scratchpad_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_4_acc_scratchpad_override_p.icache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.icache_block_width           
                 : bp_multicore_4_acc_scratchpad_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_4_acc_scratchpad_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.icache_fill_width           
                 : bp_multicore_4_acc_scratchpad_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_4_acc_scratchpad_override_p.dcache_features == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_features           
                 : bp_multicore_4_acc_scratchpad_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_4_acc_scratchpad_override_p.dcache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_sets           
                 : bp_multicore_4_acc_scratchpad_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_4_acc_scratchpad_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_assoc           
                 : bp_multicore_4_acc_scratchpad_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_4_acc_scratchpad_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_block_width           
                 : bp_multicore_4_acc_scratchpad_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_4_acc_scratchpad_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_fill_width           
                 : bp_multicore_4_acc_scratchpad_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_4_acc_scratchpad_override_p.acache_features == "inv") 
                 ? bp_multicore_4_cfg_p.acache_features           
                 : bp_multicore_4_acc_scratchpad_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_4_acc_scratchpad_override_p.acache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.acache_sets           
                 : bp_multicore_4_acc_scratchpad_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_4_acc_scratchpad_override_p.acache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.acache_assoc           
                 : bp_multicore_4_acc_scratchpad_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_4_acc_scratchpad_override_p.acache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.acache_block_width           
                 : bp_multicore_4_acc_scratchpad_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_4_acc_scratchpad_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.acache_fill_width           
                 : bp_multicore_4_acc_scratchpad_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_4_acc_scratchpad_override_p.cce_type == "inv") 
                 ? bp_multicore_4_cfg_p.cce_type           
                 : bp_multicore_4_acc_scratchpad_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_4_acc_scratchpad_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_4_cfg_p.cce_pc_width           
                 : bp_multicore_4_acc_scratchpad_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_4_acc_scratchpad_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_4_cfg_p.bedrock_data_width           
                 : bp_multicore_4_acc_scratchpad_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_4_acc_scratchpad_override_p.l2_features == "inv") 
                 ? bp_multicore_4_cfg_p.l2_features           
                 : bp_multicore_4_acc_scratchpad_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_4_acc_scratchpad_override_p.l2_banks == "inv") 
                 ? bp_multicore_4_cfg_p.l2_banks           
                 : bp_multicore_4_acc_scratchpad_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_4_acc_scratchpad_override_p.l2_data_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_data_width           
                 : bp_multicore_4_acc_scratchpad_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_4_acc_scratchpad_override_p.l2_sets == "inv") 
                 ? bp_multicore_4_cfg_p.l2_sets           
                 : bp_multicore_4_acc_scratchpad_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_4_acc_scratchpad_override_p.l2_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.l2_assoc           
                 : bp_multicore_4_acc_scratchpad_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_4_acc_scratchpad_override_p.l2_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_block_width           
                 : bp_multicore_4_acc_scratchpad_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_4_acc_scratchpad_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_fill_width           
                 : bp_multicore_4_acc_scratchpad_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_4_acc_scratchpad_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_4_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_4_acc_scratchpad_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_4_acc_scratchpad_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_coh_clk           
                 : bp_multicore_4_acc_scratchpad_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_4_acc_scratchpad_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_max_credits           
                 : bp_multicore_4_acc_scratchpad_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_4_acc_scratchpad_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_flit_width           
                 : bp_multicore_4_acc_scratchpad_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_4_acc_scratchpad_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_cid_width           
                 : bp_multicore_4_acc_scratchpad_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_4_acc_scratchpad_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_len_width           
                 : bp_multicore_4_acc_scratchpad_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_4_acc_scratchpad_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_mem_clk           
                 : bp_multicore_4_acc_scratchpad_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_4_acc_scratchpad_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_max_credits           
                 : bp_multicore_4_acc_scratchpad_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_4_acc_scratchpad_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_flit_width           
                 : bp_multicore_4_acc_scratchpad_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_4_acc_scratchpad_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_cid_width           
                 : bp_multicore_4_acc_scratchpad_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_4_acc_scratchpad_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_len_width           
                 : bp_multicore_4_acc_scratchpad_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_4_acc_scratchpad_override_p.async_io_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_io_clk           
                 : bp_multicore_4_acc_scratchpad_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_4_acc_scratchpad_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_max_credits           
                 : bp_multicore_4_acc_scratchpad_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_4_acc_scratchpad_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_flit_width           
                 : bp_multicore_4_acc_scratchpad_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_4_acc_scratchpad_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_cid_width           
                 : bp_multicore_4_acc_scratchpad_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_4_acc_scratchpad_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_did_width           
                 : bp_multicore_4_acc_scratchpad_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_4_acc_scratchpad_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_len_width           
                 : bp_multicore_4_acc_scratchpad_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_4_acc_vdp_override_p =
 '{cac_x_dim : 1
   ,sac_x_dim: 1
   ,cacc_type: e_cacc_vdp
   ,sacc_type: e_sacc_vdp
   ,num_lce  : 10
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_4_acc_vdp_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_4_acc_vdp_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cc_x_dim           
                 : bp_multicore_4_acc_vdp_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_4_acc_vdp_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cc_y_dim           
                 : bp_multicore_4_acc_vdp_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_4_acc_vdp_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.ic_y_dim           
                 : bp_multicore_4_acc_vdp_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_4_acc_vdp_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.mc_y_dim           
                 : bp_multicore_4_acc_vdp_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_4_acc_vdp_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cac_x_dim           
                 : bp_multicore_4_acc_vdp_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_4_acc_vdp_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.sac_x_dim           
                 : bp_multicore_4_acc_vdp_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_4_acc_vdp_override_p.cacc_type == "inv") 
                 ? bp_multicore_4_cfg_p.cacc_type           
                 : bp_multicore_4_acc_vdp_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_4_acc_vdp_override_p.sacc_type == "inv") 
                 ? bp_multicore_4_cfg_p.sacc_type           
                 : bp_multicore_4_acc_vdp_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_4_acc_vdp_override_p.num_cce == "inv") 
                 ? bp_multicore_4_cfg_p.num_cce           
                 : bp_multicore_4_acc_vdp_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_4_acc_vdp_override_p.num_lce == "inv") 
                 ? bp_multicore_4_cfg_p.num_lce           
                 : bp_multicore_4_acc_vdp_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_4_acc_vdp_override_p.vaddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.vaddr_width           
                 : bp_multicore_4_acc_vdp_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_4_acc_vdp_override_p.paddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.paddr_width           
                 : bp_multicore_4_acc_vdp_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_4_acc_vdp_override_p.daddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.daddr_width           
                 : bp_multicore_4_acc_vdp_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_4_acc_vdp_override_p.caddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.caddr_width           
                 : bp_multicore_4_acc_vdp_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_4_acc_vdp_override_p.asid_width == "inv") 
                 ? bp_multicore_4_cfg_p.asid_width           
                 : bp_multicore_4_acc_vdp_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_4_acc_vdp_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_4_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_4_acc_vdp_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_4_acc_vdp_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_4_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_4_acc_vdp_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_4_acc_vdp_override_p.muldiv_support == "inv") 
                 ? bp_multicore_4_cfg_p.muldiv_support           
                 : bp_multicore_4_acc_vdp_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_4_acc_vdp_override_p.fpu_support == "inv") 
                 ? bp_multicore_4_cfg_p.fpu_support           
                 : bp_multicore_4_acc_vdp_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_4_acc_vdp_override_p.compressed_support == "inv") 
                 ? bp_multicore_4_cfg_p.compressed_support           
                 : bp_multicore_4_acc_vdp_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_4_acc_vdp_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_4_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_4_acc_vdp_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_4_acc_vdp_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_4_cfg_p.btb_tag_width           
                 : bp_multicore_4_acc_vdp_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_4_acc_vdp_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_4_cfg_p.btb_idx_width           
                 : bp_multicore_4_acc_vdp_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_4_acc_vdp_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_4_cfg_p.bht_idx_width           
                 : bp_multicore_4_acc_vdp_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_4_acc_vdp_override_p.bht_row_els == "inv") 
                 ? bp_multicore_4_cfg_p.bht_row_els           
                 : bp_multicore_4_acc_vdp_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_4_acc_vdp_override_p.ghist_width == "inv") 
                 ? bp_multicore_4_cfg_p.ghist_width           
                 : bp_multicore_4_acc_vdp_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_4_acc_vdp_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_4_cfg_p.itlb_els_4k           
                 : bp_multicore_4_acc_vdp_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_4_acc_vdp_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_4_cfg_p.itlb_els_1g           
                 : bp_multicore_4_acc_vdp_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_4_acc_vdp_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_4_cfg_p.dtlb_els_4k           
                 : bp_multicore_4_acc_vdp_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_4_acc_vdp_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_4_cfg_p.dtlb_els_1g           
                 : bp_multicore_4_acc_vdp_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_4_acc_vdp_override_p.icache_features == "inv") 
                 ? bp_multicore_4_cfg_p.icache_features           
                 : bp_multicore_4_acc_vdp_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_4_acc_vdp_override_p.icache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.icache_sets           
                 : bp_multicore_4_acc_vdp_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_4_acc_vdp_override_p.icache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.icache_assoc           
                 : bp_multicore_4_acc_vdp_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_4_acc_vdp_override_p.icache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.icache_block_width           
                 : bp_multicore_4_acc_vdp_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_4_acc_vdp_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.icache_fill_width           
                 : bp_multicore_4_acc_vdp_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_4_acc_vdp_override_p.dcache_features == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_features           
                 : bp_multicore_4_acc_vdp_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_4_acc_vdp_override_p.dcache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_sets           
                 : bp_multicore_4_acc_vdp_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_4_acc_vdp_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_assoc           
                 : bp_multicore_4_acc_vdp_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_4_acc_vdp_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_block_width           
                 : bp_multicore_4_acc_vdp_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_4_acc_vdp_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_fill_width           
                 : bp_multicore_4_acc_vdp_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_4_acc_vdp_override_p.acache_features == "inv") 
                 ? bp_multicore_4_cfg_p.acache_features           
                 : bp_multicore_4_acc_vdp_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_4_acc_vdp_override_p.acache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.acache_sets           
                 : bp_multicore_4_acc_vdp_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_4_acc_vdp_override_p.acache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.acache_assoc           
                 : bp_multicore_4_acc_vdp_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_4_acc_vdp_override_p.acache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.acache_block_width           
                 : bp_multicore_4_acc_vdp_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_4_acc_vdp_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.acache_fill_width           
                 : bp_multicore_4_acc_vdp_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_4_acc_vdp_override_p.cce_type == "inv") 
                 ? bp_multicore_4_cfg_p.cce_type           
                 : bp_multicore_4_acc_vdp_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_4_acc_vdp_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_4_cfg_p.cce_pc_width           
                 : bp_multicore_4_acc_vdp_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_4_acc_vdp_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_4_cfg_p.bedrock_data_width           
                 : bp_multicore_4_acc_vdp_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_4_acc_vdp_override_p.l2_features == "inv") 
                 ? bp_multicore_4_cfg_p.l2_features           
                 : bp_multicore_4_acc_vdp_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_4_acc_vdp_override_p.l2_banks == "inv") 
                 ? bp_multicore_4_cfg_p.l2_banks           
                 : bp_multicore_4_acc_vdp_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_4_acc_vdp_override_p.l2_data_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_data_width           
                 : bp_multicore_4_acc_vdp_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_4_acc_vdp_override_p.l2_sets == "inv") 
                 ? bp_multicore_4_cfg_p.l2_sets           
                 : bp_multicore_4_acc_vdp_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_4_acc_vdp_override_p.l2_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.l2_assoc           
                 : bp_multicore_4_acc_vdp_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_4_acc_vdp_override_p.l2_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_block_width           
                 : bp_multicore_4_acc_vdp_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_4_acc_vdp_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_fill_width           
                 : bp_multicore_4_acc_vdp_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_4_acc_vdp_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_4_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_4_acc_vdp_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_4_acc_vdp_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_coh_clk           
                 : bp_multicore_4_acc_vdp_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_4_acc_vdp_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_max_credits           
                 : bp_multicore_4_acc_vdp_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_4_acc_vdp_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_flit_width           
                 : bp_multicore_4_acc_vdp_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_4_acc_vdp_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_cid_width           
                 : bp_multicore_4_acc_vdp_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_4_acc_vdp_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_len_width           
                 : bp_multicore_4_acc_vdp_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_4_acc_vdp_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_mem_clk           
                 : bp_multicore_4_acc_vdp_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_4_acc_vdp_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_max_credits           
                 : bp_multicore_4_acc_vdp_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_4_acc_vdp_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_flit_width           
                 : bp_multicore_4_acc_vdp_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_4_acc_vdp_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_cid_width           
                 : bp_multicore_4_acc_vdp_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_4_acc_vdp_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_len_width           
                 : bp_multicore_4_acc_vdp_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_4_acc_vdp_override_p.async_io_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_io_clk           
                 : bp_multicore_4_acc_vdp_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_4_acc_vdp_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_max_credits           
                 : bp_multicore_4_acc_vdp_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_4_acc_vdp_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_flit_width           
                 : bp_multicore_4_acc_vdp_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_4_acc_vdp_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_cid_width           
                 : bp_multicore_4_acc_vdp_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_4_acc_vdp_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_did_width           
                 : bp_multicore_4_acc_vdp_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_4_acc_vdp_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_len_width           
                 : bp_multicore_4_acc_vdp_override_p.io_noc_len_width          
     
       }
;


localparam bp_proc_param_s bp_multicore_1_cce_ucode_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_1_cce_ucode_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_1_cce_ucode_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_x_dim           
                 : bp_multicore_1_cce_ucode_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_1_cce_ucode_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cc_y_dim           
                 : bp_multicore_1_cce_ucode_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_1_cce_ucode_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.ic_y_dim           
                 : bp_multicore_1_cce_ucode_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_1_cce_ucode_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_cfg_p.mc_y_dim           
                 : bp_multicore_1_cce_ucode_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_1_cce_ucode_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.cac_x_dim           
                 : bp_multicore_1_cce_ucode_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_1_cce_ucode_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_cfg_p.sac_x_dim           
                 : bp_multicore_1_cce_ucode_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_1_cce_ucode_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.cacc_type           
                 : bp_multicore_1_cce_ucode_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_1_cce_ucode_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_cfg_p.sacc_type           
                 : bp_multicore_1_cce_ucode_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_1_cce_ucode_override_p.num_cce == "inv") 
                 ? bp_multicore_1_cfg_p.num_cce           
                 : bp_multicore_1_cce_ucode_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_1_cce_ucode_override_p.num_lce == "inv") 
                 ? bp_multicore_1_cfg_p.num_lce           
                 : bp_multicore_1_cce_ucode_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_1_cce_ucode_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.vaddr_width           
                 : bp_multicore_1_cce_ucode_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_1_cce_ucode_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.paddr_width           
                 : bp_multicore_1_cce_ucode_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_1_cce_ucode_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.daddr_width           
                 : bp_multicore_1_cce_ucode_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_1_cce_ucode_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_cfg_p.caddr_width           
                 : bp_multicore_1_cce_ucode_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_1_cce_ucode_override_p.asid_width == "inv") 
                 ? bp_multicore_1_cfg_p.asid_width           
                 : bp_multicore_1_cce_ucode_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_1_cce_ucode_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_1_cce_ucode_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_1_cce_ucode_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_1_cce_ucode_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_1_cce_ucode_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_cfg_p.muldiv_support           
                 : bp_multicore_1_cce_ucode_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_1_cce_ucode_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_cfg_p.fpu_support           
                 : bp_multicore_1_cce_ucode_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_1_cce_ucode_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_cfg_p.compressed_support           
                 : bp_multicore_1_cce_ucode_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_1_cce_ucode_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_1_cce_ucode_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_1_cce_ucode_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_tag_width           
                 : bp_multicore_1_cce_ucode_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_1_cce_ucode_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.btb_idx_width           
                 : bp_multicore_1_cce_ucode_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_1_cce_ucode_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_cfg_p.bht_idx_width           
                 : bp_multicore_1_cce_ucode_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_1_cce_ucode_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_cfg_p.bht_row_els           
                 : bp_multicore_1_cce_ucode_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_1_cce_ucode_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_cfg_p.ghist_width           
                 : bp_multicore_1_cce_ucode_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_1_cce_ucode_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_4k           
                 : bp_multicore_1_cce_ucode_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_1_cce_ucode_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.itlb_els_1g           
                 : bp_multicore_1_cce_ucode_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_1_cce_ucode_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_4k           
                 : bp_multicore_1_cce_ucode_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_1_cce_ucode_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_cfg_p.dtlb_els_1g           
                 : bp_multicore_1_cce_ucode_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_1_cce_ucode_override_p.icache_features == "inv") 
                 ? bp_multicore_1_cfg_p.icache_features           
                 : bp_multicore_1_cce_ucode_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_1_cce_ucode_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.icache_sets           
                 : bp_multicore_1_cce_ucode_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_1_cce_ucode_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.icache_assoc           
                 : bp_multicore_1_cce_ucode_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_1_cce_ucode_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_block_width           
                 : bp_multicore_1_cce_ucode_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_1_cce_ucode_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.icache_fill_width           
                 : bp_multicore_1_cce_ucode_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_1_cce_ucode_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_features           
                 : bp_multicore_1_cce_ucode_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_1_cce_ucode_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_sets           
                 : bp_multicore_1_cce_ucode_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_1_cce_ucode_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_assoc           
                 : bp_multicore_1_cce_ucode_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_1_cce_ucode_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_block_width           
                 : bp_multicore_1_cce_ucode_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_1_cce_ucode_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.dcache_fill_width           
                 : bp_multicore_1_cce_ucode_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_1_cce_ucode_override_p.acache_features == "inv") 
                 ? bp_multicore_1_cfg_p.acache_features           
                 : bp_multicore_1_cce_ucode_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_1_cce_ucode_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_cfg_p.acache_sets           
                 : bp_multicore_1_cce_ucode_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_1_cce_ucode_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.acache_assoc           
                 : bp_multicore_1_cce_ucode_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_1_cce_ucode_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_block_width           
                 : bp_multicore_1_cce_ucode_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_1_cce_ucode_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.acache_fill_width           
                 : bp_multicore_1_cce_ucode_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_1_cce_ucode_override_p.cce_type == "inv") 
                 ? bp_multicore_1_cfg_p.cce_type           
                 : bp_multicore_1_cce_ucode_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_1_cce_ucode_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_cfg_p.cce_pc_width           
                 : bp_multicore_1_cce_ucode_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_1_cce_ucode_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.bedrock_data_width           
                 : bp_multicore_1_cce_ucode_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_1_cce_ucode_override_p.l2_features == "inv") 
                 ? bp_multicore_1_cfg_p.l2_features           
                 : bp_multicore_1_cce_ucode_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_1_cce_ucode_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_cfg_p.l2_banks           
                 : bp_multicore_1_cce_ucode_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_1_cce_ucode_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_data_width           
                 : bp_multicore_1_cce_ucode_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_1_cce_ucode_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_cfg_p.l2_sets           
                 : bp_multicore_1_cce_ucode_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_1_cce_ucode_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_cfg_p.l2_assoc           
                 : bp_multicore_1_cce_ucode_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_1_cce_ucode_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_block_width           
                 : bp_multicore_1_cce_ucode_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_1_cce_ucode_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_cfg_p.l2_fill_width           
                 : bp_multicore_1_cce_ucode_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_1_cce_ucode_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_1_cce_ucode_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_1_cce_ucode_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_coh_clk           
                 : bp_multicore_1_cce_ucode_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_1_cce_ucode_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_max_credits           
                 : bp_multicore_1_cce_ucode_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_1_cce_ucode_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_flit_width           
                 : bp_multicore_1_cce_ucode_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_1_cce_ucode_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_cid_width           
                 : bp_multicore_1_cce_ucode_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_1_cce_ucode_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.coh_noc_len_width           
                 : bp_multicore_1_cce_ucode_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_1_cce_ucode_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_mem_clk           
                 : bp_multicore_1_cce_ucode_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_1_cce_ucode_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_max_credits           
                 : bp_multicore_1_cce_ucode_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_1_cce_ucode_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_flit_width           
                 : bp_multicore_1_cce_ucode_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_1_cce_ucode_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_cid_width           
                 : bp_multicore_1_cce_ucode_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_1_cce_ucode_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.mem_noc_len_width           
                 : bp_multicore_1_cce_ucode_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_1_cce_ucode_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_cfg_p.async_io_clk           
                 : bp_multicore_1_cce_ucode_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_1_cce_ucode_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_max_credits           
                 : bp_multicore_1_cce_ucode_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_1_cce_ucode_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_flit_width           
                 : bp_multicore_1_cce_ucode_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_1_cce_ucode_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_cid_width           
                 : bp_multicore_1_cce_ucode_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_1_cce_ucode_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_did_width           
                 : bp_multicore_1_cce_ucode_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_1_cce_ucode_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_cfg_p.io_noc_len_width           
                 : bp_multicore_1_cce_ucode_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_1_cce_ucode_megaparrot_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_1_cce_ucode_megaparrot_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_1_cce_ucode_megaparrot_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.cc_x_dim           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_1_cce_ucode_megaparrot_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.cc_y_dim           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_1_cce_ucode_megaparrot_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.ic_y_dim           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_1_cce_ucode_megaparrot_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.mc_y_dim           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_1_cce_ucode_megaparrot_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.cac_x_dim           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_1_cce_ucode_megaparrot_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.sac_x_dim           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_1_cce_ucode_megaparrot_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.cacc_type           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_1_cce_ucode_megaparrot_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.sacc_type           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_1_cce_ucode_megaparrot_override_p.num_cce == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.num_cce           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_1_cce_ucode_megaparrot_override_p.num_lce == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.num_lce           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.vaddr_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.paddr_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.daddr_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.caddr_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.asid_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.asid_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_1_cce_ucode_megaparrot_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_1_cce_ucode_megaparrot_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_1_cce_ucode_megaparrot_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.muldiv_support           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_1_cce_ucode_megaparrot_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.fpu_support           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_1_cce_ucode_megaparrot_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.compressed_support           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.btb_tag_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.btb_idx_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.bht_idx_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_1_cce_ucode_megaparrot_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.bht_row_els           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.ghist_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_1_cce_ucode_megaparrot_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.itlb_els_4k           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_1_cce_ucode_megaparrot_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.itlb_els_1g           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_1_cce_ucode_megaparrot_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.dtlb_els_4k           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_1_cce_ucode_megaparrot_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.dtlb_els_1g           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_1_cce_ucode_megaparrot_override_p.icache_features == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.icache_features           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_1_cce_ucode_megaparrot_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.icache_sets           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_1_cce_ucode_megaparrot_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.icache_assoc           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.icache_block_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.icache_fill_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.dcache_features           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.dcache_sets           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.dcache_assoc           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.dcache_block_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.dcache_fill_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_1_cce_ucode_megaparrot_override_p.acache_features == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.acache_features           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_1_cce_ucode_megaparrot_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.acache_sets           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_1_cce_ucode_megaparrot_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.acache_assoc           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.acache_block_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.acache_fill_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_1_cce_ucode_megaparrot_override_p.cce_type == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.cce_type           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.cce_pc_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.bedrock_data_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_1_cce_ucode_megaparrot_override_p.l2_features == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.l2_features           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_1_cce_ucode_megaparrot_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.l2_banks           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.l2_data_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_1_cce_ucode_megaparrot_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.l2_sets           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_1_cce_ucode_megaparrot_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.l2_assoc           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.l2_block_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.l2_fill_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_1_cce_ucode_megaparrot_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_1_cce_ucode_megaparrot_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.async_coh_clk           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_1_cce_ucode_megaparrot_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.coh_noc_max_credits           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.coh_noc_flit_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.coh_noc_cid_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.coh_noc_len_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_1_cce_ucode_megaparrot_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.async_mem_clk           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_1_cce_ucode_megaparrot_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.mem_noc_max_credits           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.mem_noc_flit_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.mem_noc_cid_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.mem_noc_len_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_1_cce_ucode_megaparrot_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.async_io_clk           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.io_noc_max_credits           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.io_noc_flit_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.io_noc_cid_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.io_noc_did_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_megaparrot_cfg_p.io_noc_len_width           
                 : bp_multicore_1_cce_ucode_megaparrot_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_1_cce_ucode_miniparrot_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_1_cce_ucode_miniparrot_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_1_cce_ucode_miniparrot_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.cc_x_dim           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_1_cce_ucode_miniparrot_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.cc_y_dim           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_1_cce_ucode_miniparrot_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.ic_y_dim           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_1_cce_ucode_miniparrot_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.mc_y_dim           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_1_cce_ucode_miniparrot_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.cac_x_dim           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_1_cce_ucode_miniparrot_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.sac_x_dim           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_1_cce_ucode_miniparrot_override_p.cacc_type == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.cacc_type           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_1_cce_ucode_miniparrot_override_p.sacc_type == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.sacc_type           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_1_cce_ucode_miniparrot_override_p.num_cce == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.num_cce           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_1_cce_ucode_miniparrot_override_p.num_lce == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.num_lce           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.vaddr_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.vaddr_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.paddr_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.paddr_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.daddr_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.daddr_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.caddr_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.caddr_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.asid_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.asid_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_1_cce_ucode_miniparrot_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_1_cce_ucode_miniparrot_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_1_cce_ucode_miniparrot_override_p.muldiv_support == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.muldiv_support           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_1_cce_ucode_miniparrot_override_p.fpu_support == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.fpu_support           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_1_cce_ucode_miniparrot_override_p.compressed_support == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.compressed_support           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.btb_tag_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.btb_idx_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.bht_idx_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_1_cce_ucode_miniparrot_override_p.bht_row_els == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.bht_row_els           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.ghist_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.ghist_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_1_cce_ucode_miniparrot_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.itlb_els_4k           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_1_cce_ucode_miniparrot_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.itlb_els_1g           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_1_cce_ucode_miniparrot_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.dtlb_els_4k           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_1_cce_ucode_miniparrot_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.dtlb_els_1g           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_1_cce_ucode_miniparrot_override_p.icache_features == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.icache_features           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_1_cce_ucode_miniparrot_override_p.icache_sets == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.icache_sets           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_1_cce_ucode_miniparrot_override_p.icache_assoc == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.icache_assoc           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.icache_block_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.icache_block_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.icache_fill_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_features == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.dcache_features           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_sets == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.dcache_sets           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.dcache_assoc           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.dcache_block_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.dcache_fill_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_1_cce_ucode_miniparrot_override_p.acache_features == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.acache_features           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_1_cce_ucode_miniparrot_override_p.acache_sets == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.acache_sets           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_1_cce_ucode_miniparrot_override_p.acache_assoc == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.acache_assoc           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.acache_block_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.acache_block_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.acache_fill_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_1_cce_ucode_miniparrot_override_p.cce_type == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.cce_type           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.cce_pc_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.bedrock_data_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_1_cce_ucode_miniparrot_override_p.l2_features == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.l2_features           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_1_cce_ucode_miniparrot_override_p.l2_banks == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.l2_banks           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.l2_data_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.l2_data_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_1_cce_ucode_miniparrot_override_p.l2_sets == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.l2_sets           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_1_cce_ucode_miniparrot_override_p.l2_assoc == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.l2_assoc           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.l2_block_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.l2_block_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.l2_fill_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_1_cce_ucode_miniparrot_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_1_cce_ucode_miniparrot_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.async_coh_clk           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_1_cce_ucode_miniparrot_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.coh_noc_max_credits           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.coh_noc_flit_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.coh_noc_cid_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.coh_noc_len_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_1_cce_ucode_miniparrot_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.async_mem_clk           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_1_cce_ucode_miniparrot_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.mem_noc_max_credits           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.mem_noc_flit_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.mem_noc_cid_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.mem_noc_len_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_1_cce_ucode_miniparrot_override_p.async_io_clk == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.async_io_clk           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.io_noc_max_credits           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.io_noc_flit_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.io_noc_cid_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.io_noc_did_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_1_miniparrot_cfg_p.io_noc_len_width           
                 : bp_multicore_1_cce_ucode_miniparrot_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_2_cce_ucode_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_2_cce_ucode_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_2_cce_ucode_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_2_cfg_p.cc_x_dim           
                 : bp_multicore_2_cce_ucode_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_2_cce_ucode_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_2_cfg_p.cc_y_dim           
                 : bp_multicore_2_cce_ucode_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_2_cce_ucode_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_2_cfg_p.ic_y_dim           
                 : bp_multicore_2_cce_ucode_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_2_cce_ucode_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_2_cfg_p.mc_y_dim           
                 : bp_multicore_2_cce_ucode_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_2_cce_ucode_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_2_cfg_p.cac_x_dim           
                 : bp_multicore_2_cce_ucode_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_2_cce_ucode_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_2_cfg_p.sac_x_dim           
                 : bp_multicore_2_cce_ucode_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_2_cce_ucode_override_p.cacc_type == "inv") 
                 ? bp_multicore_2_cfg_p.cacc_type           
                 : bp_multicore_2_cce_ucode_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_2_cce_ucode_override_p.sacc_type == "inv") 
                 ? bp_multicore_2_cfg_p.sacc_type           
                 : bp_multicore_2_cce_ucode_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_2_cce_ucode_override_p.num_cce == "inv") 
                 ? bp_multicore_2_cfg_p.num_cce           
                 : bp_multicore_2_cce_ucode_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_2_cce_ucode_override_p.num_lce == "inv") 
                 ? bp_multicore_2_cfg_p.num_lce           
                 : bp_multicore_2_cce_ucode_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_2_cce_ucode_override_p.vaddr_width == "inv") 
                 ? bp_multicore_2_cfg_p.vaddr_width           
                 : bp_multicore_2_cce_ucode_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_2_cce_ucode_override_p.paddr_width == "inv") 
                 ? bp_multicore_2_cfg_p.paddr_width           
                 : bp_multicore_2_cce_ucode_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_2_cce_ucode_override_p.daddr_width == "inv") 
                 ? bp_multicore_2_cfg_p.daddr_width           
                 : bp_multicore_2_cce_ucode_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_2_cce_ucode_override_p.caddr_width == "inv") 
                 ? bp_multicore_2_cfg_p.caddr_width           
                 : bp_multicore_2_cce_ucode_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_2_cce_ucode_override_p.asid_width == "inv") 
                 ? bp_multicore_2_cfg_p.asid_width           
                 : bp_multicore_2_cce_ucode_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_2_cce_ucode_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_2_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_2_cce_ucode_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_2_cce_ucode_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_2_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_2_cce_ucode_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_2_cce_ucode_override_p.muldiv_support == "inv") 
                 ? bp_multicore_2_cfg_p.muldiv_support           
                 : bp_multicore_2_cce_ucode_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_2_cce_ucode_override_p.fpu_support == "inv") 
                 ? bp_multicore_2_cfg_p.fpu_support           
                 : bp_multicore_2_cce_ucode_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_2_cce_ucode_override_p.compressed_support == "inv") 
                 ? bp_multicore_2_cfg_p.compressed_support           
                 : bp_multicore_2_cce_ucode_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_2_cce_ucode_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_2_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_2_cce_ucode_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_2_cce_ucode_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_2_cfg_p.btb_tag_width           
                 : bp_multicore_2_cce_ucode_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_2_cce_ucode_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_2_cfg_p.btb_idx_width           
                 : bp_multicore_2_cce_ucode_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_2_cce_ucode_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_2_cfg_p.bht_idx_width           
                 : bp_multicore_2_cce_ucode_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_2_cce_ucode_override_p.bht_row_els == "inv") 
                 ? bp_multicore_2_cfg_p.bht_row_els           
                 : bp_multicore_2_cce_ucode_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_2_cce_ucode_override_p.ghist_width == "inv") 
                 ? bp_multicore_2_cfg_p.ghist_width           
                 : bp_multicore_2_cce_ucode_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_2_cce_ucode_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_2_cfg_p.itlb_els_4k           
                 : bp_multicore_2_cce_ucode_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_2_cce_ucode_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_2_cfg_p.itlb_els_1g           
                 : bp_multicore_2_cce_ucode_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_2_cce_ucode_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_2_cfg_p.dtlb_els_4k           
                 : bp_multicore_2_cce_ucode_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_2_cce_ucode_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_2_cfg_p.dtlb_els_1g           
                 : bp_multicore_2_cce_ucode_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_2_cce_ucode_override_p.icache_features == "inv") 
                 ? bp_multicore_2_cfg_p.icache_features           
                 : bp_multicore_2_cce_ucode_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_2_cce_ucode_override_p.icache_sets == "inv") 
                 ? bp_multicore_2_cfg_p.icache_sets           
                 : bp_multicore_2_cce_ucode_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_2_cce_ucode_override_p.icache_assoc == "inv") 
                 ? bp_multicore_2_cfg_p.icache_assoc           
                 : bp_multicore_2_cce_ucode_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_2_cce_ucode_override_p.icache_block_width == "inv") 
                 ? bp_multicore_2_cfg_p.icache_block_width           
                 : bp_multicore_2_cce_ucode_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_2_cce_ucode_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_2_cfg_p.icache_fill_width           
                 : bp_multicore_2_cce_ucode_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_2_cce_ucode_override_p.dcache_features == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_features           
                 : bp_multicore_2_cce_ucode_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_2_cce_ucode_override_p.dcache_sets == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_sets           
                 : bp_multicore_2_cce_ucode_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_2_cce_ucode_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_assoc           
                 : bp_multicore_2_cce_ucode_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_2_cce_ucode_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_block_width           
                 : bp_multicore_2_cce_ucode_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_2_cce_ucode_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_2_cfg_p.dcache_fill_width           
                 : bp_multicore_2_cce_ucode_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_2_cce_ucode_override_p.acache_features == "inv") 
                 ? bp_multicore_2_cfg_p.acache_features           
                 : bp_multicore_2_cce_ucode_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_2_cce_ucode_override_p.acache_sets == "inv") 
                 ? bp_multicore_2_cfg_p.acache_sets           
                 : bp_multicore_2_cce_ucode_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_2_cce_ucode_override_p.acache_assoc == "inv") 
                 ? bp_multicore_2_cfg_p.acache_assoc           
                 : bp_multicore_2_cce_ucode_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_2_cce_ucode_override_p.acache_block_width == "inv") 
                 ? bp_multicore_2_cfg_p.acache_block_width           
                 : bp_multicore_2_cce_ucode_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_2_cce_ucode_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_2_cfg_p.acache_fill_width           
                 : bp_multicore_2_cce_ucode_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_2_cce_ucode_override_p.cce_type == "inv") 
                 ? bp_multicore_2_cfg_p.cce_type           
                 : bp_multicore_2_cce_ucode_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_2_cce_ucode_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_2_cfg_p.cce_pc_width           
                 : bp_multicore_2_cce_ucode_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_2_cce_ucode_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_2_cfg_p.bedrock_data_width           
                 : bp_multicore_2_cce_ucode_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_2_cce_ucode_override_p.l2_features == "inv") 
                 ? bp_multicore_2_cfg_p.l2_features           
                 : bp_multicore_2_cce_ucode_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_2_cce_ucode_override_p.l2_banks == "inv") 
                 ? bp_multicore_2_cfg_p.l2_banks           
                 : bp_multicore_2_cce_ucode_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_2_cce_ucode_override_p.l2_data_width == "inv") 
                 ? bp_multicore_2_cfg_p.l2_data_width           
                 : bp_multicore_2_cce_ucode_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_2_cce_ucode_override_p.l2_sets == "inv") 
                 ? bp_multicore_2_cfg_p.l2_sets           
                 : bp_multicore_2_cce_ucode_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_2_cce_ucode_override_p.l2_assoc == "inv") 
                 ? bp_multicore_2_cfg_p.l2_assoc           
                 : bp_multicore_2_cce_ucode_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_2_cce_ucode_override_p.l2_block_width == "inv") 
                 ? bp_multicore_2_cfg_p.l2_block_width           
                 : bp_multicore_2_cce_ucode_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_2_cce_ucode_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_2_cfg_p.l2_fill_width           
                 : bp_multicore_2_cce_ucode_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_2_cce_ucode_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_2_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_2_cce_ucode_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_2_cce_ucode_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_2_cfg_p.async_coh_clk           
                 : bp_multicore_2_cce_ucode_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_2_cce_ucode_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_2_cfg_p.coh_noc_max_credits           
                 : bp_multicore_2_cce_ucode_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_2_cce_ucode_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_2_cfg_p.coh_noc_flit_width           
                 : bp_multicore_2_cce_ucode_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_2_cce_ucode_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_2_cfg_p.coh_noc_cid_width           
                 : bp_multicore_2_cce_ucode_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_2_cce_ucode_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_2_cfg_p.coh_noc_len_width           
                 : bp_multicore_2_cce_ucode_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_2_cce_ucode_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_2_cfg_p.async_mem_clk           
                 : bp_multicore_2_cce_ucode_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_2_cce_ucode_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_2_cfg_p.mem_noc_max_credits           
                 : bp_multicore_2_cce_ucode_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_2_cce_ucode_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_2_cfg_p.mem_noc_flit_width           
                 : bp_multicore_2_cce_ucode_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_2_cce_ucode_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_2_cfg_p.mem_noc_cid_width           
                 : bp_multicore_2_cce_ucode_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_2_cce_ucode_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_2_cfg_p.mem_noc_len_width           
                 : bp_multicore_2_cce_ucode_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_2_cce_ucode_override_p.async_io_clk == "inv") 
                 ? bp_multicore_2_cfg_p.async_io_clk           
                 : bp_multicore_2_cce_ucode_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_2_cce_ucode_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_max_credits           
                 : bp_multicore_2_cce_ucode_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_2_cce_ucode_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_flit_width           
                 : bp_multicore_2_cce_ucode_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_2_cce_ucode_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_cid_width           
                 : bp_multicore_2_cce_ucode_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_2_cce_ucode_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_did_width           
                 : bp_multicore_2_cce_ucode_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_2_cce_ucode_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_2_cfg_p.io_noc_len_width           
                 : bp_multicore_2_cce_ucode_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_3_cce_ucode_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_3_cce_ucode_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_3_cce_ucode_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_3_cfg_p.cc_x_dim           
                 : bp_multicore_3_cce_ucode_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_3_cce_ucode_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_3_cfg_p.cc_y_dim           
                 : bp_multicore_3_cce_ucode_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_3_cce_ucode_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_3_cfg_p.ic_y_dim           
                 : bp_multicore_3_cce_ucode_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_3_cce_ucode_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_3_cfg_p.mc_y_dim           
                 : bp_multicore_3_cce_ucode_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_3_cce_ucode_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_3_cfg_p.cac_x_dim           
                 : bp_multicore_3_cce_ucode_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_3_cce_ucode_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_3_cfg_p.sac_x_dim           
                 : bp_multicore_3_cce_ucode_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_3_cce_ucode_override_p.cacc_type == "inv") 
                 ? bp_multicore_3_cfg_p.cacc_type           
                 : bp_multicore_3_cce_ucode_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_3_cce_ucode_override_p.sacc_type == "inv") 
                 ? bp_multicore_3_cfg_p.sacc_type           
                 : bp_multicore_3_cce_ucode_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_3_cce_ucode_override_p.num_cce == "inv") 
                 ? bp_multicore_3_cfg_p.num_cce           
                 : bp_multicore_3_cce_ucode_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_3_cce_ucode_override_p.num_lce == "inv") 
                 ? bp_multicore_3_cfg_p.num_lce           
                 : bp_multicore_3_cce_ucode_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_3_cce_ucode_override_p.vaddr_width == "inv") 
                 ? bp_multicore_3_cfg_p.vaddr_width           
                 : bp_multicore_3_cce_ucode_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_3_cce_ucode_override_p.paddr_width == "inv") 
                 ? bp_multicore_3_cfg_p.paddr_width           
                 : bp_multicore_3_cce_ucode_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_3_cce_ucode_override_p.daddr_width == "inv") 
                 ? bp_multicore_3_cfg_p.daddr_width           
                 : bp_multicore_3_cce_ucode_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_3_cce_ucode_override_p.caddr_width == "inv") 
                 ? bp_multicore_3_cfg_p.caddr_width           
                 : bp_multicore_3_cce_ucode_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_3_cce_ucode_override_p.asid_width == "inv") 
                 ? bp_multicore_3_cfg_p.asid_width           
                 : bp_multicore_3_cce_ucode_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_3_cce_ucode_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_3_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_3_cce_ucode_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_3_cce_ucode_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_3_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_3_cce_ucode_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_3_cce_ucode_override_p.muldiv_support == "inv") 
                 ? bp_multicore_3_cfg_p.muldiv_support           
                 : bp_multicore_3_cce_ucode_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_3_cce_ucode_override_p.fpu_support == "inv") 
                 ? bp_multicore_3_cfg_p.fpu_support           
                 : bp_multicore_3_cce_ucode_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_3_cce_ucode_override_p.compressed_support == "inv") 
                 ? bp_multicore_3_cfg_p.compressed_support           
                 : bp_multicore_3_cce_ucode_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_3_cce_ucode_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_3_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_3_cce_ucode_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_3_cce_ucode_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_3_cfg_p.btb_tag_width           
                 : bp_multicore_3_cce_ucode_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_3_cce_ucode_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_3_cfg_p.btb_idx_width           
                 : bp_multicore_3_cce_ucode_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_3_cce_ucode_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_3_cfg_p.bht_idx_width           
                 : bp_multicore_3_cce_ucode_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_3_cce_ucode_override_p.bht_row_els == "inv") 
                 ? bp_multicore_3_cfg_p.bht_row_els           
                 : bp_multicore_3_cce_ucode_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_3_cce_ucode_override_p.ghist_width == "inv") 
                 ? bp_multicore_3_cfg_p.ghist_width           
                 : bp_multicore_3_cce_ucode_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_3_cce_ucode_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_3_cfg_p.itlb_els_4k           
                 : bp_multicore_3_cce_ucode_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_3_cce_ucode_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_3_cfg_p.itlb_els_1g           
                 : bp_multicore_3_cce_ucode_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_3_cce_ucode_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_3_cfg_p.dtlb_els_4k           
                 : bp_multicore_3_cce_ucode_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_3_cce_ucode_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_3_cfg_p.dtlb_els_1g           
                 : bp_multicore_3_cce_ucode_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_3_cce_ucode_override_p.icache_features == "inv") 
                 ? bp_multicore_3_cfg_p.icache_features           
                 : bp_multicore_3_cce_ucode_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_3_cce_ucode_override_p.icache_sets == "inv") 
                 ? bp_multicore_3_cfg_p.icache_sets           
                 : bp_multicore_3_cce_ucode_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_3_cce_ucode_override_p.icache_assoc == "inv") 
                 ? bp_multicore_3_cfg_p.icache_assoc           
                 : bp_multicore_3_cce_ucode_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_3_cce_ucode_override_p.icache_block_width == "inv") 
                 ? bp_multicore_3_cfg_p.icache_block_width           
                 : bp_multicore_3_cce_ucode_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_3_cce_ucode_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_3_cfg_p.icache_fill_width           
                 : bp_multicore_3_cce_ucode_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_3_cce_ucode_override_p.dcache_features == "inv") 
                 ? bp_multicore_3_cfg_p.dcache_features           
                 : bp_multicore_3_cce_ucode_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_3_cce_ucode_override_p.dcache_sets == "inv") 
                 ? bp_multicore_3_cfg_p.dcache_sets           
                 : bp_multicore_3_cce_ucode_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_3_cce_ucode_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_3_cfg_p.dcache_assoc           
                 : bp_multicore_3_cce_ucode_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_3_cce_ucode_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_3_cfg_p.dcache_block_width           
                 : bp_multicore_3_cce_ucode_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_3_cce_ucode_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_3_cfg_p.dcache_fill_width           
                 : bp_multicore_3_cce_ucode_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_3_cce_ucode_override_p.acache_features == "inv") 
                 ? bp_multicore_3_cfg_p.acache_features           
                 : bp_multicore_3_cce_ucode_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_3_cce_ucode_override_p.acache_sets == "inv") 
                 ? bp_multicore_3_cfg_p.acache_sets           
                 : bp_multicore_3_cce_ucode_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_3_cce_ucode_override_p.acache_assoc == "inv") 
                 ? bp_multicore_3_cfg_p.acache_assoc           
                 : bp_multicore_3_cce_ucode_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_3_cce_ucode_override_p.acache_block_width == "inv") 
                 ? bp_multicore_3_cfg_p.acache_block_width           
                 : bp_multicore_3_cce_ucode_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_3_cce_ucode_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_3_cfg_p.acache_fill_width           
                 : bp_multicore_3_cce_ucode_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_3_cce_ucode_override_p.cce_type == "inv") 
                 ? bp_multicore_3_cfg_p.cce_type           
                 : bp_multicore_3_cce_ucode_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_3_cce_ucode_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_3_cfg_p.cce_pc_width           
                 : bp_multicore_3_cce_ucode_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_3_cce_ucode_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_3_cfg_p.bedrock_data_width           
                 : bp_multicore_3_cce_ucode_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_3_cce_ucode_override_p.l2_features == "inv") 
                 ? bp_multicore_3_cfg_p.l2_features           
                 : bp_multicore_3_cce_ucode_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_3_cce_ucode_override_p.l2_banks == "inv") 
                 ? bp_multicore_3_cfg_p.l2_banks           
                 : bp_multicore_3_cce_ucode_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_3_cce_ucode_override_p.l2_data_width == "inv") 
                 ? bp_multicore_3_cfg_p.l2_data_width           
                 : bp_multicore_3_cce_ucode_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_3_cce_ucode_override_p.l2_sets == "inv") 
                 ? bp_multicore_3_cfg_p.l2_sets           
                 : bp_multicore_3_cce_ucode_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_3_cce_ucode_override_p.l2_assoc == "inv") 
                 ? bp_multicore_3_cfg_p.l2_assoc           
                 : bp_multicore_3_cce_ucode_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_3_cce_ucode_override_p.l2_block_width == "inv") 
                 ? bp_multicore_3_cfg_p.l2_block_width           
                 : bp_multicore_3_cce_ucode_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_3_cce_ucode_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_3_cfg_p.l2_fill_width           
                 : bp_multicore_3_cce_ucode_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_3_cce_ucode_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_3_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_3_cce_ucode_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_3_cce_ucode_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_3_cfg_p.async_coh_clk           
                 : bp_multicore_3_cce_ucode_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_3_cce_ucode_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_3_cfg_p.coh_noc_max_credits           
                 : bp_multicore_3_cce_ucode_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_3_cce_ucode_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_3_cfg_p.coh_noc_flit_width           
                 : bp_multicore_3_cce_ucode_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_3_cce_ucode_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_3_cfg_p.coh_noc_cid_width           
                 : bp_multicore_3_cce_ucode_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_3_cce_ucode_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_3_cfg_p.coh_noc_len_width           
                 : bp_multicore_3_cce_ucode_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_3_cce_ucode_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_3_cfg_p.async_mem_clk           
                 : bp_multicore_3_cce_ucode_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_3_cce_ucode_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_3_cfg_p.mem_noc_max_credits           
                 : bp_multicore_3_cce_ucode_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_3_cce_ucode_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_3_cfg_p.mem_noc_flit_width           
                 : bp_multicore_3_cce_ucode_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_3_cce_ucode_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_3_cfg_p.mem_noc_cid_width           
                 : bp_multicore_3_cce_ucode_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_3_cce_ucode_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_3_cfg_p.mem_noc_len_width           
                 : bp_multicore_3_cce_ucode_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_3_cce_ucode_override_p.async_io_clk == "inv") 
                 ? bp_multicore_3_cfg_p.async_io_clk           
                 : bp_multicore_3_cce_ucode_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_3_cce_ucode_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_3_cfg_p.io_noc_max_credits           
                 : bp_multicore_3_cce_ucode_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_3_cce_ucode_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_3_cfg_p.io_noc_flit_width           
                 : bp_multicore_3_cce_ucode_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_3_cce_ucode_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_3_cfg_p.io_noc_cid_width           
                 : bp_multicore_3_cce_ucode_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_3_cce_ucode_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_3_cfg_p.io_noc_did_width           
                 : bp_multicore_3_cce_ucode_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_3_cce_ucode_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_3_cfg_p.io_noc_len_width           
                 : bp_multicore_3_cce_ucode_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_4_cce_ucode_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_4_cce_ucode_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_4_cce_ucode_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cc_x_dim           
                 : bp_multicore_4_cce_ucode_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_4_cce_ucode_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cc_y_dim           
                 : bp_multicore_4_cce_ucode_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_4_cce_ucode_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.ic_y_dim           
                 : bp_multicore_4_cce_ucode_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_4_cce_ucode_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_4_cfg_p.mc_y_dim           
                 : bp_multicore_4_cce_ucode_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_4_cce_ucode_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.cac_x_dim           
                 : bp_multicore_4_cce_ucode_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_4_cce_ucode_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_4_cfg_p.sac_x_dim           
                 : bp_multicore_4_cce_ucode_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_4_cce_ucode_override_p.cacc_type == "inv") 
                 ? bp_multicore_4_cfg_p.cacc_type           
                 : bp_multicore_4_cce_ucode_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_4_cce_ucode_override_p.sacc_type == "inv") 
                 ? bp_multicore_4_cfg_p.sacc_type           
                 : bp_multicore_4_cce_ucode_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_4_cce_ucode_override_p.num_cce == "inv") 
                 ? bp_multicore_4_cfg_p.num_cce           
                 : bp_multicore_4_cce_ucode_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_4_cce_ucode_override_p.num_lce == "inv") 
                 ? bp_multicore_4_cfg_p.num_lce           
                 : bp_multicore_4_cce_ucode_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_4_cce_ucode_override_p.vaddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.vaddr_width           
                 : bp_multicore_4_cce_ucode_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_4_cce_ucode_override_p.paddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.paddr_width           
                 : bp_multicore_4_cce_ucode_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_4_cce_ucode_override_p.daddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.daddr_width           
                 : bp_multicore_4_cce_ucode_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_4_cce_ucode_override_p.caddr_width == "inv") 
                 ? bp_multicore_4_cfg_p.caddr_width           
                 : bp_multicore_4_cce_ucode_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_4_cce_ucode_override_p.asid_width == "inv") 
                 ? bp_multicore_4_cfg_p.asid_width           
                 : bp_multicore_4_cce_ucode_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_4_cce_ucode_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_4_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_4_cce_ucode_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_4_cce_ucode_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_4_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_4_cce_ucode_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_4_cce_ucode_override_p.muldiv_support == "inv") 
                 ? bp_multicore_4_cfg_p.muldiv_support           
                 : bp_multicore_4_cce_ucode_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_4_cce_ucode_override_p.fpu_support == "inv") 
                 ? bp_multicore_4_cfg_p.fpu_support           
                 : bp_multicore_4_cce_ucode_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_4_cce_ucode_override_p.compressed_support == "inv") 
                 ? bp_multicore_4_cfg_p.compressed_support           
                 : bp_multicore_4_cce_ucode_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_4_cce_ucode_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_4_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_4_cce_ucode_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_4_cce_ucode_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_4_cfg_p.btb_tag_width           
                 : bp_multicore_4_cce_ucode_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_4_cce_ucode_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_4_cfg_p.btb_idx_width           
                 : bp_multicore_4_cce_ucode_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_4_cce_ucode_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_4_cfg_p.bht_idx_width           
                 : bp_multicore_4_cce_ucode_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_4_cce_ucode_override_p.bht_row_els == "inv") 
                 ? bp_multicore_4_cfg_p.bht_row_els           
                 : bp_multicore_4_cce_ucode_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_4_cce_ucode_override_p.ghist_width == "inv") 
                 ? bp_multicore_4_cfg_p.ghist_width           
                 : bp_multicore_4_cce_ucode_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_4_cce_ucode_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_4_cfg_p.itlb_els_4k           
                 : bp_multicore_4_cce_ucode_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_4_cce_ucode_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_4_cfg_p.itlb_els_1g           
                 : bp_multicore_4_cce_ucode_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_4_cce_ucode_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_4_cfg_p.dtlb_els_4k           
                 : bp_multicore_4_cce_ucode_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_4_cce_ucode_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_4_cfg_p.dtlb_els_1g           
                 : bp_multicore_4_cce_ucode_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_4_cce_ucode_override_p.icache_features == "inv") 
                 ? bp_multicore_4_cfg_p.icache_features           
                 : bp_multicore_4_cce_ucode_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_4_cce_ucode_override_p.icache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.icache_sets           
                 : bp_multicore_4_cce_ucode_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_4_cce_ucode_override_p.icache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.icache_assoc           
                 : bp_multicore_4_cce_ucode_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_4_cce_ucode_override_p.icache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.icache_block_width           
                 : bp_multicore_4_cce_ucode_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_4_cce_ucode_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.icache_fill_width           
                 : bp_multicore_4_cce_ucode_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_4_cce_ucode_override_p.dcache_features == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_features           
                 : bp_multicore_4_cce_ucode_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_4_cce_ucode_override_p.dcache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_sets           
                 : bp_multicore_4_cce_ucode_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_4_cce_ucode_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_assoc           
                 : bp_multicore_4_cce_ucode_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_4_cce_ucode_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_block_width           
                 : bp_multicore_4_cce_ucode_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_4_cce_ucode_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.dcache_fill_width           
                 : bp_multicore_4_cce_ucode_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_4_cce_ucode_override_p.acache_features == "inv") 
                 ? bp_multicore_4_cfg_p.acache_features           
                 : bp_multicore_4_cce_ucode_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_4_cce_ucode_override_p.acache_sets == "inv") 
                 ? bp_multicore_4_cfg_p.acache_sets           
                 : bp_multicore_4_cce_ucode_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_4_cce_ucode_override_p.acache_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.acache_assoc           
                 : bp_multicore_4_cce_ucode_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_4_cce_ucode_override_p.acache_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.acache_block_width           
                 : bp_multicore_4_cce_ucode_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_4_cce_ucode_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.acache_fill_width           
                 : bp_multicore_4_cce_ucode_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_4_cce_ucode_override_p.cce_type == "inv") 
                 ? bp_multicore_4_cfg_p.cce_type           
                 : bp_multicore_4_cce_ucode_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_4_cce_ucode_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_4_cfg_p.cce_pc_width           
                 : bp_multicore_4_cce_ucode_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_4_cce_ucode_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_4_cfg_p.bedrock_data_width           
                 : bp_multicore_4_cce_ucode_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_4_cce_ucode_override_p.l2_features == "inv") 
                 ? bp_multicore_4_cfg_p.l2_features           
                 : bp_multicore_4_cce_ucode_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_4_cce_ucode_override_p.l2_banks == "inv") 
                 ? bp_multicore_4_cfg_p.l2_banks           
                 : bp_multicore_4_cce_ucode_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_4_cce_ucode_override_p.l2_data_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_data_width           
                 : bp_multicore_4_cce_ucode_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_4_cce_ucode_override_p.l2_sets == "inv") 
                 ? bp_multicore_4_cfg_p.l2_sets           
                 : bp_multicore_4_cce_ucode_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_4_cce_ucode_override_p.l2_assoc == "inv") 
                 ? bp_multicore_4_cfg_p.l2_assoc           
                 : bp_multicore_4_cce_ucode_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_4_cce_ucode_override_p.l2_block_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_block_width           
                 : bp_multicore_4_cce_ucode_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_4_cce_ucode_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_4_cfg_p.l2_fill_width           
                 : bp_multicore_4_cce_ucode_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_4_cce_ucode_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_4_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_4_cce_ucode_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_4_cce_ucode_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_coh_clk           
                 : bp_multicore_4_cce_ucode_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_4_cce_ucode_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_max_credits           
                 : bp_multicore_4_cce_ucode_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_4_cce_ucode_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_flit_width           
                 : bp_multicore_4_cce_ucode_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_4_cce_ucode_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_cid_width           
                 : bp_multicore_4_cce_ucode_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_4_cce_ucode_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.coh_noc_len_width           
                 : bp_multicore_4_cce_ucode_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_4_cce_ucode_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_mem_clk           
                 : bp_multicore_4_cce_ucode_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_4_cce_ucode_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_max_credits           
                 : bp_multicore_4_cce_ucode_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_4_cce_ucode_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_flit_width           
                 : bp_multicore_4_cce_ucode_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_4_cce_ucode_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_cid_width           
                 : bp_multicore_4_cce_ucode_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_4_cce_ucode_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.mem_noc_len_width           
                 : bp_multicore_4_cce_ucode_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_4_cce_ucode_override_p.async_io_clk == "inv") 
                 ? bp_multicore_4_cfg_p.async_io_clk           
                 : bp_multicore_4_cce_ucode_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_4_cce_ucode_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_max_credits           
                 : bp_multicore_4_cce_ucode_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_4_cce_ucode_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_flit_width           
                 : bp_multicore_4_cce_ucode_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_4_cce_ucode_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_cid_width           
                 : bp_multicore_4_cce_ucode_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_4_cce_ucode_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_did_width           
                 : bp_multicore_4_cce_ucode_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_4_cce_ucode_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_4_cfg_p.io_noc_len_width           
                 : bp_multicore_4_cce_ucode_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_6_cce_ucode_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_6_cce_ucode_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_6_cce_ucode_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_6_cfg_p.cc_x_dim           
                 : bp_multicore_6_cce_ucode_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_6_cce_ucode_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_6_cfg_p.cc_y_dim           
                 : bp_multicore_6_cce_ucode_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_6_cce_ucode_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_6_cfg_p.ic_y_dim           
                 : bp_multicore_6_cce_ucode_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_6_cce_ucode_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_6_cfg_p.mc_y_dim           
                 : bp_multicore_6_cce_ucode_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_6_cce_ucode_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_6_cfg_p.cac_x_dim           
                 : bp_multicore_6_cce_ucode_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_6_cce_ucode_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_6_cfg_p.sac_x_dim           
                 : bp_multicore_6_cce_ucode_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_6_cce_ucode_override_p.cacc_type == "inv") 
                 ? bp_multicore_6_cfg_p.cacc_type           
                 : bp_multicore_6_cce_ucode_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_6_cce_ucode_override_p.sacc_type == "inv") 
                 ? bp_multicore_6_cfg_p.sacc_type           
                 : bp_multicore_6_cce_ucode_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_6_cce_ucode_override_p.num_cce == "inv") 
                 ? bp_multicore_6_cfg_p.num_cce           
                 : bp_multicore_6_cce_ucode_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_6_cce_ucode_override_p.num_lce == "inv") 
                 ? bp_multicore_6_cfg_p.num_lce           
                 : bp_multicore_6_cce_ucode_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_6_cce_ucode_override_p.vaddr_width == "inv") 
                 ? bp_multicore_6_cfg_p.vaddr_width           
                 : bp_multicore_6_cce_ucode_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_6_cce_ucode_override_p.paddr_width == "inv") 
                 ? bp_multicore_6_cfg_p.paddr_width           
                 : bp_multicore_6_cce_ucode_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_6_cce_ucode_override_p.daddr_width == "inv") 
                 ? bp_multicore_6_cfg_p.daddr_width           
                 : bp_multicore_6_cce_ucode_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_6_cce_ucode_override_p.caddr_width == "inv") 
                 ? bp_multicore_6_cfg_p.caddr_width           
                 : bp_multicore_6_cce_ucode_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_6_cce_ucode_override_p.asid_width == "inv") 
                 ? bp_multicore_6_cfg_p.asid_width           
                 : bp_multicore_6_cce_ucode_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_6_cce_ucode_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_6_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_6_cce_ucode_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_6_cce_ucode_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_6_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_6_cce_ucode_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_6_cce_ucode_override_p.muldiv_support == "inv") 
                 ? bp_multicore_6_cfg_p.muldiv_support           
                 : bp_multicore_6_cce_ucode_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_6_cce_ucode_override_p.fpu_support == "inv") 
                 ? bp_multicore_6_cfg_p.fpu_support           
                 : bp_multicore_6_cce_ucode_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_6_cce_ucode_override_p.compressed_support == "inv") 
                 ? bp_multicore_6_cfg_p.compressed_support           
                 : bp_multicore_6_cce_ucode_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_6_cce_ucode_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_6_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_6_cce_ucode_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_6_cce_ucode_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_6_cfg_p.btb_tag_width           
                 : bp_multicore_6_cce_ucode_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_6_cce_ucode_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_6_cfg_p.btb_idx_width           
                 : bp_multicore_6_cce_ucode_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_6_cce_ucode_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_6_cfg_p.bht_idx_width           
                 : bp_multicore_6_cce_ucode_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_6_cce_ucode_override_p.bht_row_els == "inv") 
                 ? bp_multicore_6_cfg_p.bht_row_els           
                 : bp_multicore_6_cce_ucode_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_6_cce_ucode_override_p.ghist_width == "inv") 
                 ? bp_multicore_6_cfg_p.ghist_width           
                 : bp_multicore_6_cce_ucode_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_6_cce_ucode_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_6_cfg_p.itlb_els_4k           
                 : bp_multicore_6_cce_ucode_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_6_cce_ucode_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_6_cfg_p.itlb_els_1g           
                 : bp_multicore_6_cce_ucode_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_6_cce_ucode_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_6_cfg_p.dtlb_els_4k           
                 : bp_multicore_6_cce_ucode_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_6_cce_ucode_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_6_cfg_p.dtlb_els_1g           
                 : bp_multicore_6_cce_ucode_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_6_cce_ucode_override_p.icache_features == "inv") 
                 ? bp_multicore_6_cfg_p.icache_features           
                 : bp_multicore_6_cce_ucode_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_6_cce_ucode_override_p.icache_sets == "inv") 
                 ? bp_multicore_6_cfg_p.icache_sets           
                 : bp_multicore_6_cce_ucode_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_6_cce_ucode_override_p.icache_assoc == "inv") 
                 ? bp_multicore_6_cfg_p.icache_assoc           
                 : bp_multicore_6_cce_ucode_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_6_cce_ucode_override_p.icache_block_width == "inv") 
                 ? bp_multicore_6_cfg_p.icache_block_width           
                 : bp_multicore_6_cce_ucode_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_6_cce_ucode_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_6_cfg_p.icache_fill_width           
                 : bp_multicore_6_cce_ucode_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_6_cce_ucode_override_p.dcache_features == "inv") 
                 ? bp_multicore_6_cfg_p.dcache_features           
                 : bp_multicore_6_cce_ucode_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_6_cce_ucode_override_p.dcache_sets == "inv") 
                 ? bp_multicore_6_cfg_p.dcache_sets           
                 : bp_multicore_6_cce_ucode_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_6_cce_ucode_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_6_cfg_p.dcache_assoc           
                 : bp_multicore_6_cce_ucode_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_6_cce_ucode_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_6_cfg_p.dcache_block_width           
                 : bp_multicore_6_cce_ucode_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_6_cce_ucode_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_6_cfg_p.dcache_fill_width           
                 : bp_multicore_6_cce_ucode_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_6_cce_ucode_override_p.acache_features == "inv") 
                 ? bp_multicore_6_cfg_p.acache_features           
                 : bp_multicore_6_cce_ucode_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_6_cce_ucode_override_p.acache_sets == "inv") 
                 ? bp_multicore_6_cfg_p.acache_sets           
                 : bp_multicore_6_cce_ucode_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_6_cce_ucode_override_p.acache_assoc == "inv") 
                 ? bp_multicore_6_cfg_p.acache_assoc           
                 : bp_multicore_6_cce_ucode_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_6_cce_ucode_override_p.acache_block_width == "inv") 
                 ? bp_multicore_6_cfg_p.acache_block_width           
                 : bp_multicore_6_cce_ucode_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_6_cce_ucode_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_6_cfg_p.acache_fill_width           
                 : bp_multicore_6_cce_ucode_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_6_cce_ucode_override_p.cce_type == "inv") 
                 ? bp_multicore_6_cfg_p.cce_type           
                 : bp_multicore_6_cce_ucode_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_6_cce_ucode_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_6_cfg_p.cce_pc_width           
                 : bp_multicore_6_cce_ucode_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_6_cce_ucode_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_6_cfg_p.bedrock_data_width           
                 : bp_multicore_6_cce_ucode_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_6_cce_ucode_override_p.l2_features == "inv") 
                 ? bp_multicore_6_cfg_p.l2_features           
                 : bp_multicore_6_cce_ucode_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_6_cce_ucode_override_p.l2_banks == "inv") 
                 ? bp_multicore_6_cfg_p.l2_banks           
                 : bp_multicore_6_cce_ucode_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_6_cce_ucode_override_p.l2_data_width == "inv") 
                 ? bp_multicore_6_cfg_p.l2_data_width           
                 : bp_multicore_6_cce_ucode_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_6_cce_ucode_override_p.l2_sets == "inv") 
                 ? bp_multicore_6_cfg_p.l2_sets           
                 : bp_multicore_6_cce_ucode_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_6_cce_ucode_override_p.l2_assoc == "inv") 
                 ? bp_multicore_6_cfg_p.l2_assoc           
                 : bp_multicore_6_cce_ucode_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_6_cce_ucode_override_p.l2_block_width == "inv") 
                 ? bp_multicore_6_cfg_p.l2_block_width           
                 : bp_multicore_6_cce_ucode_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_6_cce_ucode_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_6_cfg_p.l2_fill_width           
                 : bp_multicore_6_cce_ucode_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_6_cce_ucode_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_6_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_6_cce_ucode_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_6_cce_ucode_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_6_cfg_p.async_coh_clk           
                 : bp_multicore_6_cce_ucode_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_6_cce_ucode_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_6_cfg_p.coh_noc_max_credits           
                 : bp_multicore_6_cce_ucode_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_6_cce_ucode_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_6_cfg_p.coh_noc_flit_width           
                 : bp_multicore_6_cce_ucode_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_6_cce_ucode_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_6_cfg_p.coh_noc_cid_width           
                 : bp_multicore_6_cce_ucode_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_6_cce_ucode_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_6_cfg_p.coh_noc_len_width           
                 : bp_multicore_6_cce_ucode_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_6_cce_ucode_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_6_cfg_p.async_mem_clk           
                 : bp_multicore_6_cce_ucode_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_6_cce_ucode_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_6_cfg_p.mem_noc_max_credits           
                 : bp_multicore_6_cce_ucode_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_6_cce_ucode_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_6_cfg_p.mem_noc_flit_width           
                 : bp_multicore_6_cce_ucode_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_6_cce_ucode_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_6_cfg_p.mem_noc_cid_width           
                 : bp_multicore_6_cce_ucode_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_6_cce_ucode_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_6_cfg_p.mem_noc_len_width           
                 : bp_multicore_6_cce_ucode_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_6_cce_ucode_override_p.async_io_clk == "inv") 
                 ? bp_multicore_6_cfg_p.async_io_clk           
                 : bp_multicore_6_cce_ucode_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_6_cce_ucode_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_6_cfg_p.io_noc_max_credits           
                 : bp_multicore_6_cce_ucode_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_6_cce_ucode_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_6_cfg_p.io_noc_flit_width           
                 : bp_multicore_6_cce_ucode_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_6_cce_ucode_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_6_cfg_p.io_noc_cid_width           
                 : bp_multicore_6_cce_ucode_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_6_cce_ucode_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_6_cfg_p.io_noc_did_width           
                 : bp_multicore_6_cce_ucode_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_6_cce_ucode_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_6_cfg_p.io_noc_len_width           
                 : bp_multicore_6_cce_ucode_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_8_cce_ucode_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_8_cce_ucode_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_8_cce_ucode_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_8_cfg_p.cc_x_dim           
                 : bp_multicore_8_cce_ucode_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_8_cce_ucode_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_8_cfg_p.cc_y_dim           
                 : bp_multicore_8_cce_ucode_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_8_cce_ucode_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_8_cfg_p.ic_y_dim           
                 : bp_multicore_8_cce_ucode_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_8_cce_ucode_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_8_cfg_p.mc_y_dim           
                 : bp_multicore_8_cce_ucode_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_8_cce_ucode_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_8_cfg_p.cac_x_dim           
                 : bp_multicore_8_cce_ucode_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_8_cce_ucode_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_8_cfg_p.sac_x_dim           
                 : bp_multicore_8_cce_ucode_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_8_cce_ucode_override_p.cacc_type == "inv") 
                 ? bp_multicore_8_cfg_p.cacc_type           
                 : bp_multicore_8_cce_ucode_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_8_cce_ucode_override_p.sacc_type == "inv") 
                 ? bp_multicore_8_cfg_p.sacc_type           
                 : bp_multicore_8_cce_ucode_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_8_cce_ucode_override_p.num_cce == "inv") 
                 ? bp_multicore_8_cfg_p.num_cce           
                 : bp_multicore_8_cce_ucode_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_8_cce_ucode_override_p.num_lce == "inv") 
                 ? bp_multicore_8_cfg_p.num_lce           
                 : bp_multicore_8_cce_ucode_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_8_cce_ucode_override_p.vaddr_width == "inv") 
                 ? bp_multicore_8_cfg_p.vaddr_width           
                 : bp_multicore_8_cce_ucode_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_8_cce_ucode_override_p.paddr_width == "inv") 
                 ? bp_multicore_8_cfg_p.paddr_width           
                 : bp_multicore_8_cce_ucode_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_8_cce_ucode_override_p.daddr_width == "inv") 
                 ? bp_multicore_8_cfg_p.daddr_width           
                 : bp_multicore_8_cce_ucode_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_8_cce_ucode_override_p.caddr_width == "inv") 
                 ? bp_multicore_8_cfg_p.caddr_width           
                 : bp_multicore_8_cce_ucode_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_8_cce_ucode_override_p.asid_width == "inv") 
                 ? bp_multicore_8_cfg_p.asid_width           
                 : bp_multicore_8_cce_ucode_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_8_cce_ucode_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_8_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_8_cce_ucode_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_8_cce_ucode_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_8_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_8_cce_ucode_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_8_cce_ucode_override_p.muldiv_support == "inv") 
                 ? bp_multicore_8_cfg_p.muldiv_support           
                 : bp_multicore_8_cce_ucode_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_8_cce_ucode_override_p.fpu_support == "inv") 
                 ? bp_multicore_8_cfg_p.fpu_support           
                 : bp_multicore_8_cce_ucode_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_8_cce_ucode_override_p.compressed_support == "inv") 
                 ? bp_multicore_8_cfg_p.compressed_support           
                 : bp_multicore_8_cce_ucode_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_8_cce_ucode_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_8_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_8_cce_ucode_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_8_cce_ucode_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_8_cfg_p.btb_tag_width           
                 : bp_multicore_8_cce_ucode_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_8_cce_ucode_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_8_cfg_p.btb_idx_width           
                 : bp_multicore_8_cce_ucode_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_8_cce_ucode_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_8_cfg_p.bht_idx_width           
                 : bp_multicore_8_cce_ucode_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_8_cce_ucode_override_p.bht_row_els == "inv") 
                 ? bp_multicore_8_cfg_p.bht_row_els           
                 : bp_multicore_8_cce_ucode_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_8_cce_ucode_override_p.ghist_width == "inv") 
                 ? bp_multicore_8_cfg_p.ghist_width           
                 : bp_multicore_8_cce_ucode_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_8_cce_ucode_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_8_cfg_p.itlb_els_4k           
                 : bp_multicore_8_cce_ucode_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_8_cce_ucode_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_8_cfg_p.itlb_els_1g           
                 : bp_multicore_8_cce_ucode_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_8_cce_ucode_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_8_cfg_p.dtlb_els_4k           
                 : bp_multicore_8_cce_ucode_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_8_cce_ucode_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_8_cfg_p.dtlb_els_1g           
                 : bp_multicore_8_cce_ucode_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_8_cce_ucode_override_p.icache_features == "inv") 
                 ? bp_multicore_8_cfg_p.icache_features           
                 : bp_multicore_8_cce_ucode_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_8_cce_ucode_override_p.icache_sets == "inv") 
                 ? bp_multicore_8_cfg_p.icache_sets           
                 : bp_multicore_8_cce_ucode_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_8_cce_ucode_override_p.icache_assoc == "inv") 
                 ? bp_multicore_8_cfg_p.icache_assoc           
                 : bp_multicore_8_cce_ucode_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_8_cce_ucode_override_p.icache_block_width == "inv") 
                 ? bp_multicore_8_cfg_p.icache_block_width           
                 : bp_multicore_8_cce_ucode_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_8_cce_ucode_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_8_cfg_p.icache_fill_width           
                 : bp_multicore_8_cce_ucode_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_8_cce_ucode_override_p.dcache_features == "inv") 
                 ? bp_multicore_8_cfg_p.dcache_features           
                 : bp_multicore_8_cce_ucode_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_8_cce_ucode_override_p.dcache_sets == "inv") 
                 ? bp_multicore_8_cfg_p.dcache_sets           
                 : bp_multicore_8_cce_ucode_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_8_cce_ucode_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_8_cfg_p.dcache_assoc           
                 : bp_multicore_8_cce_ucode_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_8_cce_ucode_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_8_cfg_p.dcache_block_width           
                 : bp_multicore_8_cce_ucode_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_8_cce_ucode_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_8_cfg_p.dcache_fill_width           
                 : bp_multicore_8_cce_ucode_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_8_cce_ucode_override_p.acache_features == "inv") 
                 ? bp_multicore_8_cfg_p.acache_features           
                 : bp_multicore_8_cce_ucode_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_8_cce_ucode_override_p.acache_sets == "inv") 
                 ? bp_multicore_8_cfg_p.acache_sets           
                 : bp_multicore_8_cce_ucode_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_8_cce_ucode_override_p.acache_assoc == "inv") 
                 ? bp_multicore_8_cfg_p.acache_assoc           
                 : bp_multicore_8_cce_ucode_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_8_cce_ucode_override_p.acache_block_width == "inv") 
                 ? bp_multicore_8_cfg_p.acache_block_width           
                 : bp_multicore_8_cce_ucode_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_8_cce_ucode_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_8_cfg_p.acache_fill_width           
                 : bp_multicore_8_cce_ucode_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_8_cce_ucode_override_p.cce_type == "inv") 
                 ? bp_multicore_8_cfg_p.cce_type           
                 : bp_multicore_8_cce_ucode_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_8_cce_ucode_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_8_cfg_p.cce_pc_width           
                 : bp_multicore_8_cce_ucode_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_8_cce_ucode_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_8_cfg_p.bedrock_data_width           
                 : bp_multicore_8_cce_ucode_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_8_cce_ucode_override_p.l2_features == "inv") 
                 ? bp_multicore_8_cfg_p.l2_features           
                 : bp_multicore_8_cce_ucode_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_8_cce_ucode_override_p.l2_banks == "inv") 
                 ? bp_multicore_8_cfg_p.l2_banks           
                 : bp_multicore_8_cce_ucode_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_8_cce_ucode_override_p.l2_data_width == "inv") 
                 ? bp_multicore_8_cfg_p.l2_data_width           
                 : bp_multicore_8_cce_ucode_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_8_cce_ucode_override_p.l2_sets == "inv") 
                 ? bp_multicore_8_cfg_p.l2_sets           
                 : bp_multicore_8_cce_ucode_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_8_cce_ucode_override_p.l2_assoc == "inv") 
                 ? bp_multicore_8_cfg_p.l2_assoc           
                 : bp_multicore_8_cce_ucode_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_8_cce_ucode_override_p.l2_block_width == "inv") 
                 ? bp_multicore_8_cfg_p.l2_block_width           
                 : bp_multicore_8_cce_ucode_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_8_cce_ucode_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_8_cfg_p.l2_fill_width           
                 : bp_multicore_8_cce_ucode_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_8_cce_ucode_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_8_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_8_cce_ucode_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_8_cce_ucode_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_8_cfg_p.async_coh_clk           
                 : bp_multicore_8_cce_ucode_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_8_cce_ucode_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_8_cfg_p.coh_noc_max_credits           
                 : bp_multicore_8_cce_ucode_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_8_cce_ucode_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_8_cfg_p.coh_noc_flit_width           
                 : bp_multicore_8_cce_ucode_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_8_cce_ucode_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_8_cfg_p.coh_noc_cid_width           
                 : bp_multicore_8_cce_ucode_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_8_cce_ucode_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_8_cfg_p.coh_noc_len_width           
                 : bp_multicore_8_cce_ucode_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_8_cce_ucode_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_8_cfg_p.async_mem_clk           
                 : bp_multicore_8_cce_ucode_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_8_cce_ucode_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_8_cfg_p.mem_noc_max_credits           
                 : bp_multicore_8_cce_ucode_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_8_cce_ucode_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_8_cfg_p.mem_noc_flit_width           
                 : bp_multicore_8_cce_ucode_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_8_cce_ucode_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_8_cfg_p.mem_noc_cid_width           
                 : bp_multicore_8_cce_ucode_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_8_cce_ucode_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_8_cfg_p.mem_noc_len_width           
                 : bp_multicore_8_cce_ucode_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_8_cce_ucode_override_p.async_io_clk == "inv") 
                 ? bp_multicore_8_cfg_p.async_io_clk           
                 : bp_multicore_8_cce_ucode_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_8_cce_ucode_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_8_cfg_p.io_noc_max_credits           
                 : bp_multicore_8_cce_ucode_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_8_cce_ucode_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_8_cfg_p.io_noc_flit_width           
                 : bp_multicore_8_cce_ucode_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_8_cce_ucode_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_8_cfg_p.io_noc_cid_width           
                 : bp_multicore_8_cce_ucode_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_8_cce_ucode_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_8_cfg_p.io_noc_did_width           
                 : bp_multicore_8_cce_ucode_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_8_cce_ucode_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_8_cfg_p.io_noc_len_width           
                 : bp_multicore_8_cce_ucode_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_12_cce_ucode_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_12_cce_ucode_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_12_cce_ucode_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_12_cfg_p.cc_x_dim           
                 : bp_multicore_12_cce_ucode_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_12_cce_ucode_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_12_cfg_p.cc_y_dim           
                 : bp_multicore_12_cce_ucode_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_12_cce_ucode_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_12_cfg_p.ic_y_dim           
                 : bp_multicore_12_cce_ucode_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_12_cce_ucode_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_12_cfg_p.mc_y_dim           
                 : bp_multicore_12_cce_ucode_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_12_cce_ucode_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_12_cfg_p.cac_x_dim           
                 : bp_multicore_12_cce_ucode_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_12_cce_ucode_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_12_cfg_p.sac_x_dim           
                 : bp_multicore_12_cce_ucode_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_12_cce_ucode_override_p.cacc_type == "inv") 
                 ? bp_multicore_12_cfg_p.cacc_type           
                 : bp_multicore_12_cce_ucode_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_12_cce_ucode_override_p.sacc_type == "inv") 
                 ? bp_multicore_12_cfg_p.sacc_type           
                 : bp_multicore_12_cce_ucode_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_12_cce_ucode_override_p.num_cce == "inv") 
                 ? bp_multicore_12_cfg_p.num_cce           
                 : bp_multicore_12_cce_ucode_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_12_cce_ucode_override_p.num_lce == "inv") 
                 ? bp_multicore_12_cfg_p.num_lce           
                 : bp_multicore_12_cce_ucode_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_12_cce_ucode_override_p.vaddr_width == "inv") 
                 ? bp_multicore_12_cfg_p.vaddr_width           
                 : bp_multicore_12_cce_ucode_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_12_cce_ucode_override_p.paddr_width == "inv") 
                 ? bp_multicore_12_cfg_p.paddr_width           
                 : bp_multicore_12_cce_ucode_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_12_cce_ucode_override_p.daddr_width == "inv") 
                 ? bp_multicore_12_cfg_p.daddr_width           
                 : bp_multicore_12_cce_ucode_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_12_cce_ucode_override_p.caddr_width == "inv") 
                 ? bp_multicore_12_cfg_p.caddr_width           
                 : bp_multicore_12_cce_ucode_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_12_cce_ucode_override_p.asid_width == "inv") 
                 ? bp_multicore_12_cfg_p.asid_width           
                 : bp_multicore_12_cce_ucode_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_12_cce_ucode_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_12_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_12_cce_ucode_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_12_cce_ucode_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_12_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_12_cce_ucode_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_12_cce_ucode_override_p.muldiv_support == "inv") 
                 ? bp_multicore_12_cfg_p.muldiv_support           
                 : bp_multicore_12_cce_ucode_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_12_cce_ucode_override_p.fpu_support == "inv") 
                 ? bp_multicore_12_cfg_p.fpu_support           
                 : bp_multicore_12_cce_ucode_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_12_cce_ucode_override_p.compressed_support == "inv") 
                 ? bp_multicore_12_cfg_p.compressed_support           
                 : bp_multicore_12_cce_ucode_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_12_cce_ucode_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_12_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_12_cce_ucode_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_12_cce_ucode_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_12_cfg_p.btb_tag_width           
                 : bp_multicore_12_cce_ucode_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_12_cce_ucode_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_12_cfg_p.btb_idx_width           
                 : bp_multicore_12_cce_ucode_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_12_cce_ucode_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_12_cfg_p.bht_idx_width           
                 : bp_multicore_12_cce_ucode_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_12_cce_ucode_override_p.bht_row_els == "inv") 
                 ? bp_multicore_12_cfg_p.bht_row_els           
                 : bp_multicore_12_cce_ucode_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_12_cce_ucode_override_p.ghist_width == "inv") 
                 ? bp_multicore_12_cfg_p.ghist_width           
                 : bp_multicore_12_cce_ucode_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_12_cce_ucode_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_12_cfg_p.itlb_els_4k           
                 : bp_multicore_12_cce_ucode_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_12_cce_ucode_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_12_cfg_p.itlb_els_1g           
                 : bp_multicore_12_cce_ucode_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_12_cce_ucode_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_12_cfg_p.dtlb_els_4k           
                 : bp_multicore_12_cce_ucode_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_12_cce_ucode_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_12_cfg_p.dtlb_els_1g           
                 : bp_multicore_12_cce_ucode_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_12_cce_ucode_override_p.icache_features == "inv") 
                 ? bp_multicore_12_cfg_p.icache_features           
                 : bp_multicore_12_cce_ucode_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_12_cce_ucode_override_p.icache_sets == "inv") 
                 ? bp_multicore_12_cfg_p.icache_sets           
                 : bp_multicore_12_cce_ucode_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_12_cce_ucode_override_p.icache_assoc == "inv") 
                 ? bp_multicore_12_cfg_p.icache_assoc           
                 : bp_multicore_12_cce_ucode_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_12_cce_ucode_override_p.icache_block_width == "inv") 
                 ? bp_multicore_12_cfg_p.icache_block_width           
                 : bp_multicore_12_cce_ucode_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_12_cce_ucode_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_12_cfg_p.icache_fill_width           
                 : bp_multicore_12_cce_ucode_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_12_cce_ucode_override_p.dcache_features == "inv") 
                 ? bp_multicore_12_cfg_p.dcache_features           
                 : bp_multicore_12_cce_ucode_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_12_cce_ucode_override_p.dcache_sets == "inv") 
                 ? bp_multicore_12_cfg_p.dcache_sets           
                 : bp_multicore_12_cce_ucode_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_12_cce_ucode_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_12_cfg_p.dcache_assoc           
                 : bp_multicore_12_cce_ucode_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_12_cce_ucode_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_12_cfg_p.dcache_block_width           
                 : bp_multicore_12_cce_ucode_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_12_cce_ucode_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_12_cfg_p.dcache_fill_width           
                 : bp_multicore_12_cce_ucode_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_12_cce_ucode_override_p.acache_features == "inv") 
                 ? bp_multicore_12_cfg_p.acache_features           
                 : bp_multicore_12_cce_ucode_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_12_cce_ucode_override_p.acache_sets == "inv") 
                 ? bp_multicore_12_cfg_p.acache_sets           
                 : bp_multicore_12_cce_ucode_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_12_cce_ucode_override_p.acache_assoc == "inv") 
                 ? bp_multicore_12_cfg_p.acache_assoc           
                 : bp_multicore_12_cce_ucode_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_12_cce_ucode_override_p.acache_block_width == "inv") 
                 ? bp_multicore_12_cfg_p.acache_block_width           
                 : bp_multicore_12_cce_ucode_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_12_cce_ucode_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_12_cfg_p.acache_fill_width           
                 : bp_multicore_12_cce_ucode_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_12_cce_ucode_override_p.cce_type == "inv") 
                 ? bp_multicore_12_cfg_p.cce_type           
                 : bp_multicore_12_cce_ucode_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_12_cce_ucode_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_12_cfg_p.cce_pc_width           
                 : bp_multicore_12_cce_ucode_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_12_cce_ucode_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_12_cfg_p.bedrock_data_width           
                 : bp_multicore_12_cce_ucode_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_12_cce_ucode_override_p.l2_features == "inv") 
                 ? bp_multicore_12_cfg_p.l2_features           
                 : bp_multicore_12_cce_ucode_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_12_cce_ucode_override_p.l2_banks == "inv") 
                 ? bp_multicore_12_cfg_p.l2_banks           
                 : bp_multicore_12_cce_ucode_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_12_cce_ucode_override_p.l2_data_width == "inv") 
                 ? bp_multicore_12_cfg_p.l2_data_width           
                 : bp_multicore_12_cce_ucode_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_12_cce_ucode_override_p.l2_sets == "inv") 
                 ? bp_multicore_12_cfg_p.l2_sets           
                 : bp_multicore_12_cce_ucode_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_12_cce_ucode_override_p.l2_assoc == "inv") 
                 ? bp_multicore_12_cfg_p.l2_assoc           
                 : bp_multicore_12_cce_ucode_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_12_cce_ucode_override_p.l2_block_width == "inv") 
                 ? bp_multicore_12_cfg_p.l2_block_width           
                 : bp_multicore_12_cce_ucode_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_12_cce_ucode_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_12_cfg_p.l2_fill_width           
                 : bp_multicore_12_cce_ucode_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_12_cce_ucode_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_12_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_12_cce_ucode_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_12_cce_ucode_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_12_cfg_p.async_coh_clk           
                 : bp_multicore_12_cce_ucode_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_12_cce_ucode_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_12_cfg_p.coh_noc_max_credits           
                 : bp_multicore_12_cce_ucode_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_12_cce_ucode_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_12_cfg_p.coh_noc_flit_width           
                 : bp_multicore_12_cce_ucode_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_12_cce_ucode_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_12_cfg_p.coh_noc_cid_width           
                 : bp_multicore_12_cce_ucode_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_12_cce_ucode_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_12_cfg_p.coh_noc_len_width           
                 : bp_multicore_12_cce_ucode_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_12_cce_ucode_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_12_cfg_p.async_mem_clk           
                 : bp_multicore_12_cce_ucode_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_12_cce_ucode_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_12_cfg_p.mem_noc_max_credits           
                 : bp_multicore_12_cce_ucode_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_12_cce_ucode_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_12_cfg_p.mem_noc_flit_width           
                 : bp_multicore_12_cce_ucode_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_12_cce_ucode_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_12_cfg_p.mem_noc_cid_width           
                 : bp_multicore_12_cce_ucode_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_12_cce_ucode_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_12_cfg_p.mem_noc_len_width           
                 : bp_multicore_12_cce_ucode_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_12_cce_ucode_override_p.async_io_clk == "inv") 
                 ? bp_multicore_12_cfg_p.async_io_clk           
                 : bp_multicore_12_cce_ucode_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_12_cce_ucode_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_12_cfg_p.io_noc_max_credits           
                 : bp_multicore_12_cce_ucode_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_12_cce_ucode_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_12_cfg_p.io_noc_flit_width           
                 : bp_multicore_12_cce_ucode_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_12_cce_ucode_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_12_cfg_p.io_noc_cid_width           
                 : bp_multicore_12_cce_ucode_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_12_cce_ucode_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_12_cfg_p.io_noc_did_width           
                 : bp_multicore_12_cce_ucode_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_12_cce_ucode_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_12_cfg_p.io_noc_len_width           
                 : bp_multicore_12_cce_ucode_override_p.io_noc_len_width          
     
       }
;

localparam bp_proc_param_s bp_multicore_16_cce_ucode_override_p =
 '{cce_type : e_cce_ucode
   ,default : "inv"
   };

   localparam bp_proc_param_s bp_multicore_16_cce_ucode_cfg_p =                                                     
     '{
   cc_x_dim: (bp_multicore_16_cce_ucode_override_p.cc_x_dim == "inv") 
                 ? bp_multicore_16_cfg_p.cc_x_dim           
                 : bp_multicore_16_cce_ucode_override_p.cc_x_dim          
              
       ,
   cc_y_dim: (bp_multicore_16_cce_ucode_override_p.cc_y_dim == "inv") 
                 ? bp_multicore_16_cfg_p.cc_y_dim           
                 : bp_multicore_16_cce_ucode_override_p.cc_y_dim          
             
       ,
   ic_y_dim: (bp_multicore_16_cce_ucode_override_p.ic_y_dim == "inv") 
                 ? bp_multicore_16_cfg_p.ic_y_dim           
                 : bp_multicore_16_cce_ucode_override_p.ic_y_dim          
             
       ,
   mc_y_dim: (bp_multicore_16_cce_ucode_override_p.mc_y_dim == "inv") 
                 ? bp_multicore_16_cfg_p.mc_y_dim           
                 : bp_multicore_16_cce_ucode_override_p.mc_y_dim          
             
       ,
   cac_x_dim: (bp_multicore_16_cce_ucode_override_p.cac_x_dim == "inv") 
                 ? bp_multicore_16_cfg_p.cac_x_dim           
                 : bp_multicore_16_cce_ucode_override_p.cac_x_dim          
            
       ,
   sac_x_dim: (bp_multicore_16_cce_ucode_override_p.sac_x_dim == "inv") 
                 ? bp_multicore_16_cfg_p.sac_x_dim           
                 : bp_multicore_16_cce_ucode_override_p.sac_x_dim          
            
       ,
   cacc_type: (bp_multicore_16_cce_ucode_override_p.cacc_type == "inv") 
                 ? bp_multicore_16_cfg_p.cacc_type           
                 : bp_multicore_16_cce_ucode_override_p.cacc_type          
            
       ,
   sacc_type: (bp_multicore_16_cce_ucode_override_p.sacc_type == "inv") 
                 ? bp_multicore_16_cfg_p.sacc_type           
                 : bp_multicore_16_cce_ucode_override_p.sacc_type          
            
                                                                                                
       ,
   num_cce: (bp_multicore_16_cce_ucode_override_p.num_cce == "inv") 
                 ? bp_multicore_16_cfg_p.num_cce           
                 : bp_multicore_16_cce_ucode_override_p.num_cce          
              
       ,
   num_lce: (bp_multicore_16_cce_ucode_override_p.num_lce == "inv") 
                 ? bp_multicore_16_cfg_p.num_lce           
                 : bp_multicore_16_cce_ucode_override_p.num_lce          
              
                                                                                                
       ,
   vaddr_width: (bp_multicore_16_cce_ucode_override_p.vaddr_width == "inv") 
                 ? bp_multicore_16_cfg_p.vaddr_width           
                 : bp_multicore_16_cce_ucode_override_p.vaddr_width          
          
       ,
   paddr_width: (bp_multicore_16_cce_ucode_override_p.paddr_width == "inv") 
                 ? bp_multicore_16_cfg_p.paddr_width           
                 : bp_multicore_16_cce_ucode_override_p.paddr_width          
          
       ,
   daddr_width: (bp_multicore_16_cce_ucode_override_p.daddr_width == "inv") 
                 ? bp_multicore_16_cfg_p.daddr_width           
                 : bp_multicore_16_cce_ucode_override_p.daddr_width          
          
       ,
   caddr_width: (bp_multicore_16_cce_ucode_override_p.caddr_width == "inv") 
                 ? bp_multicore_16_cfg_p.caddr_width           
                 : bp_multicore_16_cce_ucode_override_p.caddr_width          
          
       ,
   asid_width: (bp_multicore_16_cce_ucode_override_p.asid_width == "inv") 
                 ? bp_multicore_16_cfg_p.asid_width           
                 : bp_multicore_16_cce_ucode_override_p.asid_width          
           
                                                                                                
       ,
   fe_queue_fifo_els: (bp_multicore_16_cce_ucode_override_p.fe_queue_fifo_els == "inv") 
                 ? bp_multicore_16_cfg_p.fe_queue_fifo_els           
                 : bp_multicore_16_cce_ucode_override_p.fe_queue_fifo_els          
    
       ,
   fe_cmd_fifo_els: (bp_multicore_16_cce_ucode_override_p.fe_cmd_fifo_els == "inv") 
                 ? bp_multicore_16_cfg_p.fe_cmd_fifo_els           
                 : bp_multicore_16_cce_ucode_override_p.fe_cmd_fifo_els          
      
       ,
   muldiv_support: (bp_multicore_16_cce_ucode_override_p.muldiv_support == "inv") 
                 ? bp_multicore_16_cfg_p.muldiv_support           
                 : bp_multicore_16_cce_ucode_override_p.muldiv_support          
       
       ,
   fpu_support: (bp_multicore_16_cce_ucode_override_p.fpu_support == "inv") 
                 ? bp_multicore_16_cfg_p.fpu_support           
                 : bp_multicore_16_cce_ucode_override_p.fpu_support          
          
       ,
   compressed_support: (bp_multicore_16_cce_ucode_override_p.compressed_support == "inv") 
                 ? bp_multicore_16_cfg_p.compressed_support           
                 : bp_multicore_16_cce_ucode_override_p.compressed_support          
   
                                                                                                
       ,
   branch_metadata_fwd_width: (bp_multicore_16_cce_ucode_override_p.branch_metadata_fwd_width == "inv") 
                 ? bp_multicore_16_cfg_p.branch_metadata_fwd_width           
                 : bp_multicore_16_cce_ucode_override_p.branch_metadata_fwd_width          

       ,
   btb_tag_width: (bp_multicore_16_cce_ucode_override_p.btb_tag_width == "inv") 
                 ? bp_multicore_16_cfg_p.btb_tag_width           
                 : bp_multicore_16_cce_ucode_override_p.btb_tag_width          
        
       ,
   btb_idx_width: (bp_multicore_16_cce_ucode_override_p.btb_idx_width == "inv") 
                 ? bp_multicore_16_cfg_p.btb_idx_width           
                 : bp_multicore_16_cce_ucode_override_p.btb_idx_width          
        
       ,
   bht_idx_width: (bp_multicore_16_cce_ucode_override_p.bht_idx_width == "inv") 
                 ? bp_multicore_16_cfg_p.bht_idx_width           
                 : bp_multicore_16_cce_ucode_override_p.bht_idx_width          
        
       ,
   bht_row_els: (bp_multicore_16_cce_ucode_override_p.bht_row_els == "inv") 
                 ? bp_multicore_16_cfg_p.bht_row_els           
                 : bp_multicore_16_cce_ucode_override_p.bht_row_els          
          
       ,
   ghist_width: (bp_multicore_16_cce_ucode_override_p.ghist_width == "inv") 
                 ? bp_multicore_16_cfg_p.ghist_width           
                 : bp_multicore_16_cce_ucode_override_p.ghist_width          
          
                                                                                                
       ,
   itlb_els_4k: (bp_multicore_16_cce_ucode_override_p.itlb_els_4k == "inv") 
                 ? bp_multicore_16_cfg_p.itlb_els_4k           
                 : bp_multicore_16_cce_ucode_override_p.itlb_els_4k          
          
       ,
   itlb_els_1g: (bp_multicore_16_cce_ucode_override_p.itlb_els_1g == "inv") 
                 ? bp_multicore_16_cfg_p.itlb_els_1g           
                 : bp_multicore_16_cce_ucode_override_p.itlb_els_1g          
          
       ,
   dtlb_els_4k: (bp_multicore_16_cce_ucode_override_p.dtlb_els_4k == "inv") 
                 ? bp_multicore_16_cfg_p.dtlb_els_4k           
                 : bp_multicore_16_cce_ucode_override_p.dtlb_els_4k          
          
       ,
   dtlb_els_1g: (bp_multicore_16_cce_ucode_override_p.dtlb_els_1g == "inv") 
                 ? bp_multicore_16_cfg_p.dtlb_els_1g           
                 : bp_multicore_16_cce_ucode_override_p.dtlb_els_1g          
          
                                                                                                
       ,
   icache_features: (bp_multicore_16_cce_ucode_override_p.icache_features == "inv") 
                 ? bp_multicore_16_cfg_p.icache_features           
                 : bp_multicore_16_cce_ucode_override_p.icache_features          
      
       ,
   icache_sets: (bp_multicore_16_cce_ucode_override_p.icache_sets == "inv") 
                 ? bp_multicore_16_cfg_p.icache_sets           
                 : bp_multicore_16_cce_ucode_override_p.icache_sets          
          
       ,
   icache_assoc: (bp_multicore_16_cce_ucode_override_p.icache_assoc == "inv") 
                 ? bp_multicore_16_cfg_p.icache_assoc           
                 : bp_multicore_16_cce_ucode_override_p.icache_assoc          
         
       ,
   icache_block_width: (bp_multicore_16_cce_ucode_override_p.icache_block_width == "inv") 
                 ? bp_multicore_16_cfg_p.icache_block_width           
                 : bp_multicore_16_cce_ucode_override_p.icache_block_width          
   
       ,
   icache_fill_width: (bp_multicore_16_cce_ucode_override_p.icache_fill_width == "inv") 
                 ? bp_multicore_16_cfg_p.icache_fill_width           
                 : bp_multicore_16_cce_ucode_override_p.icache_fill_width          
    
                                                                                                
       ,
   dcache_features: (bp_multicore_16_cce_ucode_override_p.dcache_features == "inv") 
                 ? bp_multicore_16_cfg_p.dcache_features           
                 : bp_multicore_16_cce_ucode_override_p.dcache_features          
      
       ,
   dcache_sets: (bp_multicore_16_cce_ucode_override_p.dcache_sets == "inv") 
                 ? bp_multicore_16_cfg_p.dcache_sets           
                 : bp_multicore_16_cce_ucode_override_p.dcache_sets          
          
       ,
   dcache_assoc: (bp_multicore_16_cce_ucode_override_p.dcache_assoc == "inv") 
                 ? bp_multicore_16_cfg_p.dcache_assoc           
                 : bp_multicore_16_cce_ucode_override_p.dcache_assoc          
         
       ,
   dcache_block_width: (bp_multicore_16_cce_ucode_override_p.dcache_block_width == "inv") 
                 ? bp_multicore_16_cfg_p.dcache_block_width           
                 : bp_multicore_16_cce_ucode_override_p.dcache_block_width          
   
       ,
   dcache_fill_width: (bp_multicore_16_cce_ucode_override_p.dcache_fill_width == "inv") 
                 ? bp_multicore_16_cfg_p.dcache_fill_width           
                 : bp_multicore_16_cce_ucode_override_p.dcache_fill_width          
    
                                                                                                
       ,
   acache_features: (bp_multicore_16_cce_ucode_override_p.acache_features == "inv") 
                 ? bp_multicore_16_cfg_p.acache_features           
                 : bp_multicore_16_cce_ucode_override_p.acache_features          
      
       ,
   acache_sets: (bp_multicore_16_cce_ucode_override_p.acache_sets == "inv") 
                 ? bp_multicore_16_cfg_p.acache_sets           
                 : bp_multicore_16_cce_ucode_override_p.acache_sets          
          
       ,
   acache_assoc: (bp_multicore_16_cce_ucode_override_p.acache_assoc == "inv") 
                 ? bp_multicore_16_cfg_p.acache_assoc           
                 : bp_multicore_16_cce_ucode_override_p.acache_assoc          
         
       ,
   acache_block_width: (bp_multicore_16_cce_ucode_override_p.acache_block_width == "inv") 
                 ? bp_multicore_16_cfg_p.acache_block_width           
                 : bp_multicore_16_cce_ucode_override_p.acache_block_width          
   
       ,
   acache_fill_width: (bp_multicore_16_cce_ucode_override_p.acache_fill_width == "inv") 
                 ? bp_multicore_16_cfg_p.acache_fill_width           
                 : bp_multicore_16_cce_ucode_override_p.acache_fill_width          
    
                                                                                                
       ,
   cce_type: (bp_multicore_16_cce_ucode_override_p.cce_type == "inv") 
                 ? bp_multicore_16_cfg_p.cce_type           
                 : bp_multicore_16_cce_ucode_override_p.cce_type          
             
       ,
   cce_pc_width: (bp_multicore_16_cce_ucode_override_p.cce_pc_width == "inv") 
                 ? bp_multicore_16_cfg_p.cce_pc_width           
                 : bp_multicore_16_cce_ucode_override_p.cce_pc_width          
         
       ,
   bedrock_data_width: (bp_multicore_16_cce_ucode_override_p.bedrock_data_width == "inv") 
                 ? bp_multicore_16_cfg_p.bedrock_data_width           
                 : bp_multicore_16_cce_ucode_override_p.bedrock_data_width          
   
                                                                                                
       ,
   l2_features: (bp_multicore_16_cce_ucode_override_p.l2_features == "inv") 
                 ? bp_multicore_16_cfg_p.l2_features           
                 : bp_multicore_16_cce_ucode_override_p.l2_features          
          
       ,
   l2_banks: (bp_multicore_16_cce_ucode_override_p.l2_banks == "inv") 
                 ? bp_multicore_16_cfg_p.l2_banks           
                 : bp_multicore_16_cce_ucode_override_p.l2_banks          
             
       ,
   l2_data_width: (bp_multicore_16_cce_ucode_override_p.l2_data_width == "inv") 
                 ? bp_multicore_16_cfg_p.l2_data_width           
                 : bp_multicore_16_cce_ucode_override_p.l2_data_width          
        
       ,
   l2_sets: (bp_multicore_16_cce_ucode_override_p.l2_sets == "inv") 
                 ? bp_multicore_16_cfg_p.l2_sets           
                 : bp_multicore_16_cce_ucode_override_p.l2_sets          
              
       ,
   l2_assoc: (bp_multicore_16_cce_ucode_override_p.l2_assoc == "inv") 
                 ? bp_multicore_16_cfg_p.l2_assoc           
                 : bp_multicore_16_cce_ucode_override_p.l2_assoc          
             
       ,
   l2_block_width: (bp_multicore_16_cce_ucode_override_p.l2_block_width == "inv") 
                 ? bp_multicore_16_cfg_p.l2_block_width           
                 : bp_multicore_16_cce_ucode_override_p.l2_block_width          
       
       ,
   l2_fill_width: (bp_multicore_16_cce_ucode_override_p.l2_fill_width == "inv") 
                 ? bp_multicore_16_cfg_p.l2_fill_width           
                 : bp_multicore_16_cce_ucode_override_p.l2_fill_width          
        
       ,
   l2_outstanding_reqs: (bp_multicore_16_cce_ucode_override_p.l2_outstanding_reqs == "inv") 
                 ? bp_multicore_16_cfg_p.l2_outstanding_reqs           
                 : bp_multicore_16_cce_ucode_override_p.l2_outstanding_reqs          
  
                                                                                                
       ,
   async_coh_clk: (bp_multicore_16_cce_ucode_override_p.async_coh_clk == "inv") 
                 ? bp_multicore_16_cfg_p.async_coh_clk           
                 : bp_multicore_16_cce_ucode_override_p.async_coh_clk          
        
       ,
   coh_noc_max_credits: (bp_multicore_16_cce_ucode_override_p.coh_noc_max_credits == "inv") 
                 ? bp_multicore_16_cfg_p.coh_noc_max_credits           
                 : bp_multicore_16_cce_ucode_override_p.coh_noc_max_credits          
  
       ,
   coh_noc_flit_width: (bp_multicore_16_cce_ucode_override_p.coh_noc_flit_width == "inv") 
                 ? bp_multicore_16_cfg_p.coh_noc_flit_width           
                 : bp_multicore_16_cce_ucode_override_p.coh_noc_flit_width          
   
       ,
   coh_noc_cid_width: (bp_multicore_16_cce_ucode_override_p.coh_noc_cid_width == "inv") 
                 ? bp_multicore_16_cfg_p.coh_noc_cid_width           
                 : bp_multicore_16_cce_ucode_override_p.coh_noc_cid_width          
    
       ,
   coh_noc_len_width: (bp_multicore_16_cce_ucode_override_p.coh_noc_len_width == "inv") 
                 ? bp_multicore_16_cfg_p.coh_noc_len_width           
                 : bp_multicore_16_cce_ucode_override_p.coh_noc_len_width          
    
                                                                                                
       ,
   async_mem_clk: (bp_multicore_16_cce_ucode_override_p.async_mem_clk == "inv") 
                 ? bp_multicore_16_cfg_p.async_mem_clk           
                 : bp_multicore_16_cce_ucode_override_p.async_mem_clk          
        
       ,
   mem_noc_max_credits: (bp_multicore_16_cce_ucode_override_p.mem_noc_max_credits == "inv") 
                 ? bp_multicore_16_cfg_p.mem_noc_max_credits           
                 : bp_multicore_16_cce_ucode_override_p.mem_noc_max_credits          
  
       ,
   mem_noc_flit_width: (bp_multicore_16_cce_ucode_override_p.mem_noc_flit_width == "inv") 
                 ? bp_multicore_16_cfg_p.mem_noc_flit_width           
                 : bp_multicore_16_cce_ucode_override_p.mem_noc_flit_width          
   
       ,
   mem_noc_cid_width: (bp_multicore_16_cce_ucode_override_p.mem_noc_cid_width == "inv") 
                 ? bp_multicore_16_cfg_p.mem_noc_cid_width           
                 : bp_multicore_16_cce_ucode_override_p.mem_noc_cid_width          
    
       ,
   mem_noc_len_width: (bp_multicore_16_cce_ucode_override_p.mem_noc_len_width == "inv") 
                 ? bp_multicore_16_cfg_p.mem_noc_len_width           
                 : bp_multicore_16_cce_ucode_override_p.mem_noc_len_width          
    
                                                                                                
       ,
   async_io_clk: (bp_multicore_16_cce_ucode_override_p.async_io_clk == "inv") 
                 ? bp_multicore_16_cfg_p.async_io_clk           
                 : bp_multicore_16_cce_ucode_override_p.async_io_clk          
         
       ,
   io_noc_max_credits: (bp_multicore_16_cce_ucode_override_p.io_noc_max_credits == "inv") 
                 ? bp_multicore_16_cfg_p.io_noc_max_credits           
                 : bp_multicore_16_cce_ucode_override_p.io_noc_max_credits          
   
       ,
   io_noc_flit_width: (bp_multicore_16_cce_ucode_override_p.io_noc_flit_width == "inv") 
                 ? bp_multicore_16_cfg_p.io_noc_flit_width           
                 : bp_multicore_16_cce_ucode_override_p.io_noc_flit_width          
    
       ,
   io_noc_cid_width: (bp_multicore_16_cce_ucode_override_p.io_noc_cid_width == "inv") 
                 ? bp_multicore_16_cfg_p.io_noc_cid_width           
                 : bp_multicore_16_cce_ucode_override_p.io_noc_cid_width          
     
       ,
   io_noc_did_width: (bp_multicore_16_cce_ucode_override_p.io_noc_did_width == "inv") 
                 ? bp_multicore_16_cfg_p.io_noc_did_width           
                 : bp_multicore_16_cce_ucode_override_p.io_noc_did_width          
     
       ,
   io_noc_len_width: (bp_multicore_16_cce_ucode_override_p.io_noc_len_width == "inv") 
                 ? bp_multicore_16_cfg_p.io_noc_len_width           
                 : bp_multicore_16_cce_ucode_override_p.io_noc_len_width          
     
       }
;

/* verilator lint_off WIDTH */
parameter bp_proc_param_s [max_cfgs-1:0] all_cfgs_gp =
{
 // L2 extension configurations
 bp_multicore_4_l2e_cfg_p
 ,bp_multicore_2_l2e_cfg_p
 ,bp_multicore_1_l2e_cfg_p

 // Accelerator configurations
 ,bp_multicore_4_acc_vdp_cfg_p
 ,bp_multicore_4_acc_scratchpad_cfg_p
 ,bp_multicore_1_acc_vdp_cfg_p
 ,bp_multicore_1_acc_scratchpad_cfg_p

 // Ucode configurations
 ,bp_multicore_16_cce_ucode_cfg_p
 ,bp_multicore_12_cce_ucode_cfg_p
 ,bp_multicore_8_cce_ucode_cfg_p
 ,bp_multicore_6_cce_ucode_cfg_p
 ,bp_multicore_4_cce_ucode_cfg_p
 ,bp_multicore_3_cce_ucode_cfg_p
 ,bp_multicore_2_cce_ucode_cfg_p
 ,bp_multicore_1_cce_ucode_megaparrot_cfg_p
 ,bp_multicore_1_cce_ucode_miniparrot_cfg_p
 ,bp_multicore_1_cce_ucode_cfg_p

 // Multicore configurations
 ,bp_multicore_16_cfg_p
 ,bp_multicore_12_cfg_p
 ,bp_multicore_8_cfg_p
 ,bp_multicore_6_cfg_p
 ,bp_multicore_4_cfg_p
 ,bp_multicore_3_cfg_p
 ,bp_multicore_2_cfg_p
 ,bp_multicore_1_megaparrot_cfg_p
 ,bp_multicore_1_miniparrot_cfg_p
 ,bp_multicore_1_cfg_p

 // Unicore configurations
 ,bp_unicore_megaparrot_cfg_p
 ,bp_unicore_miniparrot_cfg_p
 ,bp_unicore_tinyparrot_cfg_p
 ,bp_unicore_cfg_p

 // A custom BP configuration generated from Makefile
 ,bp_custom_cfg_p
 // The default BP
 ,bp_default_cfg_p
};
/* verilator lint_on WIDTH */

// This enum MUST be kept up to date with the parameter array above
typedef enum bit [lg_max_cfgs-1:0]
{
 // L2 extension configurations
 e_bp_multicore_4_l2e_cfg                        = 32
 ,e_bp_multicore_2_l2e_cfg                       = 31
 ,e_bp_multicore_1_l2e_cfg                       = 30

 // Accelerator configurations
 ,e_bp_multicore_4_acc_vdp_cfg                   = 29
 ,e_bp_multicore_4_acc_scratchpad_cfg            = 28
 ,e_bp_multicore_1_acc_vdp_cfg                   = 27
 ,e_bp_multicore_1_acc_scratchpad_cfg            = 26

 // Ucode configurations
 ,e_bp_multicore_16_cce_ucode_cfg                = 25
 ,e_bp_multicore_12_cce_ucode_cfg                = 24
 ,e_bp_multicore_8_cce_ucode_cfg                 = 23
 ,e_bp_multicore_6_cce_ucode_cfg                 = 22
 ,e_bp_multicore_4_cce_ucode_cfg                 = 21
 ,e_bp_multicore_3_cce_ucode_cfg                 = 20
 ,e_bp_multicore_2_cce_ucode_cfg                 = 19
 ,e_bp_multicore_1_cce_ucode_megaparrot_cfg      = 18
 ,e_bp_multicore_1_cce_ucode_miniparrot_cfg      = 17
 ,e_bp_multicore_1_cce_ucode_cfg                 = 16

 // Multicore configurations
 ,e_bp_multicore_16_cfg                          = 15
 ,e_bp_multicore_12_cfg                          = 14
 ,e_bp_multicore_8_cfg                           = 13
 ,e_bp_multicore_6_cfg                           = 12
 ,e_bp_multicore_4_cfg                           = 11
 ,e_bp_multicore_3_cfg                           = 10
 ,e_bp_multicore_2_cfg                           = 9
 ,e_bp_multicore_1_megaparrot_cfg                = 8
 ,e_bp_multicore_1_miniparrot_cfg                = 7
 ,e_bp_multicore_1_cfg                           = 6

 // Unicore configurations
 ,e_bp_unicore_megaparrot_cfg                    = 5
 ,e_bp_unicore_miniparrot_cfg                    = 4
 ,e_bp_unicore_tinyparrot_cfg                    = 3
 ,e_bp_unicore_cfg                               = 2

 // A custom BP configuration generated from `defines
 ,e_bp_custom_cfg                                = 1
 // The default BP
 ,e_bp_default_cfg                               = 0
} bp_params_e;









/*
* BedRock Interface Enum Definitions
*
* These enums define the options for fields of the BedRock Interface messages. Clients should use
* the enums to set and compare fields of messages, rather than examining the bit pattern directly.
*/

/*
* bp_bedrock_msg_size_e specifies the amount of data in the message, after the header
*
* Note: these enum values are fixed and should not be changed. This allows easily computing
*  number of bytes in message = N bytes = (1 << e_bedrock_msg_size_N)
*/
typedef enum logic [2:0]
{
 e_bedrock_msg_size_1     = 3'b000 // 1 byte
 ,e_bedrock_msg_size_2    = 3'b001 // 2 bytes
 ,e_bedrock_msg_size_4    = 3'b010 // 4 bytes
 ,e_bedrock_msg_size_8    = 3'b011 // 8 bytes
 ,e_bedrock_msg_size_16   = 3'b100 // 16 bytes
 ,e_bedrock_msg_size_32   = 3'b101 // 32 bytes
 ,e_bedrock_msg_size_64   = 3'b110 // 64 bytes
 ,e_bedrock_msg_size_128  = 3'b111 // 128 bytes
} bp_bedrock_msg_size_e;

/*
* bp_bedrock_fwd_type_e specifies the memory command from the UCE/CCE
*
* There are three types of commands:
* 1. Access to memory that should be cached in L2/LLC (rd/wr)
* 2. Access to memory that should remain uncached by L2/LLC (uc_rd/uc_wr)
* 3. Prefetch access to memory that should be cached in L2/LLC (pre)
*
* Cacheability of the data at the L1/LCE level is determined by the uncached bit within
* the payload of the message, and is managed by the LCE/CCE. This information is not
* exposed to memory/L2/LLC, allowing the CCE to maintain coherence for all required
* blocks.
*
*/
typedef enum logic [3:0]
{
 e_bedrock_mem_rd       = 4'b0000 // Cache block fetch / load / Get (cached in L2/LLC)
 ,e_bedrock_mem_wr      = 4'b0001 // Cache block write / writeback / store / Put (cached in L2/LLC)
 ,e_bedrock_mem_uc_rd   = 4'b0010 // Uncached load (uncached in L2/LLC)
 ,e_bedrock_mem_uc_wr   = 4'b0011 // Uncached store (uncached in L2/LLC)
 ,e_bedrock_mem_pre     = 4'b0100 // Pre-fetch block request from CCE, fill into L2/LLC if able
 ,e_bedrock_mem_amo     = 4'b0101 // Atomic operation in L2/LLC
} bp_bedrock_fwd_type_e;

// rev messages are identical to fwd messages and can be safely casted between
typedef bp_bedrock_fwd_type_e bp_bedrock_rev_type_e;

/*
* bp_bedrock_req_type_e specifies whether the containing message is related to a read or write
* cache miss request from and LCE.
*/
typedef enum logic [3:0]
{
 e_bedrock_req_rd_miss    = 4'b0000 // Read-miss
 ,e_bedrock_req_wr_miss   = 4'b0001 // Write-miss
 ,e_bedrock_req_uc_rd     = 4'b0010 // Uncached Read
 ,e_bedrock_req_uc_wr     = 4'b0011 // Uncached Write
 ,e_bedrock_req_uc_amo    = 4'b0100 // AMO
} bp_bedrock_req_type_e;

/*
* bp_bedrock_wr_subop_e specifies the type of store
* Valid only for
* req: e_bedrock_req_uc_wr, e_bedrock_req_uc_amo
* mem_fwd: e_bedrock_mem_uc_wr, e_bedrock_mem_amo
*/
typedef enum logic [3:0]
{
 e_bedrock_store            = 4'b0000
 ,e_bedrock_amolr           = 4'b0001
 ,e_bedrock_amosc           = 4'b0010
 ,e_bedrock_amoswap         = 4'b0011
 ,e_bedrock_amoadd          = 4'b0100
 ,e_bedrock_amoxor          = 4'b0101
 ,e_bedrock_amoand          = 4'b0110
 ,e_bedrock_amoor           = 4'b0111
 ,e_bedrock_amomin          = 4'b1000
 ,e_bedrock_amomax          = 4'b1001
 ,e_bedrock_amominu         = 4'b1010
 ,e_bedrock_amomaxu         = 4'b1011
} bp_bedrock_wr_subop_e;


/*
* bp_bedrock_cmd_type_e defines commands from CCE to LCE
*/
typedef enum logic [3:0]
{
 e_bedrock_cmd_sync             = 4'b0000 // sync/ready, respond with sync_ack
 ,e_bedrock_cmd_set_clear       = 4'b0001 // clear cache set of address field
 ,e_bedrock_cmd_inv             = 4'b0010 // invalidate block, respond with inv_ack
 ,e_bedrock_cmd_st              = 4'b0011 // set state
 ,e_bedrock_cmd_data            = 4'b0100 // data, adddress, and state to LCE, i.e., cache block fill
 ,e_bedrock_cmd_st_wakeup       = 4'b0101 // set state and wakeup (upgrade response, state only)
 ,e_bedrock_cmd_wb              = 4'b0110 // writeback block
 ,e_bedrock_cmd_st_wb           = 4'b0111 // set state and writeback block
 ,e_bedrock_cmd_tr              = 4'b1000 // transfer block
 ,e_bedrock_cmd_st_tr           = 4'b1001 // set state and transfer block
 ,e_bedrock_cmd_st_tr_wb        = 4'b1010 // set state, transfer, and writeback block
 ,e_bedrock_cmd_uc_data         = 4'b1011 // uncached data
 ,e_bedrock_cmd_uc_st_done      = 4'b1100 // uncached request complete
} bp_bedrock_cmd_type_e;

/*
* bp_bedrock_fill_type_e defines LCE to LCE messages
*/
typedef enum logic [3:0]
{
 e_bedrock_fill_data            = e_bedrock_cmd_data // data, adddress, and state to LCE, i.e., cache block fill
} bp_bedrock_fill_type_e;

/*
* bp_bedrock_resp_type_e defines the different LCE-CCE response messages
*/
typedef enum logic [3:0]
{
 e_bedrock_resp_sync_ack    = 4'b0000 // ack to sync command. LCE is ready for cacheable operation
 ,e_bedrock_resp_inv_ack    = 4'b0001 // ack to invalidate. Block is now invalid at LCE
 ,e_bedrock_resp_coh_ack    = 4'b0010 // ack that coherence request is complete
 ,e_bedrock_resp_wb         = 4'b0011 // Normal Writeback Response (full data)
 ,e_bedrock_resp_null_wb    = 4'b0100 // Null Writeback Response (no data)
} bp_bedrock_resp_type_e;

/*
* bp_bedrock_msg_u is a union that holds the LCE-CCE Req, Cmd, and Resp message types
*/
typedef union packed
{
 bp_bedrock_req_type_e    req;
 bp_bedrock_cmd_type_e    cmd;
 bp_bedrock_fill_type_e   fill;
 bp_bedrock_resp_type_e   resp;
 bp_bedrock_fwd_type_e    fwd;
 bp_bedrock_rev_type_e    rev;
} bp_bedrock_msg_u;

/*
* bp_bedrock_req_non_excl_e specifies whether the requesting LCE would like a read-miss request
* to be returned in an exclusive coherence state if possible or not. An I$, for example, should
* set this bit to indicate that there is no benefit in the CCE granting a cache block in the E
* state as opposed to the S state in a MESI protocol. The CCE treats this bit as a hint, and is
* not required to follow it.
*/
typedef enum logic
{
 e_bedrock_req_excl            = 1'b0 // exclusive cache line request (read-only, exclusive request)
 ,e_bedrock_req_non_excl       = 1'b1 // non-exclusive cache line request (read-only, shared request)
} bp_bedrock_req_non_excl_e;

/*
* bp_cce_coh_states_e defines the coherence states available in BlackParrot. Each bit represents
* a property of the cache block as defined below:
* 0: Shared (not Exclusive)
* 1: Owned
* 2: Potentially Dirty
*
* These properties are derived from "A Primer on Memory Consistency and Cache Coherence", and
* they allow an easy definition for the common MOESIF coherence states.
*/
typedef enum logic [2:0]
{
 e_COH_I                   = 3'b000 // Invalid
 ,e_COH_S                  = 3'b001 // Shared - clean, not owned, shared (not exclusive)
 ,e_COH_E                  = 3'b010 // Exclusive - clean, owned, not shared (exclusive)
 ,e_COH_F                  = 3'b011 // Forward - clean, owned, shared (not exclusive)
 // unused                 = 3'b100 // potentially dirty, not owned, not shared (exclusive)
 // unused                 = 3'b101 // potentially dirty, not owned, shared (not exclusive)
 ,e_COH_M                  = 3'b110 // Modified - potentially dirty, owned, not shared (exclusive)
 ,e_COH_O                  = 3'b111 // Owned - potentially dirty, owned, shared (not exclusive)
} bp_coh_states_e;

/*
* payload mask parameters
*
* These masks define the BedRock message types that carry data.
*
*/
localparam mem_fwd_payload_mask_gp  = (1 << e_bedrock_mem_uc_wr) | (1 << e_bedrock_mem_wr) | (1 << e_bedrock_mem_amo);
localparam mem_rev_payload_mask_gp = (1 << e_bedrock_mem_uc_rd) | (1 << e_bedrock_mem_rd) | (1 << e_bedrock_mem_amo);
localparam lce_req_payload_mask_gp = (1 << e_bedrock_req_uc_wr) | (1 << e_bedrock_req_uc_amo);
localparam lce_cmd_payload_mask_gp = (1 << e_bedrock_cmd_data) | (1 << e_bedrock_cmd_uc_data);
localparam lce_fill_payload_mask_gp = (1 << e_bedrock_fill_data);
localparam lce_resp_payload_mask_gp = (1 << e_bedrock_resp_wb);








localparam cache_base_addr_gp   = (dev_id_width_gp+dev_addr_width_gp)'('h0400_0000);
localparam cache_tagfl_addr_gp  = (dev_addr_width_gp)'('h0_0000);








typedef enum logic [3:0]
{
 e_miss_load         = 4'b0000
 ,e_miss_store       = 4'b0001
 ,e_wt_store         = 4'b0010
 ,e_uc_load          = 4'b0011
 ,e_uc_store         = 4'b0100
 ,e_uc_amo           = 4'b0101
 ,e_cache_flush      = 4'b0110
 ,e_cache_clear      = 4'b0111
} bp_cache_req_msg_type_e;

typedef enum logic [2:0]
{
 e_size_1B    = 3'b000
 ,e_size_2B   = 3'b001
 ,e_size_4B   = 3'b010
 ,e_size_8B   = 3'b011
 ,e_size_16B  = 3'b100
 ,e_size_32B  = 3'b101
 ,e_size_64B  = 3'b110
} bp_cache_req_size_e;

// Relevant for uc_store and uc_amo
typedef enum logic [3:0]
{
 // Return value of e_req_store is undefined, clients should not
 //   depend on it being zero
 e_req_store    = 4'b0000
 ,e_req_amolr   = 4'b0001
 ,e_req_amosc   = 4'b0010
 ,e_req_amoswap = 4'b0011
 ,e_req_amoadd  = 4'b0100
 ,e_req_amoxor  = 4'b0101
 ,e_req_amoand  = 4'b0110
 ,e_req_amoor   = 4'b0111
 ,e_req_amomin  = 4'b1000
 ,e_req_amomax  = 4'b1001
 ,e_req_amominu = 4'b1010
 ,e_req_amomaxu = 4'b1011
} bp_cache_req_wr_subop_e;








// LCE Operating Mode
// e_lce_mode_uncached: Cache treats all requests as uncached
// e_lce_mode_normal: Cache acts normally
// e_lce_mode_nonspec: Cache acts mostly normally, but will not send a speculative miss
typedef enum logic [1:0]
{
 e_lce_mode_uncached = 0
 ,e_lce_mode_normal  = 1
 ,e_lce_mode_nonspec = 2
} bp_lce_mode_e;

// CCE Operating Mode
// e_cce_mode_uncached: CCE supports uncached requests only
// e_cce_mode_normal: CCE supports cacheable requests
typedef enum logic
{
 e_cce_mode_uncached = 0
 ,e_cce_mode_normal  = 1
} bp_cce_mode_e;

// The overall memory map of the config link is:
//   16'h0000 - 16'h01ff: chip level config
//   16'h0200 - 16'h03ff: fe config
//   16'h0400 - 16'h05ff: be config
//   16'h0600 - 16'h07ff: me config
//   16'h0800 - 16'h7fff: reserved
//   16'h8000 - 16'h8fff: cce ucode

localparam cfg_base_addr_gp           = (dev_id_width_gp+dev_addr_width_gp)'('h0020_0000);
localparam cfg_match_addr_gp          = (dev_id_width_gp+dev_addr_width_gp)'('h002?_????);

localparam cfg_reg_freeze_gp          = (dev_addr_width_gp)'('h0_0008);
localparam cfg_reg_npc_gp             = (dev_addr_width_gp)'('h0_0010);
localparam cfg_reg_core_id_gp         = (dev_addr_width_gp)'('h0_0018);
localparam cfg_reg_did_gp             = (dev_addr_width_gp)'('h0_0020);
localparam cfg_reg_cord_gp            = (dev_addr_width_gp)'('h0_0028);
localparam cfg_reg_host_did_gp        = (dev_addr_width_gp)'('h0_0030);
// Used until PMP are setup properly
localparam cfg_reg_hio_mask_gp        = (dev_addr_width_gp)'('h0_0038);
localparam cfg_reg_icache_id_gp       = (dev_addr_width_gp)'('h0_0200);
localparam cfg_reg_icache_mode_gp     = (dev_addr_width_gp)'('h0_0208);
localparam cfg_reg_dcache_id_gp       = (dev_addr_width_gp)'('h0_0400);
localparam cfg_reg_dcache_mode_gp     = (dev_addr_width_gp)'('h0_0408);
localparam cfg_reg_cce_id_gp          = (dev_addr_width_gp)'('h0_0600);
localparam cfg_reg_cce_mode_gp        = (dev_addr_width_gp)'('h0_0608);
localparam cfg_mem_cce_ucode_base_gp  = (dev_addr_width_gp)'('h0_8000);
localparam cfg_mem_cce_ucode_match_gp = (dev_addr_width_gp)'('h0_8???);









localparam clint_base_addr_gp         = (dev_id_width_gp+dev_addr_width_gp)'('h30_0000);
localparam clint_match_addr_gp        = (dev_id_width_gp+dev_addr_width_gp)'('h30_0???);

localparam mipi_reg_base_addr_gp      = dev_addr_width_gp'('h0_0000);
localparam mipi_reg_match_addr_gp     = dev_addr_width_gp'('h0_0???);

localparam mtimecmp_reg_base_addr_gp  = dev_addr_width_gp'('h0_4000);
localparam mtimecmp_reg_match_addr_gp = dev_addr_width_gp'('h0_4???);

localparam mtimesel_reg_base_addr_gp  = dev_addr_width_gp'('h0_8000);
localparam mtimesel_reg_match_addr_gp = dev_addr_width_gp'('h0_8???);

localparam mtime_reg_addr_gp          = dev_addr_width_gp'('h0_bff8);
localparam mtime_reg_match_addr_gp    = dev_addr_width_gp'('h0_bff?);

localparam plic_reg_base_addr_gp      = dev_addr_width_gp'('h0_b000);
localparam plic_reg_match_addr_gp     = dev_addr_width_gp'('h0_b00?);

localparam debug_reg_base_addr_gp     = dev_addr_width_gp'('h0_c000);
localparam debug_reg_match_addr_gp    = dev_addr_width_gp'('h0_c???);








/*
* bp_fe_command_queue_opcodes_e defines the opcodes from backend to frontend in
* the cases of an exception. bp_fe_command_queue_opcodes_e explains the reason
* of why pc is redirected. Only e_op_pc_redirection contains possible at-fault
* redirections
* e_op_state_reset is used after the reset, which flushes all the states.
* e_op_pc_redirection defines the changes of PC, which happens during the branches.
* e_op_attaboy informs the frontend that the prediction is correct.
* e_op_icache_fill_restart happens when icache non-speculatively misses
* e_op_icache_fill_resume happens when icache non-speculatively misses and refetches
* e_op_icache_fence happens when there is flush in the icache.
* e_op_itlb_fill_restart happens when itlb populates translation and restarts fetching
* e_op_itlb_fill_resume happens when itlb populates translation and resumes fetching 
* e_op_itlb_fence issues a fence operation to itlb.
*/
typedef enum logic [3:0]
{
 e_op_state_reset           = 0
 ,e_op_pc_redirection       = 1
 ,e_op_attaboy              = 2
 ,e_op_icache_fill_restart  = 3
 ,e_op_icache_fill_resume   = 4
 ,e_op_icache_fence         = 5
 ,e_op_itlb_fill_restart    = 6
 ,e_op_itlb_fill_resume     = 7
 ,e_op_itlb_fence           = 8
 ,e_op_wait                 = 9
} bp_fe_command_queue_opcodes_e;

/*
* bp_fe_misprediction_reason_e is the misprediction reason provided by the backend.
*/
typedef enum logic [1:0]
{
 e_not_a_branch           = 0
 ,e_incorrect_pred_taken  = 1
 ,e_incorrect_pred_ntaken = 2
} bp_fe_misprediction_reason_e;

/*
* The exception code types.
* e_itlb_miss is for an ITLB miss
* e_instr_page_fault is for an access page fault
* e_instr_access_fault is when the physical address is not allowed for the access type
* e_icache_miss is for a nonspeculative I$ miss which needs to be confirmed by the backend
*/
typedef enum logic [2:0]
{
 e_itlb_miss            = 0
 ,e_instr_page_fault    = 1
 ,e_instr_access_fault  = 2
 ,e_icache_miss         = 3
 ,e_instr_fetch         = 4
} bp_fe_queue_type_e;

/*
* bp_fe_command_queue_subopcodes_e defines the subopcodes in the case of pc_redirection in
* bp_fe_command_queue_opcodes_e. It provides the reasons of why pc are redirected.
* e_subop_uret,sret,mret are the returns from trap and contain the pc where it returns.
* e_subop_interrupt is no-fault pc redirection.
* e_subop_branch_mispredict is at-fault PC redirection.
* e_subop_trap is at-fault PC redirection. It will changes the permission bits.
* e_subop_context_switch is no-fault PC redirection. It redirect pc to a new address space.
* e_subop_translation_switch is no-fault PC redirection resulting from translation mode changes
*/
typedef enum logic [2:0]
{
 e_subop_eret
 ,e_subop_interrupt
 ,e_subop_branch_mispredict
 ,e_subop_trap
 ,e_subop_context_switch
 ,e_subop_translation_switch
} bp_fe_command_queue_subopcodes_e;








localparam dword_width_gp       = 64;
localparam word_width_gp        = 32;
localparam half_width_gp        = 16;
localparam byte_width_gp        = 8;
localparam hinstr_width_gp      = 16;
localparam instr_width_gp       = 32;
localparam csr_addr_width_gp    = 12;
localparam reg_addr_width_gp    = 5;
localparam page_offset_width_gp = 12;

localparam rv64_rf_els_gp         = 32;
localparam rv64_instr_width_gp    = 32;
localparam rv64_eaddr_width_gp    = 64;
localparam rv64_byte_width_gp     = 8;
localparam rv64_hword_width_gp    = 16;
localparam rv64_word_width_gp     = 32;
localparam rv64_dword_width_gp    = 64;
localparam rv64_reg_data_width_gp = 64;
localparam rv64_reg_addr_width_gp = 5;
localparam rv64_shamt_width_gp    = 6;
localparam rv64_shamtw_width_gp   = 5;
localparam rv64_opcode_width_gp   = 7;
localparam rv64_funct3_width_gp   = 3;
localparam rv64_funct7_width_gp   = 7;
localparam rv64_csr_addr_width_gp = 12;
localparam rv64_imm20_width_gp    = 20;
localparam rv64_imm12_width_gp    = 12;
localparam rv64_imm11to5_width_gp = 7;
localparam rv64_imm4to0_width_gp  = 5;
localparam rv64_priv_width_gp     = 2;

typedef struct packed
{
 logic [rv64_funct7_width_gp-1:0]   funct7;
 logic [rv64_reg_addr_width_gp-1:0] rs2_addr;
 logic [rv64_reg_addr_width_gp-1:0] rs1_addr;
 logic [rv64_funct3_width_gp-1:0]   funct3;
 logic [rv64_reg_addr_width_gp-1:0] rd_addr;
 logic [rv64_opcode_width_gp-1:0]   opcode;
}  rv64_instr_rtype_s;

typedef struct packed
{
 logic [rv64_reg_addr_width_gp-1:0] rs3_addr;
 logic [1:0]                        fmt;
 logic [rv64_reg_addr_width_gp-1:0] rs2_addr;
 logic [rv64_reg_addr_width_gp-1:0] rs1_addr;
 logic [2:0]                        rm;
 logic [rv64_reg_addr_width_gp-1:0] rd_addr;
 logic [rv64_opcode_width_gp-1:0]   opcode;
}  rv64_instr_fmatype_s;

typedef struct packed
{
 logic [rv64_funct7_width_gp-1:0]   funct7;
 logic [rv64_reg_addr_width_gp-1:0] rs2_addr;
 logic [rv64_reg_addr_width_gp-1:0] rs1_addr;
 logic [2:0]                        rm;
 logic [rv64_reg_addr_width_gp-1:0] rd_addr;
 logic [rv64_opcode_width_gp-1:0]   opcode;
}  rv64_instr_ftype_s;

typedef struct packed
{
 logic [rv64_imm12_width_gp-1:0]    imm12;
 logic [rv64_reg_addr_width_gp-1:0] rs1;
 logic [rv64_funct3_width_gp-1:0]   funct3;
 logic [rv64_reg_addr_width_gp-1:0] rd_addr;
 logic [rv64_opcode_width_gp-1:0]   opcode;
}  rv64_instr_itype_s;

typedef struct packed
{
 logic [rv64_imm11to5_width_gp-1:0] imm11to5;
 logic [rv64_reg_addr_width_gp-1:0] rs2;
 logic [rv64_reg_addr_width_gp-1:0] rs1;
 logic [rv64_funct3_width_gp-1:0]   funct3;
 logic [rv64_imm4to0_width_gp-1:0]  imm4to0;
 logic [rv64_opcode_width_gp-1:0]   opcode;
}  rv64_instr_stype_s;

typedef struct packed
{
 logic [rv64_imm20_width_gp-1:0]    imm20;
 logic [rv64_reg_addr_width_gp-1:0] rd_addr;
 logic [rv64_opcode_width_gp-1:0]   opcode;
}  rv64_instr_utype_s;

typedef struct packed
{
 logic                              imm12;
 logic [10:5]                       imm10to5;
 logic [rv64_reg_addr_width_gp-1:0] rs2;
 logic [rv64_reg_addr_width_gp-1:0] rs1;
 logic [rv64_funct3_width_gp-1:0]   funct3;
 logic [4:1]                        imm4to1;
 logic                              imm11;
 logic [rv64_opcode_width_gp-1:0]   opcode;
}  rv64_instr_btype_s;

typedef struct packed
{
 union packed
 {
   rv64_instr_rtype_s    rtype;
   rv64_instr_fmatype_s  fmatype;
   rv64_instr_ftype_s    ftype;
   rv64_instr_itype_s    itype;
   rv64_instr_stype_s    stype;
   rv64_instr_utype_s    utype;
   rv64_instr_btype_s    btype;
 }  t;
}  rv64_instr_s;

typedef struct packed
{
 // RISC-V exceptions
 logic store_page_fault;
 logic reserved2;
 logic load_page_fault;
 logic instr_page_fault;
 logic ecall_m_mode;
 logic reserved1;
 logic ecall_s_mode;
 logic ecall_u_mode;
 logic store_access_fault;
 logic store_misaligned;
 logic load_access_fault;
 logic load_misaligned;
 logic breakpoint;
 logic illegal_instr;
 logic instr_access_fault;
 logic instr_misaligned;
}  rv64_exception_dec_s;

typedef enum logic [2:0]
{
 e_rne   = 3'b000
 ,e_rtz  = 3'b001
 ,e_rdn  = 3'b010
 ,e_rup  = 3'b011
 ,e_rmm  = 3'b100
 // 3'b101, 3'b110 reserved
 ,e_dyn  = 3'b111
} rv64_frm_e;

typedef enum logic
{
 e_fmt_single  = 1'b0
 ,e_fmt_double = 1'b1
} rv64_fmt_e;

typedef struct packed
{
 // Invalid operation
 logic nv;
 // Divide by zero
 logic dz;
 // Overflow
 logic of;
 // Underflow
 logic uf;
 // Inexact
 logic nx;
}  rv64_fflags_s;

typedef struct packed
{
 // Invalid operation
 logic nv;
 // Overflow
 logic of;
 // Inexact
 logic nx;
}  rv64_iflags_s;

typedef struct packed
{
 logic [53:0] padding;
 logic        q_nan;
 logic        s_nan;
 logic        p_inf;
 logic        p_norm;
 logic        p_sub;
 logic        p_zero;
 logic        n_zero;
 logic        n_sub;
 logic        n_norm;
 logic        n_inf;
}  rv64_fclass_s;

/*
* RV64 specifies a 64b effective address and 32b instruction.
* BlackParrot supports SV39 virtual memory, which specifies 39b virtual / 56b physical address.
* Effective addresses must have bits 39-63 match bit 38
*   or a page fault exception will occur during translation.
* Currently, we only support a very limited number of parameter configurations.
* Thought: We could have a `define surrounding core instantiations of each parameter and then
* when they import this package, `declare the if structs. No more casting!
*/

localparam sv39_pte_width_gp          = 64;
localparam sv39_levels_gp             = 3;
localparam sv39_vaddr_width_gp        = 39;
localparam sv39_paddr_width_gp        = 56;
localparam sv39_ppn_width_gp          = 44;
localparam sv39_page_idx_width_gp     = 9;
localparam sv39_page_offset_width_gp  = 12;
localparam sv39_page_size_in_bytes_gp = 1 << sv39_page_offset_width_gp;
localparam sv39_pte_size_in_bytes_gp  = 8;

typedef struct packed
{
 logic [sv39_pte_width_gp-10-sv39_ppn_width_gp-1:0] reserved;
 logic [sv39_ppn_width_gp-1:0] ppn;
 logic [1:0] rsw;
 logic d;
 logic a;
 logic g;
 logic u;
 logic x;
 logic w;
 logic r;
 logic v;
}  sv39_pte_s;

endpackage



package bp_be_pkg;

  import bp_common_pkg::*;

  localparam sp_float_width_gp = 32;
  localparam sp_rec_width_gp   = 33;
  localparam sp_exp_width_gp   = 8;
  localparam sp_sig_width_gp   = 24;

  localparam dp_float_width_gp = 64;
  localparam dp_rec_width_gp   = 65;
  localparam dp_exp_width_gp   = 11;
  localparam dp_sig_width_gp   = 53;

  localparam [dp_float_width_gp-1:0] dp_canonical_nan = 64'h7ff80000_00000000;
  localparam [dp_float_width_gp-1:0] sp_canonical_nan = 64'hffffffff_7fc00000;

  localparam [dp_rec_width_gp-1:0] dp_rec_1_0 = 65'h0_80000000_00000000;
  localparam [dp_rec_width_gp-1:0] dp_rec_0_0 = 65'h0_00000000_00000000;

  localparam [dp_rec_width_gp-1:0] dp_canonical_rec = 65'h0_e0080000_00000000;

  typedef enum logic [2:0]
  {
    e_fp_rne     = 3'b000
    ,e_fp_rtz    = 3'b001
    ,e_fp_rdn    = 3'b010
    ,e_fp_rup    = 3'b011
    ,e_fp_rmm    = 3'b100
    ,e_fp_full   = 3'b111
  } bp_be_fp_tag_e;

  typedef struct packed
  {
    logic                       sign;
    logic [sp_exp_width_gp:0]   exp;
    logic [sp_sig_width_gp-2:0] fract;
  }  bp_hardfloat_rec_sp_s;

  typedef struct packed
  {
    logic                       sign;
    logic [dp_exp_width_gp:0]   exp;
    logic [dp_sig_width_gp-2:0] fract;
  }  bp_hardfloat_rec_dp_s;

  typedef struct packed
  {
    logic [2:0]           tag;
    bp_hardfloat_rec_dp_s rec;
  }  bp_be_fp_reg_s;

  localparam dpath_width_gp = $bits(bp_be_fp_reg_s);

  



  typedef enum logic [5:0]
  {
    e_ctrl_op_beq       = 6'b000000
    ,e_ctrl_op_bne      = 6'b000001
    ,e_ctrl_op_blt      = 6'b000010
    ,e_ctrl_op_bltu     = 6'b000011
    ,e_ctrl_op_bge      = 6'b000100
    ,e_ctrl_op_bgeu     = 6'b000101
    ,e_ctrl_op_jal      = 6'b000110
    ,e_ctrl_op_jalr     = 6'b000111
  } bp_be_ctrl_fu_op_e;

  typedef enum logic [5:0]
  {
    e_int_op_add        = 6'b000000
    ,e_int_op_sub       = 6'b001000
    ,e_int_op_sll       = 6'b000001
    ,e_int_op_slt       = 6'b000010
    ,e_int_op_sge       = 6'b001010
    ,e_int_op_sltu      = 6'b000011
    ,e_int_op_sgeu      = 6'b001011
    ,e_int_op_xor       = 6'b000100
    ,e_int_op_eq        = 6'b001100
    ,e_int_op_srl       = 6'b000101
    ,e_int_op_sra       = 6'b001101
    ,e_int_op_or        = 6'b000110
    ,e_int_op_ne        = 6'b001110
    ,e_int_op_and       = 6'b000111
    ,e_int_op_pass_src2 = 6'b001111
  } bp_be_int_fu_op_e;

  typedef enum logic [5:0]
  {
    // Movement instructions
    e_aux_op_f2f        = 6'b000000
    ,e_aux_op_f2i       = 6'b000001
    ,e_aux_op_i2f       = 6'b000010
    ,e_aux_op_f2iu      = 6'b000011
    ,e_aux_op_iu2f      = 6'b000100
    ,e_aux_op_imvf      = 6'b000101
    ,e_aux_op_fmvi      = 6'b000110
    ,e_aux_op_fsgnj     = 6'b000111
    ,e_aux_op_fsgnjn    = 6'b001000
    ,e_aux_op_fsgnjx    = 6'b001001

    // FCMP instructions
    ,e_aux_op_feq       = 6'b001010
    ,e_aux_op_flt       = 6'b001011
    ,e_aux_op_fle       = 6'b001100
    ,e_aux_op_fmax      = 6'b001101
    ,e_aux_op_fmin      = 6'b001110
    ,e_aux_op_fclass    = 6'b001111
  } bp_be_aux_fu_op_e;

  typedef enum logic [5:0]
  {
    e_dcache_op_lb        = 6'b000000
    ,e_dcache_op_lh       = 6'b000001
    ,e_dcache_op_lw       = 6'b000010
    ,e_dcache_op_ld       = 6'b000011
    ,e_dcache_op_lbu      = 6'b000100
    ,e_dcache_op_lhu      = 6'b000101
    ,e_dcache_op_lwu      = 6'b000110

    ,e_dcache_op_sb       = 6'b001000
    ,e_dcache_op_sh       = 6'b001001
    ,e_dcache_op_sw       = 6'b001010
    ,e_dcache_op_sd       = 6'b001011

    ,e_dcache_op_lrw      = 6'b000111
    ,e_dcache_op_scw      = 6'b001100

    ,e_dcache_op_lrd      = 6'b001101
    ,e_dcache_op_scd      = 6'b001110

    ,e_dcache_op_flw      = 6'b100010
    ,e_dcache_op_fld      = 6'b100011

    ,e_dcache_op_fsw      = 6'b100100
    ,e_dcache_op_fsd      = 6'b100101

    ,e_dcache_op_amoswapw = 6'b010000
    ,e_dcache_op_amoaddw  = 6'b010001
    ,e_dcache_op_amoxorw  = 6'b010010
    ,e_dcache_op_amoandw  = 6'b010011
    ,e_dcache_op_amoorw   = 6'b010100
    ,e_dcache_op_amominw  = 6'b010101
    ,e_dcache_op_amomaxw  = 6'b010110
    ,e_dcache_op_amominuw = 6'b010111
    ,e_dcache_op_amomaxuw = 6'b011000

    ,e_dcache_op_amoswapd = 6'b011001
    ,e_dcache_op_amoaddd  = 6'b011010
    ,e_dcache_op_amoxord  = 6'b011011
    ,e_dcache_op_amoandd  = 6'b011100
    ,e_dcache_op_amoord   = 6'b011101
    ,e_dcache_op_amomind  = 6'b011110
    ,e_dcache_op_amomaxd  = 6'b011111
    ,e_dcache_op_amominud = 6'b100000
    ,e_dcache_op_amomaxud = 6'b100001

    ,e_dcache_op_fencei   = 6'b111111
  } bp_be_dcache_fu_op_e;

  typedef enum logic [5:0]
  {
    e_csrr    = 6'b000000
    ,e_csrrw  = 6'b000001
    ,e_csrrs  = 6'b000010
    ,e_csrrc  = 6'b000011
    ,e_csrrwi = 6'b000100
    ,e_csrrsi = 6'b000101
    ,e_csrrci = 6'b000110
  } bp_be_csr_fu_op_e;

  typedef enum logic [5:0]
  {
    e_fma_op_fadd    = 6'b000000
    ,e_fma_op_fsub   = 6'b000001
    ,e_fma_op_fmul   = 6'b000010
    ,e_fma_op_fmadd  = 6'b000011
    ,e_fma_op_fmsub  = 6'b000100
    ,e_fma_op_fnmsub = 6'b000101
    ,e_fma_op_fnmadd = 6'b000110
    ,e_fma_op_imul   = 6'b000111
    ,e_fma_op_fdiv   = 6'b001000
    ,e_fma_op_fsqrt  = 6'b001001
  } bp_be_fma_fu_op_e;

  typedef enum logic [5:0]
  {
    e_mul_op_mul        = 6'b000000
    ,e_mul_op_div       = 6'b000001
    ,e_mul_op_divu      = 6'b000010
    ,e_mul_op_rem       = 6'b000011
    ,e_mul_op_remu      = 6'b000100
    ,e_mul_op_mulh      = 6'b000101
    ,e_mul_op_mulhsu    = 6'b000110
    ,e_mul_op_mulhu     = 6'b000111
  } bp_be_mul_fu_op_e;

  typedef struct packed
  {
    union packed
    {
      bp_be_ctrl_fu_op_e     ctrl_fu_op;
      bp_be_aux_fu_op_e      aux_fu_op;
      bp_be_int_fu_op_e      int_fu_op;
      bp_be_dcache_fu_op_e   dcache_op;
      bp_be_csr_fu_op_e      csr_fu_op;
      bp_be_fma_fu_op_e      fma_fu_op;
      bp_be_mul_fu_op_e      mul_fu_op;
    }  fu_op;
  }  bp_be_fu_op_s;

  typedef enum logic
  {
    e_src1_is_rs1 = 1'b0
    ,e_src1_is_pc = 1'b1
  } bp_be_src1_e;

  typedef enum logic
  {
    e_src2_is_rs2  = 1'b0
    ,e_src2_is_imm = 1'b1
  } bp_be_src2_e;

  typedef enum logic
  {
    e_baddr_is_pc   = 1'b0
    ,e_baddr_is_rs1 = 1'b1
  } bp_be_baddr_e;

  typedef enum logic
  {
    e_offset_is_imm   = 1'b0
    ,e_offset_is_zero = 1'b1
  } bp_be_offset_e;

  typedef enum logic
  {
    e_result_from_alu       = 1'b0
    ,e_result_from_pc_plus4 = 1'b1
  } bp_be_result_e;

  typedef struct packed
  {
    logic                             pipe_ctl_v;
    logic                             pipe_int_v;
    logic                             pipe_mem_early_v;
    logic                             pipe_aux_v;
    logic                             pipe_mem_final_v;
    logic                             pipe_sys_v;
    logic                             pipe_mul_v;
    logic                             pipe_fma_v;
    logic                             pipe_long_v;

    logic                             irf_w_v;
    logic                             frf_w_v;
    logic                             fflags_w_v;
    logic                             dcache_r_v;
    logic                             dcache_w_v;
    logic                             late_iwb_v;
    logic                             late_fwb_v;
    logic                             csr_w_v;
    logic                             csr_r_v;
    logic                             mem_v;
    logic                             opw_v;
    logic                             ops_v;

    bp_be_fu_op_s                     fu_op;

    bp_be_src1_e                      src1_sel;
    bp_be_src2_e                      src2_sel;
    bp_be_baddr_e                     baddr_sel;
  }  bp_be_decode_s;

  typedef struct packed
  {
    // True exceptions
    logic store_page_fault;
    logic load_page_fault;
    logic instr_page_fault;
    logic ecall_m;
    logic ecall_s;
    logic ecall_u;
    logic store_access_fault;
    logic store_misaligned;
    logic load_access_fault;
    logic load_misaligned;
    logic ebreak;
    logic illegal_instr;
    logic instr_access_fault;
    logic instr_misaligned;

    // BP "exceptions"
    logic unfreeze;
    logic itlb_miss;
    logic icache_miss;
    logic dcache_replay;
    logic dtlb_load_miss;
    logic dtlb_store_miss;
    logic itlb_fill;
    logic dtlb_fill;
    logic _interrupt;
    logic cmd_full;
  }  bp_be_exception_s;

  typedef struct packed
  {
    logic dcache_store_miss;
    logic dcache_load_miss;
    logic fencei_clean;
    logic sfence_vma;
    logic dbreak;
    logic dret;
    logic mret;
    logic sret;
    logic wfi;
    logic csrw;
  }  bp_be_special_s;

  typedef struct packed
  {
    logic v;
    logic queue_v;

    bp_be_exception_s exc;
    bp_be_special_s   spec;
  }  bp_be_exc_stage_s;

  typedef struct packed
  {
    bp_be_csr_fu_op_e                  csr_op;
    logic [rv64_csr_addr_width_gp-1:0] csr_addr;
    logic [rv64_reg_data_width_gp-1:0] data;
  }  bp_be_csr_cmd_s;




  



  typedef enum logic [3:0]
  {
    e_dcache_subop_none
    ,e_dcache_subop_lr
    ,e_dcache_subop_sc
    ,e_dcache_subop_amoswap
    ,e_dcache_subop_amoadd
    ,e_dcache_subop_amoxor
    ,e_dcache_subop_amoand
    ,e_dcache_subop_amoor
    ,e_dcache_subop_amomin
    ,e_dcache_subop_amomax
    ,e_dcache_subop_amominu
    ,e_dcache_subop_amomaxu
  } bp_be_amo_subop_e;

  typedef struct packed
  {
    logic                         load_op;
    logic                         ret_op;
    logic                         store_op;
    logic                         signed_op;
    logic                         float_op;
    logic                         double_op;
    logic                         word_op;
    logic                         half_op;
    logic                         byte_op;
    logic                         fencei_op;
    logic                         uncached_op;
    logic                         lr_op;
    logic                         sc_op;
    logic                         amo_op;
    bp_be_amo_subop_e             amo_subop;
    logic [reg_addr_width_gp-1:0] rd_addr;
  }  bp_be_dcache_decode_s;





endpackage



module bp_be_pipe_int
import bp_common_pkg::*;
import bp_be_pkg::*;
#(parameter bp_params_e bp_params_p = e_bp_default_cfg
  
   , localparam bp_proc_param_s proc_param_lp = all_cfgs_gp[bp_params_p]                       
                                                                                                  
   , localparam cc_x_dim_p  = proc_param_lp.cc_x_dim                                              
   , localparam cc_y_dim_p  = proc_param_lp.cc_y_dim                                              
                                                                                                  
   , localparam ic_x_dim_p = cc_x_dim_p                                                           
   , localparam ic_y_dim_p = proc_param_lp.ic_y_dim                                               
   , localparam mc_x_dim_p = cc_x_dim_p                                                           
   , localparam mc_y_dim_p = proc_param_lp.mc_y_dim                                               
   , localparam cac_x_dim_p = proc_param_lp.cac_x_dim                                             
   , localparam cac_y_dim_p = cc_y_dim_p                                                          
   , localparam sac_x_dim_p = proc_param_lp.sac_x_dim                                             
   , localparam sac_y_dim_p = cc_y_dim_p                                                          
   , localparam cacc_type_p = proc_param_lp.cacc_type                                             
   , localparam sacc_type_p = proc_param_lp.sacc_type                                             
                                                                                                  
   , localparam num_core_p  = cc_x_dim_p * cc_y_dim_p                                             
   , localparam num_io_p    = ic_x_dim_p * ic_y_dim_p                                             
   , localparam num_l2e_p   = mc_x_dim_p * mc_y_dim_p                                             
   , localparam num_cacc_p  = cac_x_dim_p * cac_y_dim_p                                           
   , localparam num_sacc_p  = sac_x_dim_p * sac_y_dim_p                                           
                                                                                                  
   , localparam num_cce_p = proc_param_lp.num_cce                                                 
   , localparam num_lce_p = proc_param_lp.num_lce                                                 
                                                                                                  
   , localparam core_id_width_p = ( ((cc_x_dim_p*cc_y_dim_p)==1) ? 1 : $clog2((cc_x_dim_p*cc_y_dim_p)))                          
   , localparam cce_id_width_p  = ( ((((cc_x_dim_p*1)+2)*((cc_y_dim_p*1)+2))==1) ? 1 : $clog2((((cc_x_dim_p*1)+2)*((cc_y_dim_p*1)+2))))          
   , localparam lce_id_width_p  = ( ((((cc_x_dim_p*2)+2)*((cc_y_dim_p*2)+2))==1) ? 1 : $clog2((((cc_x_dim_p*2)+2)*((cc_y_dim_p*2)+2))))          
                                                                                                  
   , localparam vaddr_width_p   = proc_param_lp.vaddr_width                                       
   , localparam paddr_width_p   = proc_param_lp.paddr_width                                       
   , localparam daddr_width_p   = proc_param_lp.daddr_width                                       
   , localparam caddr_width_p   = proc_param_lp.caddr_width                                       
   , localparam asid_width_p    = proc_param_lp.asid_width                                        
   , localparam hio_width_p     = paddr_width_p - daddr_width_p                                   
                                                                                                  
   , localparam branch_metadata_fwd_width_p = proc_param_lp.branch_metadata_fwd_width             
   , localparam btb_tag_width_p             = proc_param_lp.btb_tag_width                         
   , localparam btb_idx_width_p             = proc_param_lp.btb_idx_width                         
   , localparam bht_idx_width_p             = proc_param_lp.bht_idx_width                         
   , localparam bht_row_els_p               = proc_param_lp.bht_row_els                           
   , localparam ghist_width_p               = proc_param_lp.ghist_width                           
   , localparam bht_row_width_p             = 2*bht_row_els_p                                     
                                                                                                  
   , localparam itlb_els_4k_p              = proc_param_lp.itlb_els_4k                            
   , localparam itlb_els_1g_p              = proc_param_lp.itlb_els_1g                            
   , localparam dtlb_els_4k_p              = proc_param_lp.dtlb_els_4k                            
   , localparam dtlb_els_1g_p              = proc_param_lp.dtlb_els_1g                            
                                                                                                  
   , localparam dcache_features_p          = proc_param_lp.dcache_features                        
   , localparam dcache_sets_p              = proc_param_lp.dcache_sets                            
   , localparam dcache_assoc_p             = proc_param_lp.dcache_assoc                           
   , localparam dcache_block_width_p       = proc_param_lp.dcache_block_width                     
   , localparam dcache_fill_width_p        = proc_param_lp.dcache_fill_width                      
   , localparam icache_features_p          = proc_param_lp.icache_features                        
   , localparam icache_sets_p              = proc_param_lp.icache_sets                            
   , localparam icache_assoc_p             = proc_param_lp.icache_assoc                           
   , localparam icache_block_width_p       = proc_param_lp.icache_block_width                     
   , localparam icache_fill_width_p        = proc_param_lp.icache_fill_width                      
   , localparam acache_features_p          = proc_param_lp.acache_features                        
   , localparam acache_sets_p              = proc_param_lp.acache_sets                            
   , localparam acache_assoc_p             = proc_param_lp.acache_assoc                           
   , localparam acache_block_width_p       = proc_param_lp.acache_block_width                     
   , localparam acache_fill_width_p        = proc_param_lp.acache_fill_width                      
   , localparam lce_assoc_p                =                                                      
       (((dcache_assoc_p)>((((icache_assoc_p)>(num_cacc_p ? acache_assoc_p : '0)) ? (icache_assoc_p) : (num_cacc_p ? acache_assoc_p : '0)))) ? (dcache_assoc_p) : ((((icache_assoc_p)>(num_cacc_p ? acache_assoc_p : '0)) ? (icache_assoc_p) : (num_cacc_p ? acache_assoc_p : '0))))       
   , localparam lce_assoc_width_p          = ( ((lce_assoc_p)==1) ? 1 : $clog2((lce_assoc_p)))                         
   , localparam lce_sets_p                 =                                                      
       (((dcache_sets_p)>((((icache_sets_p)>(num_cacc_p ? acache_sets_p : '0)) ? (icache_sets_p) : (num_cacc_p ? acache_sets_p : '0)))) ? (dcache_sets_p) : ((((icache_sets_p)>(num_cacc_p ? acache_sets_p : '0)) ? (icache_sets_p) : (num_cacc_p ? acache_sets_p : '0))))          
   , localparam lce_sets_width_p           = ( ((lce_sets_p)==1) ? 1 : $clog2((lce_sets_p)))                          
                                                                                                  
   , localparam cce_block_width_p          =                                                      
       (((dcache_block_width_p)>((((icache_block_width_p)>(num_cacc_p ? acache_block_width_p : '0)) ? (icache_block_width_p) : (num_cacc_p ? acache_block_width_p : '0)))) ? (dcache_block_width_p) : ((((icache_block_width_p)>(num_cacc_p ? acache_block_width_p : '0)) ? (icache_block_width_p) : (num_cacc_p ? acache_block_width_p : '0)))) 
   , localparam uce_fill_width_p           =                                                      
       (((dcache_fill_width_p)>((((icache_fill_width_p)>(num_cacc_p ? acache_fill_width_p : '0)) ? (icache_fill_width_p) : (num_cacc_p ? acache_fill_width_p : '0)))) ? (dcache_fill_width_p) : ((((icache_fill_width_p)>(num_cacc_p ? acache_fill_width_p : '0)) ? (icache_fill_width_p) : (num_cacc_p ? acache_fill_width_p : '0)))) 
                                                                                                  
   , localparam cce_type_p                 = proc_param_lp.cce_type                               
   , localparam cce_pc_width_p             = proc_param_lp.cce_pc_width                           
   , localparam bedrock_data_width_p       = proc_param_lp.bedrock_data_width                     
   , localparam num_cce_instr_ram_els_p    = 2**cce_pc_width_p                                    
   , localparam cce_way_groups_p           =                                                      
       (((dcache_sets_p)<((((icache_sets_p)<(num_cacc_p ? acache_sets_p : icache_sets_p)) ? (icache_sets_p) : (num_cacc_p ? acache_sets_p : icache_sets_p)))) ? (dcache_sets_p) : ((((icache_sets_p)<(num_cacc_p ? acache_sets_p : icache_sets_p)) ? (icache_sets_p) : (num_cacc_p ? acache_sets_p : icache_sets_p)))) 
                                                                                                  
   /* L2 enable turns the L2 into a small write buffer, which is minimal size                  */ 
   , localparam l2_features_p         = proc_param_lp.l2_features                                 
   , localparam l2_banks_p            = l2_features_p[e_cfg_enabled] ? proc_param_lp.l2_banks : 1 
   , localparam l2_sets_p             = l2_features_p[e_cfg_enabled] ? proc_param_lp.l2_sets  : 4 
   , localparam l2_assoc_p            = l2_features_p[e_cfg_enabled] ? proc_param_lp.l2_assoc : 2 
   , localparam l2_block_width_p      = proc_param_lp.l2_block_width                              
   , localparam l2_fill_width_p       = proc_param_lp.l2_fill_width                               
   , localparam l2_data_width_p       = proc_param_lp.l2_data_width                               
   , localparam l2_outstanding_reqs_p = proc_param_lp.l2_outstanding_reqs                         
                                                                                                  
   , localparam l2_block_size_in_words_p = l2_block_width_p / l2_data_width_p                     
   , localparam l2_block_size_in_fill_p  = l2_block_width_p / l2_fill_width_p                     
                                                                                                  
   , localparam fe_queue_fifo_els_p  = proc_param_lp.fe_queue_fifo_els                            
   , localparam fe_cmd_fifo_els_p    = proc_param_lp.fe_cmd_fifo_els                              
   , localparam muldiv_support_p     = proc_param_lp.muldiv_support                               
   , localparam fpu_support_p        = proc_param_lp.fpu_support                                  
   , localparam compressed_support_p = proc_param_lp.compressed_support                           
                                                                                                  
   , localparam async_coh_clk_p        = proc_param_lp.async_coh_clk                              
   , localparam coh_noc_max_credits_p  = proc_param_lp.coh_noc_max_credits                        
   , localparam coh_noc_flit_width_p   = proc_param_lp.coh_noc_flit_width                         
   , localparam coh_noc_cid_width_p    = proc_param_lp.coh_noc_cid_width                          
   , localparam coh_noc_len_width_p    = proc_param_lp.coh_noc_len_width                          
   , localparam coh_noc_y_cord_width_p = ( ((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)==1) ? 1 : $clog2((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)))      
   , localparam coh_noc_x_cord_width_p = ( ((sac_x_dim_p+cc_x_dim_p+cac_x_dim_p+1)==1) ? 1 : $clog2((sac_x_dim_p+cc_x_dim_p+cac_x_dim_p+1)))    
   , localparam coh_noc_dims_p         = 2 
   , localparam coh_noc_dirs_p         = coh_noc_dims_p*2 + 1 
   , localparam coh_noc_trans_p        = 0 
   , localparam int coh_noc_cord_markers_pos_p[coh_noc_dims_p:0] = coh_noc_trans_p                
       ? '{coh_noc_x_cord_width_p+coh_noc_y_cord_width_p, coh_noc_y_cord_width_p, 0}              
       : '{coh_noc_y_cord_width_p+coh_noc_x_cord_width_p, coh_noc_x_cord_width_p, 0}              
   , localparam coh_noc_cord_width_p   = coh_noc_cord_markers_pos_p[coh_noc_dims_p]               
                                                                                                  
   , localparam async_mem_clk_p           = proc_param_lp.async_mem_clk                           
   , localparam mem_noc_max_credits_p     = proc_param_lp.mem_noc_max_credits                     
   , localparam mem_noc_flit_width_p      = proc_param_lp.mem_noc_flit_width                      
   , localparam mem_noc_cid_width_p       = proc_param_lp.mem_noc_cid_width                       
   , localparam mem_noc_len_width_p       = proc_param_lp.mem_noc_len_width                       
   , localparam mem_noc_y_cord_width_p    = ( ((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)==1) ? 1 : $clog2((ic_y_dim_p+cc_y_dim_p+mc_y_dim_p+1)))   
   , localparam mem_noc_x_cord_width_p    = 0 
   , localparam mem_noc_dims_p            = 1 
   , localparam mem_noc_cord_dims_p       = 2 
   , localparam mem_noc_dirs_p            = mem_noc_dims_p*2 + 1 
   , localparam mem_noc_trans_p           = 1 
   , localparam int mem_noc_cord_markers_pos_p[mem_noc_cord_dims_p:0] = mem_noc_trans_p           
       ? '{mem_noc_x_cord_width_p+mem_noc_y_cord_width_p, mem_noc_y_cord_width_p, 0}              
       : '{mem_noc_y_cord_width_p+mem_noc_x_cord_width_p, mem_noc_x_cord_width_p, 0}              
   , localparam mem_noc_cord_width_p      = mem_noc_cord_markers_pos_p[mem_noc_dims_p]            
                                                                                                  
   , localparam async_io_clk_p           = proc_param_lp.async_io_clk                             
   , localparam io_noc_max_credits_p     = proc_param_lp.io_noc_max_credits                       
   , localparam io_noc_did_width_p       = proc_param_lp.io_noc_did_width                         
   , localparam io_noc_flit_width_p      = proc_param_lp.io_noc_flit_width                        
   , localparam io_noc_cid_width_p       = proc_param_lp.io_noc_cid_width                         
   , localparam io_noc_len_width_p       = proc_param_lp.io_noc_len_width                         
   , localparam io_noc_y_cord_width_p    = 0 
   , localparam io_noc_x_cord_width_p    = io_noc_did_width_p                                     
   , localparam io_noc_dims_p            = 1 
   , localparam io_noc_cord_dims_p       = 2 
   , localparam io_noc_dirs_p            = io_noc_cord_dims_p*2 + 1 
   , localparam io_noc_trans_p           = 0 
   , localparam int io_noc_cord_markers_pos_p[io_noc_cord_dims_p:0] = io_noc_trans_p              
       ? '{io_noc_x_cord_width_p+io_noc_y_cord_width_p, io_noc_y_cord_width_p, 0}                 
       : '{io_noc_y_cord_width_p+io_noc_x_cord_width_p, io_noc_x_cord_width_p, 0}                 
   , localparam io_noc_cord_width_p      = io_noc_cord_markers_pos_p[io_noc_dims_p]               
                                                                                                  
   , localparam did_width_p  = io_noc_did_width_p                                                 
                                                                                                  
   , localparam etag_width_p  = dword_width_gp - page_offset_width_gp                             
   , localparam vtag_width_p  = vaddr_width_p - page_offset_width_gp                              
   , localparam ptag_width_p  = paddr_width_p - page_offset_width_gp                              
   , localparam dtag_width_p  = daddr_width_p - page_offset_width_gp                              
   , localparam icache_ctag_width_p = caddr_width_p -                                             
       (( ((icache_sets_p*icache_block_width_p/8)==1) ? 1 : $clog2((icache_sets_p*icache_block_width_p/8))))                                    
   , localparam dcache_ctag_width_p = caddr_width_p -                                             
       (( ((dcache_sets_p*dcache_block_width_p/8)==1) ? 1 : $clog2((dcache_sets_p*dcache_block_width_p/8))))                                    
   , localparam acache_ctag_width_p = caddr_width_p -                                             
       (( ((acache_sets_p*acache_block_width_p/8)==1) ? 1 : $clog2((acache_sets_p*acache_block_width_p/8))))


  , localparam dispatch_pkt_width_lp = 
   (2                                                                                             
    + vaddr_width_p                                                                              
    + rv64_instr_width_gp                                                                         
    + 7                                                                                           
    + 3 * dpath_width_gp                                                                          
    + $bits(bp_be_decode_s)                                                                       
    + 1                                                                                           
    + $bits(bp_be_exception_s)                                                                    
    + $bits(bp_be_special_s)                                                                      
    )

  )
 (input                               clk_i
  , input                             reset_i

  , input [dispatch_pkt_width_lp-1:0] reservation_i
  , input                             flush_i

  // Pipeline results
  , output logic [dpath_width_gp-1:0] data_o
  , output logic                      v_o
  );

 // Suppress unused signal warning
 wire unused = &{clk_i, reset_i, flush_i};

 
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic                                    irs1_v;                                             
     logic                                    irs2_v;                                             
     logic                                    frs1_v;                                             
     logic                                    frs2_v;                                             
     logic                                    frs3_v;                                             
     rv64_instr_s                             instr;                                              
   }  bp_be_preissue_pkt_s;                                                                       
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic                                    v;                                                  
     logic                                    instr_v;                                            
     logic                                    itlb_miss_v;                                        
     logic                                    instr_access_fault_v;                               
     logic                                    instr_page_fault_v;                                 
     logic                                    icache_miss_v;                                      
     logic [vaddr_width_p-1:0]               pc;                                                 
     rv64_instr_s                             instr;                                              
     logic [branch_metadata_fwd_width_p-1:0] branch_metadata_fwd;                                
     logic                                    partial_v;                                          
     logic                                    csr_v;                                              
     logic                                    mem_v;                                              
     logic                                    fence_v;                                            
     logic                                    long_v;                                             
     logic                                    irs1_v;                                             
     logic                                    irs2_v;                                             
     logic                                    frs1_v;                                             
     logic                                    frs2_v;                                             
     logic                                    frs3_v;                                             
     logic                                    iwb_v;                                              
     logic                                    fwb_v;                                              
   }  bp_be_issue_pkt_s;                                                                          
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic                                    v;                                                  
     logic                                    queue_v;                                            
     logic [vaddr_width_p-1:0]               pc;                                                 
     logic                                    instr_v;                                            
     rv64_instr_s                             instr;                                              
     bp_be_decode_s                           decode;                                             
                                                                                                  
     logic                                    irs1_v;                                             
     logic                                    frs1_v;                                             
     logic                                    irs2_v;                                             
     logic                                    frs2_v;                                             
     logic                                    irs3_v;                                             
     logic                                    frs3_v;                                             
     logic [dpath_width_gp-1:0]               rs1;                                                
     logic [dpath_width_gp-1:0]               rs2;                                                
     logic [dpath_width_gp-1:0]               imm;                                                
     logic                                    partial;                                            
     bp_be_exception_s                        exception;                                          
     bp_be_special_s                          special;                                            
   }  bp_be_dispatch_pkt_s;                                                                       
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic                              v;                                                        
     logic                              fflags_w_v;                                               
     logic                              ctl_iwb_v;                                                
     logic                              aux_iwb_v;                                                
     logic                              aux_fwb_v;                                                
     logic                              int_iwb_v;                                                
     logic                              int_fwb_v;                                                
     logic                              emem_iwb_v;                                               
     logic                              emem_fwb_v;                                               
     logic                              fmem_iwb_v;                                               
     logic                              fmem_fwb_v;                                               
     logic                              mul_iwb_v;                                                
     logic                              fma_fwb_v;                                                
                                                                                                  
     logic [rv64_reg_addr_width_gp-1:0] rd_addr;                                                  
   }  bp_be_dep_status_s;                                                                         
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic                     v;                                                                 
     logic                     branch;                                                            
     logic                     btaken;                                                            
     logic [vaddr_width_p-1:0] npc;                                                               
   }  bp_be_branch_pkt_s;                                                                         
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic                      v;                                                                
     logic                      queue_v;                                                          
     logic                      instret;                                                          
     logic [vaddr_width_p-1:0]  npc;                                                              
     logic [vaddr_width_p-1:0]  vaddr;                                                            
     logic [dpath_width_gp-1:0] data;                                                             
     rv64_instr_s               instr;                                                            
     logic                      partial;                                                          
     bp_be_exception_s          exception;                                                        
     bp_be_special_s            special;                                                          
   }  bp_be_retire_pkt_s;                                                                         
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic [paddr_width_p-page_offset_width_gp-1:0] ptag;                                        
     logic                                           gigapage;                                    
     logic                                           a;                                           
     logic                                           d;                                           
     logic                                           u;                                           
     logic                                           x;                                           
     logic                                           w;                                           
     logic                                           r;                                           
   }  bp_be_pte_leaf_s;                                                                           
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic                           npc_w_v;                                                     
     logic                           queue_v;                                                     
     logic                           instret;                                                     
     logic [vaddr_width_p-1:0]       pc;                                                          
     logic [vaddr_width_p-1:0]       npc;                                                         
     logic [vaddr_width_p-1:0]       vaddr;                                                       
     rv64_instr_s                    instr;                                                       
     bp_be_pte_leaf_s                pte_leaf;                                                    
     logic [rv64_priv_width_gp-1:0]  priv_n;                                                      
     logic                           translation_en_n;                                            
     logic                           exception;                                                   
     logic                           partial;                                                     
     logic                           _interrupt;                                                  
     logic                           unfreeze;                                                    
     logic                           eret;                                                        
     logic                           fencei;                                                      
     logic                           sfence;                                                      
     logic                           csrw;                                                        
     logic                           wfi;                                                         
     logic                           itlb_miss;                                                   
     logic                           icache_miss;                                                 
     logic                           dtlb_store_miss;                                             
     logic                           dtlb_load_miss;                                              
     logic                           dcache_store_miss;                                           
     logic                           dcache_load_miss;                                            
     logic                           dcache_replay;                                               
     logic                           itlb_fill_v;                                                 
     logic                           dtlb_fill_v;                                                 
   }  bp_be_commit_pkt_s;                                                                         
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic                         ird_w_v;                                                       
     logic                         frd_w_v;                                                       
     logic                         late;                                                          
     logic [reg_addr_width_gp-1:0] rd_addr;                                                       
     logic [dpath_width_gp-1:0]    rd_data;                                                       
     logic                         fflags_w_v;                                                    
     rv64_fflags_s                 fflags;                                                        
   }  bp_be_wb_pkt_s;                                                                             
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     /* Trans info */                                                                             
     logic [ptag_width_p-1:0]       base_ppn;                                                     
     logic [rv64_priv_width_gp-1:0] priv_mode;                                                    
     logic                          mstatus_sum;                                                  
     logic                          mstatus_mxr;                                                  
     logic                          instr_miss_v;                                                 
     logic                          load_miss_v;                                                  
     logic                          store_miss_v;                                                 
     logic                          partial;                                                      
     logic [vaddr_width_p-1:0]     vaddr;                                                        
   }  bp_be_ptw_miss_pkt_s;                                                                       
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic v;                                                                                     
     logic itlb_fill_v;                                                                           
     logic dtlb_fill_v;                                                                           
     logic instr_page_fault_v;                                                                    
     logic load_page_fault_v;                                                                     
     logic store_page_fault_v;                                                                    
     logic partial;                                                                               
     logic [vaddr_width_p-1:0] vaddr;                                                            
     bp_be_pte_leaf_s entry;                                                                      
   }  bp_be_ptw_fill_pkt_s;                                                                       
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic [rv64_priv_width_gp-1:0] priv_mode;                                                    
     logic [ptag_width_p-1:0]       base_ppn;                                                     
     logic                          translation_en;                                               
     logic                          mstatus_sum;                                                  
     logic                          mstatus_mxr;                                                  
   }  bp_be_trans_info_s;                                                                         
                                                                                                  
   typedef struct packed                                                                          
   {                                                                                              
     logic [rv64_priv_width_gp-1:0] priv_mode;                                                    
     logic                          debug_mode;                                                   
     logic                          tsr;                                                          
     logic                          tw;                                                           
     logic                          tvm;                                                          
     logic                          ebreakm;                                                      
     logic                          ebreaks;                                                      
     logic                          ebreaku;                                                      
     logic                          fpu_en;                                                       
   }  bp_be_decode_info_s
;
 bp_be_dispatch_pkt_s reservation;
 bp_be_decode_s decode;
 rv64_instr_s instr;

 assign reservation = reservation_i;
 assign decode = reservation.decode;
 assign instr = reservation.instr;
 wire [vaddr_width_p-1:0] pc  = reservation.pc[0+:vaddr_width_p];
 wire [dword_width_gp-1:0] rs1 = reservation.rs1[0+:dword_width_gp];
 wire [dword_width_gp-1:0] rs2 = reservation.rs2[0+:dword_width_gp];
 wire [dword_width_gp-1:0] imm = reservation.imm[0+:dword_width_gp];

 // Sign-extend PC for calculation
 wire [dword_width_gp-1:0] pc_sext_li = 
 ({{(((dword_width_gp-$bits(pc))>(0)) ? (dword_width_gp-$bits(pc)) : (0)){pc[$bits(pc)-1]}}, pc[0+:(((dword_width_gp)<($bits(pc))) ? (dword_width_gp) : ($bits(pc)))]})
;
 wire [dword_width_gp-1:0] pc_plus4   = pc_sext_li + dword_width_gp'(4);

 wire [dword_width_gp-1:0] src1  = decode.src1_sel  ? pc_sext_li : rs1;
 wire [dword_width_gp-1:0] src2  = decode.src2_sel  ? imm        : rs2;

 wire [rv64_shamt_width_gp-1:0] shamt = decode.opw_v ? src2[0+:rv64_shamtw_width_gp] : src2[0+:rv64_shamt_width_gp];

 // Shift the operands to the high bits of the ALU in order to reuse 64-bit operators
 wire [dword_width_gp-1:0] final_src1 = decode.opw_v ? (src1 << word_width_gp) : src1;
 wire [dword_width_gp-1:0] final_src2 = decode.opw_v ? (src2 << word_width_gp) : src2;

 // ALU
 logic [dword_width_gp-1:0] alu_result;
 always_comb
   unique case (decode.fu_op)
     e_int_op_add       : alu_result = final_src1 +   final_src2;
     e_int_op_sub       : alu_result = final_src1 -   final_src2;
     e_int_op_xor       : alu_result = final_src1 ^   final_src2;
     e_int_op_or        : alu_result = final_src1 |   final_src2;
     e_int_op_and       : alu_result = final_src1 &   final_src2;
     e_int_op_sll       : alu_result = final_src1 <<  shamt;
     e_int_op_srl       : alu_result = final_src1 >>  shamt;
     e_int_op_sra       : alu_result = $signed(final_src1) >>> shamt;
     e_int_op_pass_src2 : alu_result = final_src2;

     // Single bit results
     e_int_op_eq   : alu_result = (dword_width_gp)'(final_src1 == final_src2);
     e_int_op_ne   : alu_result = (dword_width_gp)'(final_src1 != final_src2);
     e_int_op_slt  : alu_result = (dword_width_gp)'($signed(final_src1) <  $signed(final_src2));
     e_int_op_sltu : alu_result = (dword_width_gp)'(final_src1 <  final_src2);
     e_int_op_sge  : alu_result = (dword_width_gp)'($signed(final_src1) >= $signed(final_src2));
     e_int_op_sgeu : alu_result = (dword_width_gp)'(final_src1 >= final_src2);
     default       : alu_result = '0;
   endcase

 // Shift back the ALU result from the top field for word width operations
 wire [dword_width_gp-1:0] opw_result = $signed(alu_result) >>> word_width_gp;
 assign data_o = decode.opw_v ? opw_result : alu_result;
 assign v_o    = reservation.v & reservation.decode.pipe_int_v;

endmodule


