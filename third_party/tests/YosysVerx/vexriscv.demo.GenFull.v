// Generator : SpinalHDL v1.3.5    git head : f0505d24810c8661a24530409359554b7cfa271a
// Date      : 30/05/2019, 19:51:50
// Component : VexRiscv


`define ShiftCtrlEnum_defaultEncoding_type [1:0]
`define ShiftCtrlEnum_defaultEncoding_DISABLE_1 2'b00
`define ShiftCtrlEnum_defaultEncoding_SLL_1 2'b01
`define ShiftCtrlEnum_defaultEncoding_SRL_1 2'b10
`define ShiftCtrlEnum_defaultEncoding_SRA_1 2'b11

`define AluBitwiseCtrlEnum_defaultEncoding_type [1:0]
`define AluBitwiseCtrlEnum_defaultEncoding_XOR_1 2'b00
`define AluBitwiseCtrlEnum_defaultEncoding_OR_1 2'b01
`define AluBitwiseCtrlEnum_defaultEncoding_AND_1 2'b10

`define Src1CtrlEnum_defaultEncoding_type [1:0]
`define Src1CtrlEnum_defaultEncoding_RS 2'b00
`define Src1CtrlEnum_defaultEncoding_IMU 2'b01
`define Src1CtrlEnum_defaultEncoding_PC_INCREMENT 2'b10
`define Src1CtrlEnum_defaultEncoding_URS1 2'b11

`define Src2CtrlEnum_defaultEncoding_type [1:0]
`define Src2CtrlEnum_defaultEncoding_RS 2'b00
`define Src2CtrlEnum_defaultEncoding_IMI 2'b01
`define Src2CtrlEnum_defaultEncoding_IMS 2'b10
`define Src2CtrlEnum_defaultEncoding_PC 2'b11

`define AluCtrlEnum_defaultEncoding_type [1:0]
`define AluCtrlEnum_defaultEncoding_ADD_SUB 2'b00
`define AluCtrlEnum_defaultEncoding_SLT_SLTU 2'b01
`define AluCtrlEnum_defaultEncoding_BITWISE 2'b10

`define EnvCtrlEnum_defaultEncoding_type [0:0]
`define EnvCtrlEnum_defaultEncoding_NONE 1'b0
`define EnvCtrlEnum_defaultEncoding_XRET 1'b1

`define BranchCtrlEnum_defaultEncoding_type [1:0]
`define BranchCtrlEnum_defaultEncoding_INC 2'b00
`define BranchCtrlEnum_defaultEncoding_B 2'b01
`define BranchCtrlEnum_defaultEncoding_JAL 2'b10
`define BranchCtrlEnum_defaultEncoding_JALR 2'b11

`define MmuPlugin_shared_State_defaultEncoding_type [2:0]
`define MmuPlugin_shared_State_defaultEncoding_IDLE 3'b000
`define MmuPlugin_shared_State_defaultEncoding_L1_CMD 3'b001
`define MmuPlugin_shared_State_defaultEncoding_L1_RSP 3'b010
`define MmuPlugin_shared_State_defaultEncoding_L0_CMD 3'b011
`define MmuPlugin_shared_State_defaultEncoding_L0_RSP 3'b100

module InstructionCache (
      input   io_flush,
      input   io_cpu_prefetch_isValid,
      output reg  io_cpu_prefetch_haltIt,
      input  [31:0] io_cpu_prefetch_pc,
      input   io_cpu_fetch_isValid,
      input   io_cpu_fetch_isStuck,
      input   io_cpu_fetch_isRemoved,
      input  [31:0] io_cpu_fetch_pc,
      output [31:0] io_cpu_fetch_data,
      input   io_cpu_fetch_dataBypassValid,
      input  [31:0] io_cpu_fetch_dataBypass,
      output  io_cpu_fetch_mmuBus_cmd_isValid,
      output [31:0] io_cpu_fetch_mmuBus_cmd_virtualAddress,
      output  io_cpu_fetch_mmuBus_cmd_bypassTranslation,
      input  [31:0] io_cpu_fetch_mmuBus_rsp_physicalAddress,
      input   io_cpu_fetch_mmuBus_rsp_isIoAccess,
      input   io_cpu_fetch_mmuBus_rsp_allowRead,
      input   io_cpu_fetch_mmuBus_rsp_allowWrite,
      input   io_cpu_fetch_mmuBus_rsp_allowExecute,
      input   io_cpu_fetch_mmuBus_rsp_exception,
      input   io_cpu_fetch_mmuBus_rsp_refilling,
      output  io_cpu_fetch_mmuBus_end,
      input   io_cpu_fetch_mmuBus_busy,
      output [31:0] io_cpu_fetch_physicalAddress,
      output  io_cpu_fetch_haltIt,
      input   io_cpu_decode_isValid,
      input   io_cpu_decode_isStuck,
      input  [31:0] io_cpu_decode_pc,
      output [31:0] io_cpu_decode_physicalAddress,
      output [31:0] io_cpu_decode_data,
      output  io_cpu_decode_cacheMiss,
      output  io_cpu_decode_error,
      output  io_cpu_decode_mmuRefilling,
      output  io_cpu_decode_mmuException,
      input   io_cpu_decode_isUser,
      input   io_cpu_fill_valid,
      input  [31:0] io_cpu_fill_payload,
      output  io_mem_cmd_valid,
      input   io_mem_cmd_ready,
      output [31:0] io_mem_cmd_payload_address,
      output [2:0] io_mem_cmd_payload_size,
      input   io_mem_rsp_valid,
      input  [31:0] io_mem_rsp_payload_data,
      input   io_mem_rsp_payload_error,
      input   clk,
      input   reset);
  reg [21:0] _zz_11_;
  reg [31:0] _zz_12_;
  wire  _zz_13_;
  wire  _zz_14_;
  wire [0:0] _zz_15_;
  wire [0:0] _zz_16_;
  wire [21:0] _zz_17_;
  reg  _zz_1_;
  reg  _zz_2_;
  reg  lineLoader_fire;
  reg  lineLoader_valid;
  reg [31:0] lineLoader_address;
  reg  lineLoader_hadError;
  reg  lineLoader_flushPending;
  reg [7:0] lineLoader_flushCounter;
  reg  _zz_3_;
  reg  lineLoader_cmdSent;
  reg  lineLoader_wayToAllocate_willIncrement;
  wire  lineLoader_wayToAllocate_willClear;
  wire  lineLoader_wayToAllocate_willOverflowIfInc;
  wire  lineLoader_wayToAllocate_willOverflow;
  reg [2:0] lineLoader_wordIndex;
  wire  lineLoader_write_tag_0_valid;
  wire [6:0] lineLoader_write_tag_0_payload_address;
  wire  lineLoader_write_tag_0_payload_data_valid;
  wire  lineLoader_write_tag_0_payload_data_error;
  wire [19:0] lineLoader_write_tag_0_payload_data_address;
  wire  lineLoader_write_data_0_valid;
  wire [9:0] lineLoader_write_data_0_payload_address;
  wire [31:0] lineLoader_write_data_0_payload_data;
  wire  _zz_4_;
  wire [6:0] _zz_5_;
  wire  _zz_6_;
  wire  fetchStage_read_waysValues_0_tag_valid;
  wire  fetchStage_read_waysValues_0_tag_error;
  wire [19:0] fetchStage_read_waysValues_0_tag_address;
  wire [21:0] _zz_7_;
  wire [9:0] _zz_8_;
  wire  _zz_9_;
  wire [31:0] fetchStage_read_waysValues_0_data;
  reg [31:0] decodeStage_mmuRsp_physicalAddress;
  reg  decodeStage_mmuRsp_isIoAccess;
  reg  decodeStage_mmuRsp_allowRead;
  reg  decodeStage_mmuRsp_allowWrite;
  reg  decodeStage_mmuRsp_allowExecute;
  reg  decodeStage_mmuRsp_exception;
  reg  decodeStage_mmuRsp_refilling;
  reg  decodeStage_hit_tags_0_valid;
  reg  decodeStage_hit_tags_0_error;
  reg [19:0] decodeStage_hit_tags_0_address;
  wire  decodeStage_hit_hits_0;
  wire  decodeStage_hit_valid;
  wire  decodeStage_hit_error;
  reg [31:0] _zz_10_;
  wire [31:0] decodeStage_hit_data;
  reg [31:0] decodeStage_hit_word;
  reg  io_cpu_fetch_dataBypassValid_regNextWhen;
  reg [31:0] io_cpu_fetch_dataBypass_regNextWhen;
  reg [21:0] ways_0_tags [0:127];
  reg [31:0] ways_0_datas [0:1023];
  assign _zz_13_ = (! lineLoader_flushCounter[7]);
  assign _zz_14_ = (lineLoader_flushPending && (! (lineLoader_valid || io_cpu_fetch_isValid)));
  assign _zz_15_ = _zz_7_[0 : 0];
  assign _zz_16_ = _zz_7_[1 : 1];
  assign _zz_17_ = {lineLoader_write_tag_0_payload_data_address,{lineLoader_write_tag_0_payload_data_error,lineLoader_write_tag_0_payload_data_valid}};
  always @ (posedge clk) begin
    if(_zz_2_) begin
      ways_0_tags[lineLoader_write_tag_0_payload_address] <= _zz_17_;
    end
  end

  always @ (posedge clk) begin
    if(_zz_6_) begin
      _zz_11_ <= ways_0_tags[_zz_5_];
    end
  end

  always @ (posedge clk) begin
    if(_zz_1_) begin
      ways_0_datas[lineLoader_write_data_0_payload_address] <= lineLoader_write_data_0_payload_data;
    end
  end

  always @ (posedge clk) begin
    if(_zz_9_) begin
      _zz_12_ <= ways_0_datas[_zz_8_];
    end
  end

  always @ (*) begin
    _zz_1_ = 1'b0;
    if(lineLoader_write_data_0_valid)begin
      _zz_1_ = 1'b1;
    end
  end

  always @ (*) begin
    _zz_2_ = 1'b0;
    if(lineLoader_write_tag_0_valid)begin
      _zz_2_ = 1'b1;
    end
  end

  assign io_cpu_fetch_haltIt = io_cpu_fetch_mmuBus_busy;
  always @ (*) begin
    lineLoader_fire = 1'b0;
    if(io_mem_rsp_valid)begin
      if((lineLoader_wordIndex == (3'b111)))begin
        lineLoader_fire = 1'b1;
      end
    end
  end

  always @ (*) begin
    io_cpu_prefetch_haltIt = (lineLoader_valid || lineLoader_flushPending);
    if(_zz_13_)begin
      io_cpu_prefetch_haltIt = 1'b1;
    end
    if((! _zz_3_))begin
      io_cpu_prefetch_haltIt = 1'b1;
    end
    if(io_flush)begin
      io_cpu_prefetch_haltIt = 1'b1;
    end
  end

  assign io_mem_cmd_valid = (lineLoader_valid && (! lineLoader_cmdSent));
  assign io_mem_cmd_payload_address = {lineLoader_address[31 : 5],(5'b00000)};
  assign io_mem_cmd_payload_size = (3'b101);
  always @ (*) begin
    lineLoader_wayToAllocate_willIncrement = 1'b0;
    if(lineLoader_fire)begin
      lineLoader_wayToAllocate_willIncrement = 1'b1;
    end
  end

  assign lineLoader_wayToAllocate_willClear = 1'b0;
  assign lineLoader_wayToAllocate_willOverflowIfInc = 1'b1;
  assign lineLoader_wayToAllocate_willOverflow = (lineLoader_wayToAllocate_willOverflowIfInc && lineLoader_wayToAllocate_willIncrement);
  assign _zz_4_ = 1'b1;
  assign lineLoader_write_tag_0_valid = ((_zz_4_ && lineLoader_fire) || (! lineLoader_flushCounter[7]));
  assign lineLoader_write_tag_0_payload_address = (lineLoader_flushCounter[7] ? lineLoader_address[11 : 5] : lineLoader_flushCounter[6 : 0]);
  assign lineLoader_write_tag_0_payload_data_valid = lineLoader_flushCounter[7];
  assign lineLoader_write_tag_0_payload_data_error = (lineLoader_hadError || io_mem_rsp_payload_error);
  assign lineLoader_write_tag_0_payload_data_address = lineLoader_address[31 : 12];
  assign lineLoader_write_data_0_valid = (io_mem_rsp_valid && _zz_4_);
  assign lineLoader_write_data_0_payload_address = {lineLoader_address[11 : 5],lineLoader_wordIndex};
  assign lineLoader_write_data_0_payload_data = io_mem_rsp_payload_data;
  assign _zz_5_ = io_cpu_prefetch_pc[11 : 5];
  assign _zz_6_ = (! io_cpu_fetch_isStuck);
  assign _zz_7_ = _zz_11_;
  assign fetchStage_read_waysValues_0_tag_valid = _zz_15_[0];
  assign fetchStage_read_waysValues_0_tag_error = _zz_16_[0];
  assign fetchStage_read_waysValues_0_tag_address = _zz_7_[21 : 2];
  assign _zz_8_ = io_cpu_prefetch_pc[11 : 2];
  assign _zz_9_ = (! io_cpu_fetch_isStuck);
  assign fetchStage_read_waysValues_0_data = _zz_12_;
  assign io_cpu_fetch_data = (io_cpu_fetch_dataBypassValid ? io_cpu_fetch_dataBypass : fetchStage_read_waysValues_0_data[31 : 0]);
  assign io_cpu_fetch_mmuBus_cmd_isValid = io_cpu_fetch_isValid;
  assign io_cpu_fetch_mmuBus_cmd_virtualAddress = io_cpu_fetch_pc;
  assign io_cpu_fetch_mmuBus_cmd_bypassTranslation = 1'b0;
  assign io_cpu_fetch_mmuBus_end = ((! io_cpu_fetch_isStuck) || io_cpu_fetch_isRemoved);
  assign io_cpu_fetch_physicalAddress = io_cpu_fetch_mmuBus_rsp_physicalAddress;
  assign decodeStage_hit_hits_0 = (decodeStage_hit_tags_0_valid && (decodeStage_hit_tags_0_address == decodeStage_mmuRsp_physicalAddress[31 : 12]));
  assign decodeStage_hit_valid = (decodeStage_hit_hits_0 != (1'b0));
  assign decodeStage_hit_error = decodeStage_hit_tags_0_error;
  assign decodeStage_hit_data = _zz_10_;
  always @ (*) begin
    decodeStage_hit_word = decodeStage_hit_data[31 : 0];
    if(io_cpu_fetch_dataBypassValid_regNextWhen)begin
      decodeStage_hit_word = io_cpu_fetch_dataBypass_regNextWhen;
    end
  end

  assign io_cpu_decode_data = decodeStage_hit_word;
  assign io_cpu_decode_cacheMiss = (! decodeStage_hit_valid);
  assign io_cpu_decode_error = decodeStage_hit_error;
  assign io_cpu_decode_mmuRefilling = decodeStage_mmuRsp_refilling;
  assign io_cpu_decode_mmuException = ((! decodeStage_mmuRsp_refilling) && (decodeStage_mmuRsp_exception || (! decodeStage_mmuRsp_allowExecute)));
  assign io_cpu_decode_physicalAddress = decodeStage_mmuRsp_physicalAddress;
  always @ (posedge clk or posedge reset) begin
    if (reset) begin
      lineLoader_valid <= 1'b0;
      lineLoader_hadError <= 1'b0;
      lineLoader_flushPending <= 1'b1;
      lineLoader_cmdSent <= 1'b0;
      lineLoader_wordIndex <= (3'b000);
    end else begin
      if(lineLoader_fire)begin
        lineLoader_valid <= 1'b0;
      end
      if(lineLoader_fire)begin
        lineLoader_hadError <= 1'b0;
      end
      if(io_cpu_fill_valid)begin
        lineLoader_valid <= 1'b1;
      end
      if(io_flush)begin
        lineLoader_flushPending <= 1'b1;
      end
      if(_zz_14_)begin
        lineLoader_flushPending <= 1'b0;
      end
      if((io_mem_cmd_valid && io_mem_cmd_ready))begin
        lineLoader_cmdSent <= 1'b1;
      end
      if(lineLoader_fire)begin
        lineLoader_cmdSent <= 1'b0;
      end
      if(io_mem_rsp_valid)begin
        lineLoader_wordIndex <= (lineLoader_wordIndex + (3'b001));
        if(io_mem_rsp_payload_error)begin
          lineLoader_hadError <= 1'b1;
        end
      end
    end
  end

  always @ (posedge clk) begin
    if(io_cpu_fill_valid)begin
      lineLoader_address <= io_cpu_fill_payload;
    end
    if(_zz_13_)begin
      lineLoader_flushCounter <= (lineLoader_flushCounter + (8'b00000001));
    end
    _zz_3_ <= lineLoader_flushCounter[7];
    if(_zz_14_)begin
      lineLoader_flushCounter <= (8'b00000000);
    end
    if((! io_cpu_decode_isStuck))begin
      decodeStage_mmuRsp_physicalAddress <= io_cpu_fetch_mmuBus_rsp_physicalAddress;
      decodeStage_mmuRsp_isIoAccess <= io_cpu_fetch_mmuBus_rsp_isIoAccess;
      decodeStage_mmuRsp_allowRead <= io_cpu_fetch_mmuBus_rsp_allowRead;
      decodeStage_mmuRsp_allowWrite <= io_cpu_fetch_mmuBus_rsp_allowWrite;
      decodeStage_mmuRsp_allowExecute <= io_cpu_fetch_mmuBus_rsp_allowExecute;
      decodeStage_mmuRsp_exception <= io_cpu_fetch_mmuBus_rsp_exception;
      decodeStage_mmuRsp_refilling <= io_cpu_fetch_mmuBus_rsp_refilling;
    end
    if((! io_cpu_decode_isStuck))begin
      decodeStage_hit_tags_0_valid <= fetchStage_read_waysValues_0_tag_valid;
      decodeStage_hit_tags_0_error <= fetchStage_read_waysValues_0_tag_error;
      decodeStage_hit_tags_0_address <= fetchStage_read_waysValues_0_tag_address;
    end
    if((! io_cpu_decode_isStuck))begin
      _zz_10_ <= fetchStage_read_waysValues_0_data;
    end
    if((! io_cpu_decode_isStuck))begin
      io_cpu_fetch_dataBypassValid_regNextWhen <= io_cpu_fetch_dataBypassValid;
    end
  end

  always @ (posedge clk) begin
    if((! io_cpu_decode_isStuck))begin
      io_cpu_fetch_dataBypass_regNextWhen <= io_cpu_fetch_dataBypass;
    end
  end

endmodule

module DataCache (
      input   io_cpu_execute_isValid,
      input  [31:0] io_cpu_execute_address,
      input   io_cpu_execute_args_wr,
      input  [31:0] io_cpu_execute_args_data,
      input  [1:0] io_cpu_execute_args_size,
      input   io_cpu_memory_isValid,
      input   io_cpu_memory_isStuck,
      input   io_cpu_memory_isRemoved,
      output  io_cpu_memory_isWrite,
      input  [31:0] io_cpu_memory_address,
      output  io_cpu_memory_mmuBus_cmd_isValid,
      output [31:0] io_cpu_memory_mmuBus_cmd_virtualAddress,
      output  io_cpu_memory_mmuBus_cmd_bypassTranslation,
      input  [31:0] io_cpu_memory_mmuBus_rsp_physicalAddress,
      input   io_cpu_memory_mmuBus_rsp_isIoAccess,
      input   io_cpu_memory_mmuBus_rsp_allowRead,
      input   io_cpu_memory_mmuBus_rsp_allowWrite,
      input   io_cpu_memory_mmuBus_rsp_allowExecute,
      input   io_cpu_memory_mmuBus_rsp_exception,
      input   io_cpu_memory_mmuBus_rsp_refilling,
      output  io_cpu_memory_mmuBus_end,
      input   io_cpu_memory_mmuBus_busy,
      input   io_cpu_writeBack_isValid,
      input   io_cpu_writeBack_isStuck,
      input   io_cpu_writeBack_isUser,
      output reg  io_cpu_writeBack_haltIt,
      output  io_cpu_writeBack_isWrite,
      output reg [31:0] io_cpu_writeBack_data,
      input  [31:0] io_cpu_writeBack_address,
      output  io_cpu_writeBack_mmuException,
      output  io_cpu_writeBack_unalignedAccess,
      output reg  io_cpu_writeBack_accessError,
      output reg  io_cpu_redo,
      input   io_cpu_flush_valid,
      output reg  io_cpu_flush_ready,
      output reg  io_mem_cmd_valid,
      input   io_mem_cmd_ready,
      output reg  io_mem_cmd_payload_wr,
      output reg [31:0] io_mem_cmd_payload_address,
      output [31:0] io_mem_cmd_payload_data,
      output [3:0] io_mem_cmd_payload_mask,
      output reg [2:0] io_mem_cmd_payload_length,
      output reg  io_mem_cmd_payload_last,
      input   io_mem_rsp_valid,
      input  [31:0] io_mem_rsp_payload_data,
      input   io_mem_rsp_payload_error,
      input   clk,
      input   reset);
  reg [21:0] _zz_10_;
  reg [31:0] _zz_11_;
  wire  _zz_12_;
  wire  _zz_13_;
  wire  _zz_14_;
  wire  _zz_15_;
  wire  _zz_16_;
  wire  _zz_17_;
  wire [0:0] _zz_18_;
  wire [0:0] _zz_19_;
  wire [0:0] _zz_20_;
  wire [2:0] _zz_21_;
  wire [1:0] _zz_22_;
  wire [21:0] _zz_23_;
  reg  _zz_1_;
  reg  _zz_2_;
  wire  haltCpu;
  reg  tagsReadCmd_valid;
  reg [6:0] tagsReadCmd_payload;
  reg  tagsWriteCmd_valid;
  reg [0:0] tagsWriteCmd_payload_way;
  reg [6:0] tagsWriteCmd_payload_address;
  reg  tagsWriteCmd_payload_data_valid;
  reg  tagsWriteCmd_payload_data_error;
  reg [19:0] tagsWriteCmd_payload_data_address;
  reg  tagsWriteLastCmd_valid;
  reg [0:0] tagsWriteLastCmd_payload_way;
  reg [6:0] tagsWriteLastCmd_payload_address;
  reg  tagsWriteLastCmd_payload_data_valid;
  reg  tagsWriteLastCmd_payload_data_error;
  reg [19:0] tagsWriteLastCmd_payload_data_address;
  reg  dataReadCmd_valid;
  reg [9:0] dataReadCmd_payload;
  reg  dataWriteCmd_valid;
  reg [0:0] dataWriteCmd_payload_way;
  reg [9:0] dataWriteCmd_payload_address;
  reg [31:0] dataWriteCmd_payload_data;
  reg [3:0] dataWriteCmd_payload_mask;
  wire  _zz_3_;
  wire  ways_0_tagsReadRsp_valid;
  wire  ways_0_tagsReadRsp_error;
  wire [19:0] ways_0_tagsReadRsp_address;
  wire [21:0] _zz_4_;
  wire  _zz_5_;
  wire [31:0] ways_0_dataReadRsp;
  reg [3:0] _zz_6_;
  wire [3:0] stage0_mask;
  wire [0:0] stage0_colisions;
  reg  stageA_request_wr;
  reg [31:0] stageA_request_data;
  reg [1:0] stageA_request_size;
  reg [3:0] stageA_mask;
  wire  stageA_wayHits_0;
  reg [0:0] stage0_colisions_regNextWhen;
  wire [0:0] _zz_7_;
  wire [0:0] stageA_colisions;
  reg  stageB_request_wr;
  reg [31:0] stageB_request_data;
  reg [1:0] stageB_request_size;
  reg  stageB_mmuRspFreeze;
  reg [31:0] stageB_mmuRsp_physicalAddress;
  reg  stageB_mmuRsp_isIoAccess;
  reg  stageB_mmuRsp_allowRead;
  reg  stageB_mmuRsp_allowWrite;
  reg  stageB_mmuRsp_allowExecute;
  reg  stageB_mmuRsp_exception;
  reg  stageB_mmuRsp_refilling;
  reg  stageB_tagsReadRsp_0_valid;
  reg  stageB_tagsReadRsp_0_error;
  reg [19:0] stageB_tagsReadRsp_0_address;
  reg [31:0] stageB_dataReadRsp_0;
  wire [0:0] _zz_8_;
  reg [0:0] stageB_waysHits;
  wire  stageB_waysHit;
  wire [31:0] stageB_dataMux;
  reg [3:0] stageB_mask;
  reg [0:0] stageB_colisions;
  reg  stageB_loaderValid;
  reg  stageB_flusher_valid;
  wire [31:0] stageB_requestDataBypass;
  wire  stageB_isAmo;
  reg  stageB_memCmdSent;
  wire [0:0] _zz_9_;
  reg  loader_valid;
  reg  loader_counter_willIncrement;
  wire  loader_counter_willClear;
  reg [2:0] loader_counter_valueNext;
  reg [2:0] loader_counter_value;
  wire  loader_counter_willOverflowIfInc;
  wire  loader_counter_willOverflow;
  reg [0:0] loader_waysAllocator;
  reg  loader_error;
  reg [21:0] ways_0_tags [0:127];
  reg [7:0] ways_0_data_symbol0 [0:1023];
  reg [7:0] ways_0_data_symbol1 [0:1023];
  reg [7:0] ways_0_data_symbol2 [0:1023];
  reg [7:0] ways_0_data_symbol3 [0:1023];
  reg [7:0] _zz_24_;
  reg [7:0] _zz_25_;
  reg [7:0] _zz_26_;
  reg [7:0] _zz_27_;
  assign _zz_12_ = (io_cpu_execute_isValid && (! io_cpu_memory_isStuck));
  assign _zz_13_ = (((stageB_mmuRsp_refilling || io_cpu_writeBack_accessError) || io_cpu_writeBack_mmuException) || io_cpu_writeBack_unalignedAccess);
  assign _zz_14_ = (stageB_waysHit || (stageB_request_wr && (! stageB_isAmo)));
  assign _zz_15_ = (loader_valid && io_mem_rsp_valid);
  assign _zz_16_ = ((((io_cpu_flush_valid && (! io_cpu_execute_isValid)) && (! io_cpu_memory_isValid)) && (! io_cpu_writeBack_isValid)) && (! io_cpu_redo));
  assign _zz_17_ = ((! io_cpu_writeBack_isStuck) && (! stageB_mmuRspFreeze));
  assign _zz_18_ = _zz_4_[0 : 0];
  assign _zz_19_ = _zz_4_[1 : 1];
  assign _zz_20_ = loader_counter_willIncrement;
  assign _zz_21_ = {2'd0, _zz_20_};
  assign _zz_22_ = {loader_waysAllocator,loader_waysAllocator[0]};
  assign _zz_23_ = {tagsWriteCmd_payload_data_address,{tagsWriteCmd_payload_data_error,tagsWriteCmd_payload_data_valid}};
  always @ (posedge clk) begin
    if(_zz_2_) begin
      ways_0_tags[tagsWriteCmd_payload_address] <= _zz_23_;
    end
  end

  always @ (posedge clk) begin
    if(_zz_3_) begin
      _zz_10_ <= ways_0_tags[tagsReadCmd_payload];
    end
  end

  always @ (*) begin
    _zz_11_ = {_zz_27_, _zz_26_, _zz_25_, _zz_24_};
  end
  always @ (posedge clk) begin
    if(dataWriteCmd_payload_mask[0] && _zz_1_) begin
      ways_0_data_symbol0[dataWriteCmd_payload_address] <= dataWriteCmd_payload_data[7 : 0];
    end
    if(dataWriteCmd_payload_mask[1] && _zz_1_) begin
      ways_0_data_symbol1[dataWriteCmd_payload_address] <= dataWriteCmd_payload_data[15 : 8];
    end
    if(dataWriteCmd_payload_mask[2] && _zz_1_) begin
      ways_0_data_symbol2[dataWriteCmd_payload_address] <= dataWriteCmd_payload_data[23 : 16];
    end
    if(dataWriteCmd_payload_mask[3] && _zz_1_) begin
      ways_0_data_symbol3[dataWriteCmd_payload_address] <= dataWriteCmd_payload_data[31 : 24];
    end
  end

  always @ (posedge clk) begin
    if(_zz_5_) begin
      _zz_24_ <= ways_0_data_symbol0[dataReadCmd_payload];
      _zz_25_ <= ways_0_data_symbol1[dataReadCmd_payload];
      _zz_26_ <= ways_0_data_symbol2[dataReadCmd_payload];
      _zz_27_ <= ways_0_data_symbol3[dataReadCmd_payload];
    end
  end

  always @ (*) begin
    _zz_1_ = 1'b0;
    if((dataWriteCmd_valid && dataWriteCmd_payload_way[0]))begin
      _zz_1_ = 1'b1;
    end
  end

  always @ (*) begin
    _zz_2_ = 1'b0;
    if((tagsWriteCmd_valid && tagsWriteCmd_payload_way[0]))begin
      _zz_2_ = 1'b1;
    end
  end

  assign haltCpu = 1'b0;
  assign _zz_3_ = (tagsReadCmd_valid && (! io_cpu_memory_isStuck));
  assign _zz_4_ = _zz_10_;
  assign ways_0_tagsReadRsp_valid = _zz_18_[0];
  assign ways_0_tagsReadRsp_error = _zz_19_[0];
  assign ways_0_tagsReadRsp_address = _zz_4_[21 : 2];
  assign _zz_5_ = (dataReadCmd_valid && (! io_cpu_memory_isStuck));
  assign ways_0_dataReadRsp = _zz_11_;
  always @ (*) begin
    tagsReadCmd_valid = 1'b0;
    if(_zz_12_)begin
      tagsReadCmd_valid = 1'b1;
    end
  end

  always @ (*) begin
    tagsReadCmd_payload = (7'bxxxxxxx);
    if(_zz_12_)begin
      tagsReadCmd_payload = io_cpu_execute_address[11 : 5];
    end
  end

  always @ (*) begin
    dataReadCmd_valid = 1'b0;
    if(_zz_12_)begin
      dataReadCmd_valid = 1'b1;
    end
  end

  always @ (*) begin
    dataReadCmd_payload = (10'bxxxxxxxxxx);
    if(_zz_12_)begin
      dataReadCmd_payload = io_cpu_execute_address[11 : 2];
    end
  end

  always @ (*) begin
    tagsWriteCmd_valid = 1'b0;
    if(stageB_flusher_valid)begin
      tagsWriteCmd_valid = stageB_flusher_valid;
    end
    if(_zz_13_)begin
      tagsWriteCmd_valid = 1'b0;
    end
    if(loader_counter_willOverflow)begin
      tagsWriteCmd_valid = 1'b1;
    end
  end

  always @ (*) begin
    tagsWriteCmd_payload_way = (1'bx);
    if(stageB_flusher_valid)begin
      tagsWriteCmd_payload_way = (1'b1);
    end
    if(loader_counter_willOverflow)begin
      tagsWriteCmd_payload_way = loader_waysAllocator;
    end
  end

  always @ (*) begin
    tagsWriteCmd_payload_address = (7'bxxxxxxx);
    if(stageB_flusher_valid)begin
      tagsWriteCmd_payload_address = stageB_mmuRsp_physicalAddress[11 : 5];
    end
    if(loader_counter_willOverflow)begin
      tagsWriteCmd_payload_address = stageB_mmuRsp_physicalAddress[11 : 5];
    end
  end

  always @ (*) begin
    tagsWriteCmd_payload_data_valid = 1'bx;
    if(stageB_flusher_valid)begin
      tagsWriteCmd_payload_data_valid = 1'b0;
    end
    if(loader_counter_willOverflow)begin
      tagsWriteCmd_payload_data_valid = 1'b1;
    end
  end

  always @ (*) begin
    tagsWriteCmd_payload_data_error = 1'bx;
    if(loader_counter_willOverflow)begin
      tagsWriteCmd_payload_data_error = (loader_error || io_mem_rsp_payload_error);
    end
  end

  always @ (*) begin
    tagsWriteCmd_payload_data_address = (20'bxxxxxxxxxxxxxxxxxxxx);
    if(loader_counter_willOverflow)begin
      tagsWriteCmd_payload_data_address = stageB_mmuRsp_physicalAddress[31 : 12];
    end
  end

  always @ (*) begin
    dataWriteCmd_valid = 1'b0;
    if(io_cpu_writeBack_isValid)begin
      if(! stageB_mmuRsp_isIoAccess) begin
        if(_zz_14_)begin
          if((stageB_request_wr && stageB_waysHit))begin
            dataWriteCmd_valid = 1'b1;
          end
        end
      end
    end
    if(_zz_13_)begin
      dataWriteCmd_valid = 1'b0;
    end
    if(_zz_15_)begin
      dataWriteCmd_valid = 1'b1;
    end
  end

  always @ (*) begin
    dataWriteCmd_payload_way = (1'bx);
    if(io_cpu_writeBack_isValid)begin
      if(! stageB_mmuRsp_isIoAccess) begin
        if(_zz_14_)begin
          dataWriteCmd_payload_way = stageB_waysHits;
        end
      end
    end
    if(_zz_15_)begin
      dataWriteCmd_payload_way = loader_waysAllocator;
    end
  end

  always @ (*) begin
    dataWriteCmd_payload_address = (10'bxxxxxxxxxx);
    if(io_cpu_writeBack_isValid)begin
      if(! stageB_mmuRsp_isIoAccess) begin
        if(_zz_14_)begin
          dataWriteCmd_payload_address = stageB_mmuRsp_physicalAddress[11 : 2];
        end
      end
    end
    if(_zz_15_)begin
      dataWriteCmd_payload_address = {stageB_mmuRsp_physicalAddress[11 : 5],loader_counter_value};
    end
  end

  always @ (*) begin
    dataWriteCmd_payload_data = (32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx);
    if(io_cpu_writeBack_isValid)begin
      if(! stageB_mmuRsp_isIoAccess) begin
        if(_zz_14_)begin
          dataWriteCmd_payload_data = stageB_requestDataBypass;
        end
      end
    end
    if(_zz_15_)begin
      dataWriteCmd_payload_data = io_mem_rsp_payload_data;
    end
  end

  always @ (*) begin
    dataWriteCmd_payload_mask = (4'bxxxx);
    if(io_cpu_writeBack_isValid)begin
      if(! stageB_mmuRsp_isIoAccess) begin
        if(_zz_14_)begin
          dataWriteCmd_payload_mask = stageB_mask;
        end
      end
    end
    if(_zz_15_)begin
      dataWriteCmd_payload_mask = (4'b1111);
    end
  end

  always @ (*) begin
    case(io_cpu_execute_args_size)
      2'b00 : begin
        _zz_6_ = (4'b0001);
      end
      2'b01 : begin
        _zz_6_ = (4'b0011);
      end
      default : begin
        _zz_6_ = (4'b1111);
      end
    endcase
  end

  assign stage0_mask = (_zz_6_ <<< io_cpu_execute_address[1 : 0]);
  assign stage0_colisions[0] = (((dataWriteCmd_valid && dataWriteCmd_payload_way[0]) && (dataWriteCmd_payload_address == io_cpu_execute_address[11 : 2])) && ((stage0_mask & dataWriteCmd_payload_mask) != (4'b0000)));
  assign io_cpu_memory_mmuBus_cmd_isValid = io_cpu_memory_isValid;
  assign io_cpu_memory_mmuBus_cmd_virtualAddress = io_cpu_memory_address;
  assign io_cpu_memory_mmuBus_cmd_bypassTranslation = 1'b0;
  assign io_cpu_memory_mmuBus_end = ((! io_cpu_memory_isStuck) || io_cpu_memory_isRemoved);
  assign io_cpu_memory_isWrite = stageA_request_wr;
  assign stageA_wayHits_0 = ((io_cpu_memory_mmuBus_rsp_physicalAddress[31 : 12] == ways_0_tagsReadRsp_address) && ways_0_tagsReadRsp_valid);
  assign _zz_7_[0] = (((dataWriteCmd_valid && dataWriteCmd_payload_way[0]) && (dataWriteCmd_payload_address == io_cpu_memory_address[11 : 2])) && ((stageA_mask & dataWriteCmd_payload_mask) != (4'b0000)));
  assign stageA_colisions = (stage0_colisions_regNextWhen | _zz_7_);
  always @ (*) begin
    stageB_mmuRspFreeze = 1'b0;
    if((stageB_loaderValid || loader_valid))begin
      stageB_mmuRspFreeze = 1'b1;
    end
  end

  assign _zz_8_[0] = stageA_wayHits_0;
  assign stageB_waysHit = (stageB_waysHits != (1'b0));
  assign stageB_dataMux = stageB_dataReadRsp_0;
  always @ (*) begin
    stageB_loaderValid = 1'b0;
    if(io_cpu_writeBack_isValid)begin
      if(! stageB_mmuRsp_isIoAccess) begin
        if(! _zz_14_) begin
          if(io_mem_cmd_ready)begin
            stageB_loaderValid = 1'b1;
          end
        end
      end
    end
    if(_zz_13_)begin
      stageB_loaderValid = 1'b0;
    end
  end

  always @ (*) begin
    io_cpu_writeBack_haltIt = io_cpu_writeBack_isValid;
    if(stageB_flusher_valid)begin
      io_cpu_writeBack_haltIt = 1'b1;
    end
    if(io_cpu_writeBack_isValid)begin
      if(stageB_mmuRsp_isIoAccess)begin
        if((stageB_request_wr ? io_mem_cmd_ready : io_mem_rsp_valid))begin
          io_cpu_writeBack_haltIt = 1'b0;
        end
      end else begin
        if(_zz_14_)begin
          if(((! stageB_request_wr) || io_mem_cmd_ready))begin
            io_cpu_writeBack_haltIt = 1'b0;
          end
        end
      end
    end
    if(_zz_13_)begin
      io_cpu_writeBack_haltIt = 1'b0;
    end
  end

  always @ (*) begin
    io_cpu_flush_ready = 1'b0;
    if(_zz_16_)begin
      io_cpu_flush_ready = 1'b1;
    end
  end

  assign stageB_requestDataBypass = stageB_request_data;
  assign stageB_isAmo = 1'b0;
  always @ (*) begin
    io_cpu_redo = 1'b0;
    if(io_cpu_writeBack_isValid)begin
      if(! stageB_mmuRsp_isIoAccess) begin
        if(_zz_14_)begin
          if((((! stageB_request_wr) || stageB_isAmo) && ((stageB_colisions & stageB_waysHits) != (1'b0))))begin
            io_cpu_redo = 1'b1;
          end
        end
      end
    end
    if((io_cpu_writeBack_isValid && stageB_mmuRsp_refilling))begin
      io_cpu_redo = 1'b1;
    end
    if(loader_valid)begin
      io_cpu_redo = 1'b1;
    end
  end

  always @ (*) begin
    io_cpu_writeBack_accessError = 1'b0;
    if(stageB_mmuRsp_isIoAccess)begin
      io_cpu_writeBack_accessError = (io_mem_rsp_valid && io_mem_rsp_payload_error);
    end else begin
      io_cpu_writeBack_accessError = ((stageB_waysHits & _zz_9_) != (1'b0));
    end
  end

  assign io_cpu_writeBack_mmuException = (io_cpu_writeBack_isValid && ((stageB_mmuRsp_exception || ((! stageB_mmuRsp_allowWrite) && stageB_request_wr)) || ((! stageB_mmuRsp_allowRead) && ((! stageB_request_wr) || stageB_isAmo))));
  assign io_cpu_writeBack_unalignedAccess = (io_cpu_writeBack_isValid && (((stageB_request_size == (2'b10)) && (stageB_mmuRsp_physicalAddress[1 : 0] != (2'b00))) || ((stageB_request_size == (2'b01)) && (stageB_mmuRsp_physicalAddress[0 : 0] != (1'b0)))));
  assign io_cpu_writeBack_isWrite = stageB_request_wr;
  always @ (*) begin
    io_mem_cmd_valid = 1'b0;
    if(io_cpu_writeBack_isValid)begin
      if(stageB_mmuRsp_isIoAccess)begin
        io_mem_cmd_valid = (! stageB_memCmdSent);
      end else begin
        if(_zz_14_)begin
          if(stageB_request_wr)begin
            io_mem_cmd_valid = 1'b1;
          end
        end else begin
          if((! stageB_memCmdSent))begin
            io_mem_cmd_valid = 1'b1;
          end
        end
      end
    end
    if(_zz_13_)begin
      io_mem_cmd_valid = 1'b0;
    end
  end

  always @ (*) begin
    io_mem_cmd_payload_address = (32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx);
    if(io_cpu_writeBack_isValid)begin
      if(stageB_mmuRsp_isIoAccess)begin
        io_mem_cmd_payload_address = {stageB_mmuRsp_physicalAddress[31 : 2],(2'b00)};
      end else begin
        if(_zz_14_)begin
          io_mem_cmd_payload_address = {stageB_mmuRsp_physicalAddress[31 : 2],(2'b00)};
        end else begin
          io_mem_cmd_payload_address = {stageB_mmuRsp_physicalAddress[31 : 5],(5'b00000)};
        end
      end
    end
  end

  always @ (*) begin
    io_mem_cmd_payload_length = (3'bxxx);
    if(io_cpu_writeBack_isValid)begin
      if(stageB_mmuRsp_isIoAccess)begin
        io_mem_cmd_payload_length = (3'b000);
      end else begin
        if(_zz_14_)begin
          io_mem_cmd_payload_length = (3'b000);
        end else begin
          io_mem_cmd_payload_length = (3'b111);
        end
      end
    end
  end

  always @ (*) begin
    io_mem_cmd_payload_last = 1'bx;
    if(io_cpu_writeBack_isValid)begin
      if(stageB_mmuRsp_isIoAccess)begin
        io_mem_cmd_payload_last = 1'b1;
      end else begin
        if(_zz_14_)begin
          io_mem_cmd_payload_last = 1'b1;
        end else begin
          io_mem_cmd_payload_last = 1'b1;
        end
      end
    end
  end

  always @ (*) begin
    io_mem_cmd_payload_wr = stageB_request_wr;
    if(io_cpu_writeBack_isValid)begin
      if(! stageB_mmuRsp_isIoAccess) begin
        if(! _zz_14_) begin
          io_mem_cmd_payload_wr = 1'b0;
        end
      end
    end
  end

  assign io_mem_cmd_payload_mask = stageB_mask;
  assign io_mem_cmd_payload_data = stageB_requestDataBypass;
  always @ (*) begin
    if(stageB_mmuRsp_isIoAccess)begin
      io_cpu_writeBack_data = io_mem_rsp_payload_data;
    end else begin
      io_cpu_writeBack_data = stageB_dataMux;
    end
  end

  assign _zz_9_[0] = stageB_tagsReadRsp_0_error;
  always @ (*) begin
    loader_counter_willIncrement = 1'b0;
    if(_zz_15_)begin
      loader_counter_willIncrement = 1'b1;
    end
  end

  assign loader_counter_willClear = 1'b0;
  assign loader_counter_willOverflowIfInc = (loader_counter_value == (3'b111));
  assign loader_counter_willOverflow = (loader_counter_willOverflowIfInc && loader_counter_willIncrement);
  always @ (*) begin
    loader_counter_valueNext = (loader_counter_value + _zz_21_);
    if(loader_counter_willClear)begin
      loader_counter_valueNext = (3'b000);
    end
  end

  always @ (posedge clk) begin
    tagsWriteLastCmd_valid <= tagsWriteCmd_valid;
    tagsWriteLastCmd_payload_way <= tagsWriteCmd_payload_way;
    tagsWriteLastCmd_payload_address <= tagsWriteCmd_payload_address;
    tagsWriteLastCmd_payload_data_valid <= tagsWriteCmd_payload_data_valid;
    tagsWriteLastCmd_payload_data_error <= tagsWriteCmd_payload_data_error;
    tagsWriteLastCmd_payload_data_address <= tagsWriteCmd_payload_data_address;
    if((! io_cpu_memory_isStuck))begin
      stageA_request_wr <= io_cpu_execute_args_wr;
      stageA_request_data <= io_cpu_execute_args_data;
      stageA_request_size <= io_cpu_execute_args_size;
    end
    if((! io_cpu_memory_isStuck))begin
      stageA_mask <= stage0_mask;
    end
    if((! io_cpu_memory_isStuck))begin
      stage0_colisions_regNextWhen <= stage0_colisions;
    end
    if((! io_cpu_writeBack_isStuck))begin
      stageB_request_wr <= stageA_request_wr;
      stageB_request_data <= stageA_request_data;
      stageB_request_size <= stageA_request_size;
    end
    if(_zz_17_)begin
      stageB_mmuRsp_isIoAccess <= io_cpu_memory_mmuBus_rsp_isIoAccess;
      stageB_mmuRsp_allowRead <= io_cpu_memory_mmuBus_rsp_allowRead;
      stageB_mmuRsp_allowWrite <= io_cpu_memory_mmuBus_rsp_allowWrite;
      stageB_mmuRsp_allowExecute <= io_cpu_memory_mmuBus_rsp_allowExecute;
      stageB_mmuRsp_exception <= io_cpu_memory_mmuBus_rsp_exception;
      stageB_mmuRsp_refilling <= io_cpu_memory_mmuBus_rsp_refilling;
    end
    if((! io_cpu_writeBack_isStuck))begin
      stageB_tagsReadRsp_0_valid <= ways_0_tagsReadRsp_valid;
      stageB_tagsReadRsp_0_error <= ways_0_tagsReadRsp_error;
      stageB_tagsReadRsp_0_address <= ways_0_tagsReadRsp_address;
    end
    if((! io_cpu_writeBack_isStuck))begin
      stageB_dataReadRsp_0 <= ways_0_dataReadRsp;
    end
    if((! io_cpu_writeBack_isStuck))begin
      stageB_waysHits <= _zz_8_;
    end
    if((! io_cpu_writeBack_isStuck))begin
      stageB_mask <= stageA_mask;
    end
    if((! io_cpu_writeBack_isStuck))begin
      stageB_colisions <= stageA_colisions;
    end
    if(!(! ((io_cpu_writeBack_isValid && (! io_cpu_writeBack_haltIt)) && io_cpu_writeBack_isStuck))) begin
      $display("ERROR writeBack stuck by another plugin is not allowed");
    end
  end

  always @ (posedge clk or posedge reset) begin
    if (reset) begin
      stageB_flusher_valid <= 1'b1;
      stageB_mmuRsp_physicalAddress <= (32'b00000000000000000000000000000000);
      stageB_memCmdSent <= 1'b0;
      loader_valid <= 1'b0;
      loader_counter_value <= (3'b000);
      loader_waysAllocator <= (1'b1);
      loader_error <= 1'b0;
    end else begin
      if(_zz_17_)begin
        stageB_mmuRsp_physicalAddress <= io_cpu_memory_mmuBus_rsp_physicalAddress;
      end
      if(stageB_flusher_valid)begin
        if((stageB_mmuRsp_physicalAddress[11 : 5] != (7'b1111111)))begin
          stageB_mmuRsp_physicalAddress[11 : 5] <= (stageB_mmuRsp_physicalAddress[11 : 5] + (7'b0000001));
        end else begin
          stageB_flusher_valid <= 1'b0;
        end
      end
      if(_zz_16_)begin
        stageB_mmuRsp_physicalAddress[11 : 5] <= (7'b0000000);
        stageB_flusher_valid <= 1'b1;
      end
      if(io_mem_cmd_ready)begin
        stageB_memCmdSent <= 1'b1;
      end
      if((! io_cpu_writeBack_isStuck))begin
        stageB_memCmdSent <= 1'b0;
      end
      if(stageB_loaderValid)begin
        loader_valid <= 1'b1;
      end
      loader_counter_value <= loader_counter_valueNext;
      if(_zz_15_)begin
        loader_error <= (loader_error || io_mem_rsp_payload_error);
      end
      if(loader_counter_willOverflow)begin
        loader_valid <= 1'b0;
        loader_waysAllocator <= _zz_22_[0:0];
        loader_error <= 1'b0;
      end
    end
  end

endmodule

module \vexriscv.demo.GenFull (
      input   timerInterrupt,
      input   externalInterrupt,
      input   softwareInterrupt,
      input   debug_bus_cmd_valid,
      output reg  debug_bus_cmd_ready,
      input   debug_bus_cmd_payload_wr,
      input  [7:0] debug_bus_cmd_payload_address,
      input  [31:0] debug_bus_cmd_payload_data,
      output reg [31:0] debug_bus_rsp_data,
      output  debug_resetOut,
      output  iBus_cmd_valid,
      input   iBus_cmd_ready,
      output reg [31:0] iBus_cmd_payload_address,
      output [2:0] iBus_cmd_payload_size,
      input   iBus_rsp_valid,
      input  [31:0] iBus_rsp_payload_data,
      input   iBus_rsp_payload_error,
      output  dBus_cmd_valid,
      input   dBus_cmd_ready,
      output  dBus_cmd_payload_wr,
      output [31:0] dBus_cmd_payload_address,
      output [31:0] dBus_cmd_payload_data,
      output [3:0] dBus_cmd_payload_mask,
      output [2:0] dBus_cmd_payload_length,
      output  dBus_cmd_payload_last,
      input   dBus_rsp_valid,
      input  [31:0] dBus_rsp_payload_data,
      input   dBus_rsp_payload_error,
      input   clk,
      input   reset,
      input   debugReset);
  wire  _zz_221_;
  wire  _zz_222_;
  wire  _zz_223_;
  wire  _zz_224_;
  wire  _zz_225_;
  wire [31:0] _zz_226_;
  wire  _zz_227_;
  wire  _zz_228_;
  wire  _zz_229_;
  reg  _zz_230_;
  reg  _zz_231_;
  reg [31:0] _zz_232_;
  reg  _zz_233_;
  reg [31:0] _zz_234_;
  reg [1:0] _zz_235_;
  reg  _zz_236_;
  wire [31:0] _zz_237_;
  reg  _zz_238_;
  reg  _zz_239_;
  wire  _zz_240_;
  wire [31:0] _zz_241_;
  wire  _zz_242_;
  reg [1:0] _zz_243_;
  reg [31:0] _zz_244_;
  reg [31:0] _zz_245_;
  reg [31:0] _zz_246_;
  reg  _zz_247_;
  reg  _zz_248_;
  reg  _zz_249_;
  reg [9:0] _zz_250_;
  reg [9:0] _zz_251_;
  reg [9:0] _zz_252_;
  reg [9:0] _zz_253_;
  reg  _zz_254_;
  reg  _zz_255_;
  reg  _zz_256_;
  reg  _zz_257_;
  reg  _zz_258_;
  reg  _zz_259_;
  reg  _zz_260_;
  reg [9:0] _zz_261_;
  reg [9:0] _zz_262_;
  reg [9:0] _zz_263_;
  reg [9:0] _zz_264_;
  reg  _zz_265_;
  reg  _zz_266_;
  reg  _zz_267_;
  reg  _zz_268_;
  wire  IBusCachedPlugin_cache_io_cpu_prefetch_haltIt;
  wire [31:0] IBusCachedPlugin_cache_io_cpu_fetch_data;
  wire [31:0] IBusCachedPlugin_cache_io_cpu_fetch_physicalAddress;
  wire  IBusCachedPlugin_cache_io_cpu_fetch_haltIt;
  wire  IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_cmd_isValid;
  wire [31:0] IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_cmd_virtualAddress;
  wire  IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_cmd_bypassTranslation;
  wire  IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_end;
  wire  IBusCachedPlugin_cache_io_cpu_decode_error;
  wire  IBusCachedPlugin_cache_io_cpu_decode_mmuRefilling;
  wire  IBusCachedPlugin_cache_io_cpu_decode_mmuException;
  wire [31:0] IBusCachedPlugin_cache_io_cpu_decode_data;
  wire  IBusCachedPlugin_cache_io_cpu_decode_cacheMiss;
  wire [31:0] IBusCachedPlugin_cache_io_cpu_decode_physicalAddress;
  wire  IBusCachedPlugin_cache_io_mem_cmd_valid;
  wire [31:0] IBusCachedPlugin_cache_io_mem_cmd_payload_address;
  wire [2:0] IBusCachedPlugin_cache_io_mem_cmd_payload_size;
  wire  dataCache_1__io_cpu_memory_isWrite;
  wire  dataCache_1__io_cpu_memory_mmuBus_cmd_isValid;
  wire [31:0] dataCache_1__io_cpu_memory_mmuBus_cmd_virtualAddress;
  wire  dataCache_1__io_cpu_memory_mmuBus_cmd_bypassTranslation;
  wire  dataCache_1__io_cpu_memory_mmuBus_end;
  wire  dataCache_1__io_cpu_writeBack_haltIt;
  wire [31:0] dataCache_1__io_cpu_writeBack_data;
  wire  dataCache_1__io_cpu_writeBack_mmuException;
  wire  dataCache_1__io_cpu_writeBack_unalignedAccess;
  wire  dataCache_1__io_cpu_writeBack_accessError;
  wire  dataCache_1__io_cpu_writeBack_isWrite;
  wire  dataCache_1__io_cpu_flush_ready;
  wire  dataCache_1__io_cpu_redo;
  wire  dataCache_1__io_mem_cmd_valid;
  wire  dataCache_1__io_mem_cmd_payload_wr;
  wire [31:0] dataCache_1__io_mem_cmd_payload_address;
  wire [31:0] dataCache_1__io_mem_cmd_payload_data;
  wire [3:0] dataCache_1__io_mem_cmd_payload_mask;
  wire [2:0] dataCache_1__io_mem_cmd_payload_length;
  wire  dataCache_1__io_mem_cmd_payload_last;
  wire  _zz_269_;
  wire  _zz_270_;
  wire  _zz_271_;
  wire  _zz_272_;
  wire  _zz_273_;
  wire  _zz_274_;
  wire  _zz_275_;
  wire  _zz_276_;
  wire  _zz_277_;
  wire  _zz_278_;
  wire  _zz_279_;
  wire  _zz_280_;
  wire  _zz_281_;
  wire  _zz_282_;
  wire  _zz_283_;
  wire  _zz_284_;
  wire  _zz_285_;
  wire [1:0] _zz_286_;
  wire  _zz_287_;
  wire  _zz_288_;
  wire  _zz_289_;
  wire  _zz_290_;
  wire  _zz_291_;
  wire  _zz_292_;
  wire  _zz_293_;
  wire  _zz_294_;
  wire  _zz_295_;
  wire  _zz_296_;
  wire  _zz_297_;
  wire  _zz_298_;
  wire  _zz_299_;
  wire [1:0] _zz_300_;
  wire  _zz_301_;
  wire  _zz_302_;
  wire  _zz_303_;
  wire  _zz_304_;
  wire  _zz_305_;
  wire [5:0] _zz_306_;
  wire  _zz_307_;
  wire  _zz_308_;
  wire  _zz_309_;
  wire  _zz_310_;
  wire  _zz_311_;
  wire  _zz_312_;
  wire  _zz_313_;
  wire  _zz_314_;
  wire  _zz_315_;
  wire  _zz_316_;
  wire  _zz_317_;
  wire  _zz_318_;
  wire [1:0] _zz_319_;
  wire [1:0] _zz_320_;
  wire  _zz_321_;
  wire [4:0] _zz_322_;
  wire [2:0] _zz_323_;
  wire [31:0] _zz_324_;
  wire [1:0] _zz_325_;
  wire [1:0] _zz_326_;
  wire [1:0] _zz_327_;
  wire [1:0] _zz_328_;
  wire [9:0] _zz_329_;
  wire [29:0] _zz_330_;
  wire [9:0] _zz_331_;
  wire [1:0] _zz_332_;
  wire [1:0] _zz_333_;
  wire [1:0] _zz_334_;
  wire [19:0] _zz_335_;
  wire [11:0] _zz_336_;
  wire [31:0] _zz_337_;
  wire [31:0] _zz_338_;
  wire [19:0] _zz_339_;
  wire [11:0] _zz_340_;
  wire [2:0] _zz_341_;
  wire [2:0] _zz_342_;
  wire [0:0] _zz_343_;
  wire [2:0] _zz_344_;
  wire [0:0] _zz_345_;
  wire [1:0] _zz_346_;
  wire [0:0] _zz_347_;
  wire [0:0] _zz_348_;
  wire [0:0] _zz_349_;
  wire [0:0] _zz_350_;
  wire [0:0] _zz_351_;
  wire [0:0] _zz_352_;
  wire [0:0] _zz_353_;
  wire [0:0] _zz_354_;
  wire [0:0] _zz_355_;
  wire [0:0] _zz_356_;
  wire [0:0] _zz_357_;
  wire [0:0] _zz_358_;
  wire [0:0] _zz_359_;
  wire [0:0] _zz_360_;
  wire [0:0] _zz_361_;
  wire [0:0] _zz_362_;
  wire [0:0] _zz_363_;
  wire [0:0] _zz_364_;
  wire [0:0] _zz_365_;
  wire [0:0] _zz_366_;
  wire [0:0] _zz_367_;
  wire [0:0] _zz_368_;
  wire [0:0] _zz_369_;
  wire [0:0] _zz_370_;
  wire [0:0] _zz_371_;
  wire [0:0] _zz_372_;
  wire [0:0] _zz_373_;
  wire [0:0] _zz_374_;
  wire [2:0] _zz_375_;
  wire [4:0] _zz_376_;
  wire [11:0] _zz_377_;
  wire [11:0] _zz_378_;
  wire [31:0] _zz_379_;
  wire [31:0] _zz_380_;
  wire [31:0] _zz_381_;
  wire [31:0] _zz_382_;
  wire [31:0] _zz_383_;
  wire [31:0] _zz_384_;
  wire [31:0] _zz_385_;
  wire [32:0] _zz_386_;
  wire [31:0] _zz_387_;
  wire [32:0] _zz_388_;
  wire [51:0] _zz_389_;
  wire [51:0] _zz_390_;
  wire [51:0] _zz_391_;
  wire [32:0] _zz_392_;
  wire [51:0] _zz_393_;
  wire [49:0] _zz_394_;
  wire [51:0] _zz_395_;
  wire [49:0] _zz_396_;
  wire [51:0] _zz_397_;
  wire [65:0] _zz_398_;
  wire [65:0] _zz_399_;
  wire [31:0] _zz_400_;
  wire [31:0] _zz_401_;
  wire [0:0] _zz_402_;
  wire [5:0] _zz_403_;
  wire [32:0] _zz_404_;
  wire [32:0] _zz_405_;
  wire [31:0] _zz_406_;
  wire [31:0] _zz_407_;
  wire [32:0] _zz_408_;
  wire [32:0] _zz_409_;
  wire [32:0] _zz_410_;
  wire [0:0] _zz_411_;
  wire [32:0] _zz_412_;
  wire [0:0] _zz_413_;
  wire [32:0] _zz_414_;
  wire [0:0] _zz_415_;
  wire [31:0] _zz_416_;
  wire [1:0] _zz_417_;
  wire [1:0] _zz_418_;
  wire [11:0] _zz_419_;
  wire [19:0] _zz_420_;
  wire [11:0] _zz_421_;
  wire [31:0] _zz_422_;
  wire [31:0] _zz_423_;
  wire [31:0] _zz_424_;
  wire [11:0] _zz_425_;
  wire [19:0] _zz_426_;
  wire [11:0] _zz_427_;
  wire [2:0] _zz_428_;
  wire [0:0] _zz_429_;
  wire [0:0] _zz_430_;
  wire [0:0] _zz_431_;
  wire [0:0] _zz_432_;
  wire [0:0] _zz_433_;
  wire [0:0] _zz_434_;
  wire [0:0] _zz_435_;
  wire [0:0] _zz_436_;
  wire [0:0] _zz_437_;
  wire [0:0] _zz_438_;
  wire [0:0] _zz_439_;
  wire [0:0] _zz_440_;
  wire [0:0] _zz_441_;
  wire [1:0] _zz_442_;
  wire  _zz_443_;
  wire  _zz_444_;
  wire [2:0] _zz_445_;
  wire  _zz_446_;
  wire  _zz_447_;
  wire  _zz_448_;
  wire [31:0] _zz_449_;
  wire  _zz_450_;
  wire [0:0] _zz_451_;
  wire [0:0] _zz_452_;
  wire [3:0] _zz_453_;
  wire [3:0] _zz_454_;
  wire  _zz_455_;
  wire [0:0] _zz_456_;
  wire [26:0] _zz_457_;
  wire [31:0] _zz_458_;
  wire [31:0] _zz_459_;
  wire [31:0] _zz_460_;
  wire  _zz_461_;
  wire [0:0] _zz_462_;
  wire [0:0] _zz_463_;
  wire [31:0] _zz_464_;
  wire [31:0] _zz_465_;
  wire [0:0] _zz_466_;
  wire [4:0] _zz_467_;
  wire [4:0] _zz_468_;
  wire [4:0] _zz_469_;
  wire  _zz_470_;
  wire [0:0] _zz_471_;
  wire [23:0] _zz_472_;
  wire [31:0] _zz_473_;
  wire [31:0] _zz_474_;
  wire [31:0] _zz_475_;
  wire [31:0] _zz_476_;
  wire [31:0] _zz_477_;
  wire  _zz_478_;
  wire [0:0] _zz_479_;
  wire [2:0] _zz_480_;
  wire  _zz_481_;
  wire [0:0] _zz_482_;
  wire [2:0] _zz_483_;
  wire [0:0] _zz_484_;
  wire [0:0] _zz_485_;
  wire [0:0] _zz_486_;
  wire [0:0] _zz_487_;
  wire  _zz_488_;
  wire [0:0] _zz_489_;
  wire [21:0] _zz_490_;
  wire [31:0] _zz_491_;
  wire [31:0] _zz_492_;
  wire [31:0] _zz_493_;
  wire  _zz_494_;
  wire [0:0] _zz_495_;
  wire [0:0] _zz_496_;
  wire [31:0] _zz_497_;
  wire  _zz_498_;
  wire [0:0] _zz_499_;
  wire [0:0] _zz_500_;
  wire [31:0] _zz_501_;
  wire [31:0] _zz_502_;
  wire [31:0] _zz_503_;
  wire [31:0] _zz_504_;
  wire [31:0] _zz_505_;
  wire [31:0] _zz_506_;
  wire [0:0] _zz_507_;
  wire [0:0] _zz_508_;
  wire [0:0] _zz_509_;
  wire [0:0] _zz_510_;
  wire  _zz_511_;
  wire [0:0] _zz_512_;
  wire [19:0] _zz_513_;
  wire [31:0] _zz_514_;
  wire [31:0] _zz_515_;
  wire [31:0] _zz_516_;
  wire [31:0] _zz_517_;
  wire [31:0] _zz_518_;
  wire [31:0] _zz_519_;
  wire [31:0] _zz_520_;
  wire [31:0] _zz_521_;
  wire [31:0] _zz_522_;
  wire [31:0] _zz_523_;
  wire [31:0] _zz_524_;
  wire [31:0] _zz_525_;
  wire [31:0] _zz_526_;
  wire [31:0] _zz_527_;
  wire [0:0] _zz_528_;
  wire [0:0] _zz_529_;
  wire  _zz_530_;
  wire [0:0] _zz_531_;
  wire [17:0] _zz_532_;
  wire [31:0] _zz_533_;
  wire [31:0] _zz_534_;
  wire [31:0] _zz_535_;
  wire [31:0] _zz_536_;
  wire  _zz_537_;
  wire [0:0] _zz_538_;
  wire [0:0] _zz_539_;
  wire  _zz_540_;
  wire [0:0] _zz_541_;
  wire [0:0] _zz_542_;
  wire  _zz_543_;
  wire [0:0] _zz_544_;
  wire [13:0] _zz_545_;
  wire [31:0] _zz_546_;
  wire [31:0] _zz_547_;
  wire [31:0] _zz_548_;
  wire  _zz_549_;
  wire [0:0] _zz_550_;
  wire [0:0] _zz_551_;
  wire [0:0] _zz_552_;
  wire [0:0] _zz_553_;
  wire [0:0] _zz_554_;
  wire [0:0] _zz_555_;
  wire  _zz_556_;
  wire [0:0] _zz_557_;
  wire [10:0] _zz_558_;
  wire [31:0] _zz_559_;
  wire [31:0] _zz_560_;
  wire [31:0] _zz_561_;
  wire [31:0] _zz_562_;
  wire [31:0] _zz_563_;
  wire [31:0] _zz_564_;
  wire [31:0] _zz_565_;
  wire  _zz_566_;
  wire [2:0] _zz_567_;
  wire [2:0] _zz_568_;
  wire  _zz_569_;
  wire [0:0] _zz_570_;
  wire [7:0] _zz_571_;
  wire [31:0] _zz_572_;
  wire [31:0] _zz_573_;
  wire  _zz_574_;
  wire  _zz_575_;
  wire [31:0] _zz_576_;
  wire [31:0] _zz_577_;
  wire [0:0] _zz_578_;
  wire [3:0] _zz_579_;
  wire [0:0] _zz_580_;
  wire [0:0] _zz_581_;
  wire  _zz_582_;
  wire [0:0] _zz_583_;
  wire [4:0] _zz_584_;
  wire [31:0] _zz_585_;
  wire [31:0] _zz_586_;
  wire  _zz_587_;
  wire [0:0] _zz_588_;
  wire [0:0] _zz_589_;
  wire [31:0] _zz_590_;
  wire [31:0] _zz_591_;
  wire [31:0] _zz_592_;
  wire [0:0] _zz_593_;
  wire [0:0] _zz_594_;
  wire [0:0] _zz_595_;
  wire [0:0] _zz_596_;
  wire  _zz_597_;
  wire [0:0] _zz_598_;
  wire [1:0] _zz_599_;
  wire [31:0] _zz_600_;
  wire [31:0] _zz_601_;
  wire [31:0] _zz_602_;
  wire [31:0] _zz_603_;
  wire [31:0] _zz_604_;
  wire [31:0] _zz_605_;
  wire [0:0] _zz_606_;
  wire [0:0] _zz_607_;
  wire [1:0] _zz_608_;
  wire [1:0] _zz_609_;
  wire [0:0] _zz_610_;
  wire [0:0] _zz_611_;
  wire [31:0] _zz_612_;
  wire [31:0] _zz_613_;
  wire [31:0] _zz_614_;
  wire  _zz_615_;
  wire [0:0] _zz_616_;
  wire [13:0] _zz_617_;
  wire [31:0] _zz_618_;
  wire [31:0] _zz_619_;
  wire [31:0] _zz_620_;
  wire  _zz_621_;
  wire [0:0] _zz_622_;
  wire [7:0] _zz_623_;
  wire [31:0] _zz_624_;
  wire [31:0] _zz_625_;
  wire [31:0] _zz_626_;
  wire  _zz_627_;
  wire [0:0] _zz_628_;
  wire [1:0] _zz_629_;
  wire  _zz_630_;
  wire  _zz_631_;
  wire  _zz_632_;
  wire `ShiftCtrlEnum_defaultEncoding_type _zz_1_;
  wire `ShiftCtrlEnum_defaultEncoding_type _zz_2_;
  wire `ShiftCtrlEnum_defaultEncoding_type decode_SHIFT_CTRL;
  wire `ShiftCtrlEnum_defaultEncoding_type _zz_3_;
  wire `ShiftCtrlEnum_defaultEncoding_type _zz_4_;
  wire `ShiftCtrlEnum_defaultEncoding_type _zz_5_;
  wire  decode_SRC_LESS_UNSIGNED;
  wire  decode_IS_CSR;
  wire  decode_BYPASSABLE_EXECUTE_STAGE;
  wire  decode_SRC2_FORCE_ZERO;
  wire  memory_MEMORY_WR;
  wire  decode_MEMORY_WR;
  wire `AluBitwiseCtrlEnum_defaultEncoding_type decode_ALU_BITWISE_CTRL;
  wire `AluBitwiseCtrlEnum_defaultEncoding_type _zz_6_;
  wire `AluBitwiseCtrlEnum_defaultEncoding_type _zz_7_;
  wire `AluBitwiseCtrlEnum_defaultEncoding_type _zz_8_;
  wire  decode_IS_RS2_SIGNED;
  wire `Src1CtrlEnum_defaultEncoding_type decode_SRC1_CTRL;
  wire `Src1CtrlEnum_defaultEncoding_type _zz_9_;
  wire `Src1CtrlEnum_defaultEncoding_type _zz_10_;
  wire `Src1CtrlEnum_defaultEncoding_type _zz_11_;
  wire [33:0] memory_MUL_HH;
  wire [33:0] execute_MUL_HH;
  wire  decode_IS_RS1_SIGNED;
  wire `Src2CtrlEnum_defaultEncoding_type decode_SRC2_CTRL;
  wire `Src2CtrlEnum_defaultEncoding_type _zz_12_;
  wire `Src2CtrlEnum_defaultEncoding_type _zz_13_;
  wire `Src2CtrlEnum_defaultEncoding_type _zz_14_;
  wire  decode_IS_DIV;
  wire [31:0] writeBack_FORMAL_PC_NEXT;
  wire [31:0] memory_FORMAL_PC_NEXT;
  wire [31:0] execute_FORMAL_PC_NEXT;
  wire [31:0] decode_FORMAL_PC_NEXT;
  wire  decode_CSR_READ_OPCODE;
  wire `AluCtrlEnum_defaultEncoding_type decode_ALU_CTRL;
  wire `AluCtrlEnum_defaultEncoding_type _zz_15_;
  wire `AluCtrlEnum_defaultEncoding_type _zz_16_;
  wire `AluCtrlEnum_defaultEncoding_type _zz_17_;
  wire  execute_IS_DBUS_SHARING;
  wire [31:0] execute_REGFILE_WRITE_DATA;
  wire [1:0] memory_MEMORY_ADDRESS_LOW;
  wire [1:0] execute_MEMORY_ADDRESS_LOW;
  wire  decode_PREDICTION_HAD_BRANCHED2;
  wire [31:0] execute_BRANCH_CALC;
  wire [31:0] execute_MUL_LL;
  wire  decode_DO_EBREAK;
  wire  execute_PREDICTION_CONTEXT_hazard;
  wire [1:0] execute_PREDICTION_CONTEXT_line_history;
  wire  decode_CSR_WRITE_OPCODE;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_18_;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_19_;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_20_;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_21_;
  wire `EnvCtrlEnum_defaultEncoding_type decode_ENV_CTRL;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_22_;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_23_;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_24_;
  wire  execute_BRANCH_DO;
  wire [51:0] memory_MUL_LOW;
  wire `BranchCtrlEnum_defaultEncoding_type _zz_25_;
  wire `BranchCtrlEnum_defaultEncoding_type _zz_26_;
  wire `BranchCtrlEnum_defaultEncoding_type _zz_27_;
  wire `BranchCtrlEnum_defaultEncoding_type _zz_28_;
  wire  execute_BYPASSABLE_MEMORY_STAGE;
  wire  decode_BYPASSABLE_MEMORY_STAGE;
  wire  memory_IS_MUL;
  wire  execute_IS_MUL;
  wire  decode_IS_MUL;
  wire [31:0] execute_SHIFT_RIGHT;
  wire [33:0] execute_MUL_LH;
  wire [33:0] execute_MUL_HL;
  wire  decode_MEMORY_MANAGMENT;
  wire  memory_IS_SFENCE_VMA;
  wire  execute_IS_SFENCE_VMA;
  wire  decode_IS_SFENCE_VMA;
  wire [31:0] memory_BRANCH_CALC;
  wire  memory_BRANCH_DO;
  wire [31:0] _zz_29_;
  wire  execute_PREDICTION_HAD_BRANCHED2;
  wire  _zz_30_;
  wire  execute_BRANCH_COND_RESULT;
  wire `BranchCtrlEnum_defaultEncoding_type execute_BRANCH_CTRL;
  wire `BranchCtrlEnum_defaultEncoding_type _zz_31_;
  wire  _zz_32_;
  wire  _zz_33_;
  wire [31:0] execute_PC;
  wire  execute_DO_EBREAK;
  wire  decode_IS_EBREAK;
  wire  _zz_34_;
  wire  execute_CSR_READ_OPCODE;
  wire  execute_CSR_WRITE_OPCODE;
  wire  execute_IS_CSR;
  wire `EnvCtrlEnum_defaultEncoding_type memory_ENV_CTRL;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_35_;
  wire `EnvCtrlEnum_defaultEncoding_type execute_ENV_CTRL;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_36_;
  wire  _zz_37_;
  wire  _zz_38_;
  wire `EnvCtrlEnum_defaultEncoding_type writeBack_ENV_CTRL;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_39_;
  wire  execute_IS_RS1_SIGNED;
  wire [31:0] execute_RS1;
  wire  execute_IS_DIV;
  wire  execute_IS_RS2_SIGNED;
  wire  memory_IS_DIV;
  wire  writeBack_IS_MUL;
  wire [33:0] writeBack_MUL_HH;
  wire [51:0] writeBack_MUL_LOW;
  wire [33:0] memory_MUL_HL;
  wire [33:0] memory_MUL_LH;
  wire [31:0] memory_MUL_LL;
  wire [51:0] _zz_40_;
  wire [33:0] _zz_41_;
  wire [33:0] _zz_42_;
  wire [33:0] _zz_43_;
  wire [31:0] _zz_44_;
  wire  decode_RS2_USE;
  wire  decode_RS1_USE;
  reg [31:0] _zz_45_;
  wire  execute_REGFILE_WRITE_VALID;
  wire  execute_BYPASSABLE_EXECUTE_STAGE;
  wire  memory_REGFILE_WRITE_VALID;
  wire [31:0] memory_INSTRUCTION;
  wire  memory_BYPASSABLE_MEMORY_STAGE;
  wire  writeBack_REGFILE_WRITE_VALID;
  reg [31:0] decode_RS2;
  reg [31:0] decode_RS1;
  wire [31:0] memory_SHIFT_RIGHT;
  reg [31:0] _zz_46_;
  wire `ShiftCtrlEnum_defaultEncoding_type memory_SHIFT_CTRL;
  wire `ShiftCtrlEnum_defaultEncoding_type _zz_47_;
  wire [31:0] _zz_48_;
  wire `ShiftCtrlEnum_defaultEncoding_type execute_SHIFT_CTRL;
  wire `ShiftCtrlEnum_defaultEncoding_type _zz_49_;
  wire  _zz_50_;
  wire [31:0] _zz_51_;
  wire [31:0] _zz_52_;
  wire  execute_SRC_LESS_UNSIGNED;
  wire  execute_SRC2_FORCE_ZERO;
  wire  execute_SRC_USE_SUB_LESS;
  wire [31:0] _zz_53_;
  wire `Src2CtrlEnum_defaultEncoding_type execute_SRC2_CTRL;
  wire `Src2CtrlEnum_defaultEncoding_type _zz_54_;
  wire [31:0] _zz_55_;
  wire `Src1CtrlEnum_defaultEncoding_type execute_SRC1_CTRL;
  wire `Src1CtrlEnum_defaultEncoding_type _zz_56_;
  wire [31:0] _zz_57_;
  wire  decode_SRC_USE_SUB_LESS;
  wire  decode_SRC_ADD_ZERO;
  wire  _zz_58_;
  wire [31:0] execute_SRC_ADD_SUB;
  wire  execute_SRC_LESS;
  wire `AluCtrlEnum_defaultEncoding_type execute_ALU_CTRL;
  wire `AluCtrlEnum_defaultEncoding_type _zz_59_;
  wire [31:0] _zz_60_;
  wire [31:0] execute_SRC2;
  wire [31:0] execute_SRC1;
  wire `AluBitwiseCtrlEnum_defaultEncoding_type execute_ALU_BITWISE_CTRL;
  wire `AluBitwiseCtrlEnum_defaultEncoding_type _zz_61_;
  wire [31:0] _zz_62_;
  wire  _zz_63_;
  reg  _zz_64_;
  wire [31:0] _zz_65_;
  wire [31:0] _zz_66_;
  wire [31:0] decode_INSTRUCTION_ANTICIPATED;
  reg  decode_REGFILE_WRITE_VALID;
  wire  decode_LEGAL_INSTRUCTION;
  wire  decode_INSTRUCTION_READY;
  wire  _zz_67_;
  wire `Src1CtrlEnum_defaultEncoding_type _zz_68_;
  wire  _zz_69_;
  wire  _zz_70_;
  wire  _zz_71_;
  wire  _zz_72_;
  wire  _zz_73_;
  wire  _zz_74_;
  wire `BranchCtrlEnum_defaultEncoding_type _zz_75_;
  wire  _zz_76_;
  wire  _zz_77_;
  wire `ShiftCtrlEnum_defaultEncoding_type _zz_78_;
  wire  _zz_79_;
  wire  _zz_80_;
  wire  _zz_81_;
  wire  _zz_82_;
  wire  _zz_83_;
  wire `AluCtrlEnum_defaultEncoding_type _zz_84_;
  wire  _zz_85_;
  wire  _zz_86_;
  wire `AluBitwiseCtrlEnum_defaultEncoding_type _zz_87_;
  wire  _zz_88_;
  wire  _zz_89_;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_90_;
  wire `Src2CtrlEnum_defaultEncoding_type _zz_91_;
  wire  _zz_92_;
  wire  _zz_93_;
  wire  writeBack_IS_SFENCE_VMA;
  wire  writeBack_IS_DBUS_SHARING;
  wire  memory_IS_DBUS_SHARING;
  wire  _zz_94_;
  reg [31:0] _zz_95_;
  wire [1:0] writeBack_MEMORY_ADDRESS_LOW;
  wire  writeBack_MEMORY_WR;
  wire [31:0] writeBack_REGFILE_WRITE_DATA;
  wire  writeBack_MEMORY_ENABLE;
  wire [31:0] memory_REGFILE_WRITE_DATA;
  wire  memory_MEMORY_ENABLE;
  wire [1:0] _zz_96_;
  wire  execute_MEMORY_MANAGMENT;
  wire [31:0] execute_RS2;
  wire  execute_MEMORY_WR;
  wire [31:0] execute_SRC_ADD;
  wire  execute_MEMORY_ENABLE;
  wire [31:0] execute_INSTRUCTION;
  wire  decode_MEMORY_ENABLE;
  wire  decode_FLUSH_ALL;
  reg  IBusCachedPlugin_rsp_issueDetected;
  reg  _zz_97_;
  reg  _zz_98_;
  reg  _zz_99_;
  wire [31:0] _zz_100_;
  wire `BranchCtrlEnum_defaultEncoding_type decode_BRANCH_CTRL;
  wire `BranchCtrlEnum_defaultEncoding_type _zz_101_;
  reg [31:0] decode_INSTRUCTION;
  wire `BranchCtrlEnum_defaultEncoding_type memory_BRANCH_CTRL;
  wire `BranchCtrlEnum_defaultEncoding_type _zz_102_;
  wire [31:0] memory_PC;
  wire  memory_PREDICTION_CONTEXT_hazard;
  wire [1:0] memory_PREDICTION_CONTEXT_line_history;
  wire  decode_PREDICTION_CONTEXT_hazard;
  wire [1:0] decode_PREDICTION_CONTEXT_line_history;
  wire  _zz_103_;
  wire [1:0] _zz_104_;
  reg  _zz_105_;
  reg [31:0] _zz_106_;
  reg [31:0] _zz_107_;
  wire [31:0] decode_PC;
  wire [31:0] _zz_108_;
  wire [31:0] _zz_109_;
  wire [31:0] _zz_110_;
  wire [31:0] writeBack_PC;
  wire [31:0] writeBack_INSTRUCTION;
  reg  decode_arbitration_haltItself;
  reg  decode_arbitration_haltByOther;
  reg  decode_arbitration_removeIt;
  wire  decode_arbitration_flushAll;
  reg  decode_arbitration_isValid;
  wire  decode_arbitration_isStuck;
  wire  decode_arbitration_isStuckByOthers;
  wire  decode_arbitration_isFlushed;
  wire  decode_arbitration_isMoving;
  wire  decode_arbitration_isFiring;
  reg  execute_arbitration_haltItself;
  reg  execute_arbitration_haltByOther;
  reg  execute_arbitration_removeIt;
  reg  execute_arbitration_flushAll;
  reg  execute_arbitration_isValid;
  wire  execute_arbitration_isStuck;
  wire  execute_arbitration_isStuckByOthers;
  wire  execute_arbitration_isFlushed;
  wire  execute_arbitration_isMoving;
  wire  execute_arbitration_isFiring;
  reg  memory_arbitration_haltItself;
  wire  memory_arbitration_haltByOther;
  reg  memory_arbitration_removeIt;
  reg  memory_arbitration_flushAll;
  reg  memory_arbitration_isValid;
  wire  memory_arbitration_isStuck;
  wire  memory_arbitration_isStuckByOthers;
  wire  memory_arbitration_isFlushed;
  wire  memory_arbitration_isMoving;
  wire  memory_arbitration_isFiring;
  reg  writeBack_arbitration_haltItself;
  wire  writeBack_arbitration_haltByOther;
  reg  writeBack_arbitration_removeIt;
  reg  writeBack_arbitration_flushAll;
  reg  writeBack_arbitration_isValid;
  wire  writeBack_arbitration_isStuck;
  wire  writeBack_arbitration_isStuckByOthers;
  wire  writeBack_arbitration_isFlushed;
  wire  writeBack_arbitration_isMoving;
  wire  writeBack_arbitration_isFiring;
  wire [31:0] lastStageInstruction /* verilator public */ ;
  wire [31:0] lastStagePc /* verilator public */ ;
  wire  lastStageIsValid /* verilator public */ ;
  wire  lastStageIsFiring /* verilator public */ ;
  reg  IBusCachedPlugin_fetcherHalt;
  reg  IBusCachedPlugin_fetcherflushIt;
  reg  IBusCachedPlugin_incomingInstruction;
  wire  IBusCachedPlugin_predictionJumpInterface_valid;
  (* keep , syn_keep *) wire [31:0] IBusCachedPlugin_pcs_4 /* synthesis syn_keep = 1 */ ;
  reg  IBusCachedPlugin_decodePrediction_cmd_hadBranch;
  wire  IBusCachedPlugin_decodePrediction_rsp_wasWrong;
  wire  IBusCachedPlugin_pcValids_0;
  wire  IBusCachedPlugin_pcValids_1;
  wire  IBusCachedPlugin_pcValids_2;
  wire  IBusCachedPlugin_pcValids_3;
  wire  IBusCachedPlugin_redoBranch_valid;
  wire [31:0] IBusCachedPlugin_redoBranch_payload;
  reg  IBusCachedPlugin_decodeExceptionPort_valid;
  reg [3:0] IBusCachedPlugin_decodeExceptionPort_payload_code;
  wire [31:0] IBusCachedPlugin_decodeExceptionPort_payload_badAddr;
  wire  IBusCachedPlugin_mmuBus_cmd_isValid;
  wire [31:0] IBusCachedPlugin_mmuBus_cmd_virtualAddress;
  wire  IBusCachedPlugin_mmuBus_cmd_bypassTranslation;
  reg [31:0] IBusCachedPlugin_mmuBus_rsp_physicalAddress;
  wire  IBusCachedPlugin_mmuBus_rsp_isIoAccess;
  reg  IBusCachedPlugin_mmuBus_rsp_allowRead;
  reg  IBusCachedPlugin_mmuBus_rsp_allowWrite;
  reg  IBusCachedPlugin_mmuBus_rsp_allowExecute;
  reg  IBusCachedPlugin_mmuBus_rsp_exception;
  reg  IBusCachedPlugin_mmuBus_rsp_refilling;
  wire  IBusCachedPlugin_mmuBus_end;
  wire  IBusCachedPlugin_mmuBus_busy;
  wire  DBusCachedPlugin_mmuBus_cmd_isValid;
  wire [31:0] DBusCachedPlugin_mmuBus_cmd_virtualAddress;
  reg  DBusCachedPlugin_mmuBus_cmd_bypassTranslation;
  reg [31:0] DBusCachedPlugin_mmuBus_rsp_physicalAddress;
  wire  DBusCachedPlugin_mmuBus_rsp_isIoAccess;
  reg  DBusCachedPlugin_mmuBus_rsp_allowRead;
  reg  DBusCachedPlugin_mmuBus_rsp_allowWrite;
  reg  DBusCachedPlugin_mmuBus_rsp_allowExecute;
  reg  DBusCachedPlugin_mmuBus_rsp_exception;
  reg  DBusCachedPlugin_mmuBus_rsp_refilling;
  wire  DBusCachedPlugin_mmuBus_end;
  wire  DBusCachedPlugin_mmuBus_busy;
  reg  DBusCachedPlugin_redoBranch_valid;
  wire [31:0] DBusCachedPlugin_redoBranch_payload;
  reg  DBusCachedPlugin_exceptionBus_valid;
  reg [3:0] DBusCachedPlugin_exceptionBus_payload_code;
  wire [31:0] DBusCachedPlugin_exceptionBus_payload_badAddr;
  reg  _zz_111_;
  reg  MmuPlugin_dBusAccess_cmd_valid;
  reg  MmuPlugin_dBusAccess_cmd_ready;
  reg [31:0] MmuPlugin_dBusAccess_cmd_payload_address;
  wire [1:0] MmuPlugin_dBusAccess_cmd_payload_size;
  wire  MmuPlugin_dBusAccess_cmd_payload_write;
  wire [31:0] MmuPlugin_dBusAccess_cmd_payload_data;
  wire [3:0] MmuPlugin_dBusAccess_cmd_payload_writeMask;
  wire  MmuPlugin_dBusAccess_rsp_valid;
  wire [31:0] MmuPlugin_dBusAccess_rsp_payload_data;
  wire  MmuPlugin_dBusAccess_rsp_payload_error;
  wire  MmuPlugin_dBusAccess_rsp_payload_redo;
  wire  decodeExceptionPort_valid;
  wire [3:0] decodeExceptionPort_payload_code;
  wire [31:0] decodeExceptionPort_payload_badAddr;
  reg  CsrPlugin_jumpInterface_valid;
  reg [31:0] CsrPlugin_jumpInterface_payload;
  wire  CsrPlugin_exceptionPendings_0;
  wire  CsrPlugin_exceptionPendings_1;
  wire  CsrPlugin_exceptionPendings_2;
  wire  CsrPlugin_exceptionPendings_3;
  wire  contextSwitching;
  reg [1:0] CsrPlugin_privilege;
  reg  CsrPlugin_forceMachineWire;
  reg  CsrPlugin_allowInterrupts;
  reg  CsrPlugin_allowException;
  reg  IBusCachedPlugin_injectionPort_valid;
  reg  IBusCachedPlugin_injectionPort_ready;
  wire [31:0] IBusCachedPlugin_injectionPort_payload;
  wire  BranchPlugin_jumpInterface_valid;
  wire [31:0] BranchPlugin_jumpInterface_payload;
  wire  BranchPlugin_branchExceptionPort_valid;
  wire [3:0] BranchPlugin_branchExceptionPort_payload_code;
  wire [31:0] BranchPlugin_branchExceptionPort_payload_badAddr;
  wire  IBusCachedPlugin_jump_pcLoad_valid;
  wire [31:0] IBusCachedPlugin_jump_pcLoad_payload;
  wire [4:0] _zz_112_;
  wire [4:0] _zz_113_;
  wire  _zz_114_;
  wire  _zz_115_;
  wire  _zz_116_;
  wire  _zz_117_;
  wire  IBusCachedPlugin_fetchPc_preOutput_valid;
  wire  IBusCachedPlugin_fetchPc_preOutput_ready;
  wire [31:0] IBusCachedPlugin_fetchPc_preOutput_payload;
  wire  _zz_118_;
  wire  IBusCachedPlugin_fetchPc_output_valid;
  wire  IBusCachedPlugin_fetchPc_output_ready;
  wire [31:0] IBusCachedPlugin_fetchPc_output_payload;
  reg [31:0] IBusCachedPlugin_fetchPc_pcReg /* verilator public */ ;
  reg  IBusCachedPlugin_fetchPc_inc;
  reg  IBusCachedPlugin_fetchPc_propagatePc;
  reg [31:0] IBusCachedPlugin_fetchPc_pc;
  reg  IBusCachedPlugin_fetchPc_samplePcNext;
  reg  _zz_119_;
  wire  IBusCachedPlugin_iBusRsp_stages_0_input_valid;
  wire  IBusCachedPlugin_iBusRsp_stages_0_input_ready;
  wire [31:0] IBusCachedPlugin_iBusRsp_stages_0_input_payload;
  wire  IBusCachedPlugin_iBusRsp_stages_0_output_valid;
  wire  IBusCachedPlugin_iBusRsp_stages_0_output_ready;
  wire [31:0] IBusCachedPlugin_iBusRsp_stages_0_output_payload;
  reg  IBusCachedPlugin_iBusRsp_stages_0_halt;
  wire  IBusCachedPlugin_iBusRsp_stages_0_inputSample;
  wire  IBusCachedPlugin_iBusRsp_stages_1_input_valid;
  wire  IBusCachedPlugin_iBusRsp_stages_1_input_ready;
  wire [31:0] IBusCachedPlugin_iBusRsp_stages_1_input_payload;
  wire  IBusCachedPlugin_iBusRsp_stages_1_output_valid;
  wire  IBusCachedPlugin_iBusRsp_stages_1_output_ready;
  wire [31:0] IBusCachedPlugin_iBusRsp_stages_1_output_payload;
  reg  IBusCachedPlugin_iBusRsp_stages_1_halt;
  wire  IBusCachedPlugin_iBusRsp_stages_1_inputSample;
  wire  IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_valid;
  wire  IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_ready;
  wire [31:0] IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_payload;
  wire  IBusCachedPlugin_iBusRsp_cacheRspArbitration_output_valid;
  wire  IBusCachedPlugin_iBusRsp_cacheRspArbitration_output_ready;
  wire [31:0] IBusCachedPlugin_iBusRsp_cacheRspArbitration_output_payload;
  reg  IBusCachedPlugin_iBusRsp_cacheRspArbitration_halt;
  wire  IBusCachedPlugin_iBusRsp_cacheRspArbitration_inputSample;
  wire  _zz_120_;
  wire  _zz_121_;
  wire  _zz_122_;
  wire  _zz_123_;
  wire  _zz_124_;
  reg  _zz_125_;
  wire  _zz_126_;
  reg  _zz_127_;
  reg [31:0] _zz_128_;
  reg  IBusCachedPlugin_iBusRsp_readyForError;
  wire  IBusCachedPlugin_iBusRsp_decodeInput_valid;
  wire  IBusCachedPlugin_iBusRsp_decodeInput_ready;
  wire [31:0] IBusCachedPlugin_iBusRsp_decodeInput_payload_pc;
  wire  IBusCachedPlugin_iBusRsp_decodeInput_payload_rsp_error;
  wire [31:0] IBusCachedPlugin_iBusRsp_decodeInput_payload_rsp_inst;
  wire  IBusCachedPlugin_iBusRsp_decodeInput_payload_isRvc;
  reg  IBusCachedPlugin_injector_nextPcCalc_valids_0;
  reg  IBusCachedPlugin_injector_nextPcCalc_valids_1;
  reg  IBusCachedPlugin_injector_nextPcCalc_valids_2;
  reg  IBusCachedPlugin_injector_nextPcCalc_valids_3;
  reg  IBusCachedPlugin_injector_nextPcCalc_valids_4;
  reg  IBusCachedPlugin_injector_decodeRemoved;
  wire  _zz_130_;
  wire [9:0] _zz_131_;
  reg  _zz_132_;
  reg [9:0] _zz_133_;
  wire [29:0] _zz_134_;
  wire  _zz_135_;
  reg  _zz_136_;
  reg [1:0] _zz_137_;
  wire  _zz_138_;
  wire  _zz_139_;
  reg [10:0] _zz_140_;
  wire  _zz_141_;
  reg [18:0] _zz_142_;
  reg  _zz_143_;
  wire  _zz_144_;
  reg [10:0] _zz_145_;
  wire  _zz_146_;
  reg [18:0] _zz_147_;
  wire  IBusCachedPlugin_s0_tightlyCoupledHit;
  reg  IBusCachedPlugin_s1_tightlyCoupledHit;
  reg  IBusCachedPlugin_s2_tightlyCoupledHit;
  wire  IBusCachedPlugin_rsp_iBusRspOutputHalt;
  reg  IBusCachedPlugin_rsp_redoFetch;
  wire [1:0] execute_DBusCachedPlugin_size;
  reg [31:0] _zz_148_;
  reg [31:0] writeBack_DBusCachedPlugin_rspShifted;
  wire  _zz_149_;
  reg [31:0] _zz_150_;
  wire  _zz_151_;
  reg [31:0] _zz_152_;
  reg [31:0] writeBack_DBusCachedPlugin_rspFormated;
  reg  DBusCachedPlugin_forceDatapath;
  reg  MmuPlugin_status_sum;
  reg  MmuPlugin_status_mxr;
  reg  MmuPlugin_status_mprv;
  reg  MmuPlugin_satp_mode;
  reg [19:0] MmuPlugin_satp_ppn;
  reg  MmuPlugin_ports_0_cache_0_valid;
  reg  MmuPlugin_ports_0_cache_0_exception;
  reg  MmuPlugin_ports_0_cache_0_superPage;
  reg [9:0] MmuPlugin_ports_0_cache_0_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_0_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_0_cache_0_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_0_physicalAddress_1;
  reg  MmuPlugin_ports_0_cache_0_allowRead;
  reg  MmuPlugin_ports_0_cache_0_allowWrite;
  reg  MmuPlugin_ports_0_cache_0_allowExecute;
  reg  MmuPlugin_ports_0_cache_0_allowUser;
  reg  MmuPlugin_ports_0_cache_1_valid;
  reg  MmuPlugin_ports_0_cache_1_exception;
  reg  MmuPlugin_ports_0_cache_1_superPage;
  reg [9:0] MmuPlugin_ports_0_cache_1_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_1_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_0_cache_1_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_1_physicalAddress_1;
  reg  MmuPlugin_ports_0_cache_1_allowRead;
  reg  MmuPlugin_ports_0_cache_1_allowWrite;
  reg  MmuPlugin_ports_0_cache_1_allowExecute;
  reg  MmuPlugin_ports_0_cache_1_allowUser;
  reg  MmuPlugin_ports_0_cache_2_valid;
  reg  MmuPlugin_ports_0_cache_2_exception;
  reg  MmuPlugin_ports_0_cache_2_superPage;
  reg [9:0] MmuPlugin_ports_0_cache_2_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_2_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_0_cache_2_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_2_physicalAddress_1;
  reg  MmuPlugin_ports_0_cache_2_allowRead;
  reg  MmuPlugin_ports_0_cache_2_allowWrite;
  reg  MmuPlugin_ports_0_cache_2_allowExecute;
  reg  MmuPlugin_ports_0_cache_2_allowUser;
  reg  MmuPlugin_ports_0_cache_3_valid;
  reg  MmuPlugin_ports_0_cache_3_exception;
  reg  MmuPlugin_ports_0_cache_3_superPage;
  reg [9:0] MmuPlugin_ports_0_cache_3_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_3_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_0_cache_3_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_3_physicalAddress_1;
  reg  MmuPlugin_ports_0_cache_3_allowRead;
  reg  MmuPlugin_ports_0_cache_3_allowWrite;
  reg  MmuPlugin_ports_0_cache_3_allowExecute;
  reg  MmuPlugin_ports_0_cache_3_allowUser;
  reg  MmuPlugin_ports_0_cache_4_valid;
  reg  MmuPlugin_ports_0_cache_4_exception;
  reg  MmuPlugin_ports_0_cache_4_superPage;
  reg [9:0] MmuPlugin_ports_0_cache_4_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_4_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_0_cache_4_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_4_physicalAddress_1;
  reg  MmuPlugin_ports_0_cache_4_allowRead;
  reg  MmuPlugin_ports_0_cache_4_allowWrite;
  reg  MmuPlugin_ports_0_cache_4_allowExecute;
  reg  MmuPlugin_ports_0_cache_4_allowUser;
  reg  MmuPlugin_ports_0_cache_5_valid;
  reg  MmuPlugin_ports_0_cache_5_exception;
  reg  MmuPlugin_ports_0_cache_5_superPage;
  reg [9:0] MmuPlugin_ports_0_cache_5_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_5_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_0_cache_5_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_0_cache_5_physicalAddress_1;
  reg  MmuPlugin_ports_0_cache_5_allowRead;
  reg  MmuPlugin_ports_0_cache_5_allowWrite;
  reg  MmuPlugin_ports_0_cache_5_allowExecute;
  reg  MmuPlugin_ports_0_cache_5_allowUser;
  wire  MmuPlugin_ports_0_cacheHits_0;
  wire  MmuPlugin_ports_0_cacheHits_1;
  wire  MmuPlugin_ports_0_cacheHits_2;
  wire  MmuPlugin_ports_0_cacheHits_3;
  wire  MmuPlugin_ports_0_cacheHits_4;
  wire  MmuPlugin_ports_0_cacheHits_5;
  wire  MmuPlugin_ports_0_cacheHit;
  wire  _zz_153_;
  wire  _zz_154_;
  wire  _zz_155_;
  wire [2:0] _zz_156_;
  wire  MmuPlugin_ports_0_cacheLine_valid;
  wire  MmuPlugin_ports_0_cacheLine_exception;
  wire  MmuPlugin_ports_0_cacheLine_superPage;
  wire [9:0] MmuPlugin_ports_0_cacheLine_virtualAddress_0;
  wire [9:0] MmuPlugin_ports_0_cacheLine_virtualAddress_1;
  wire [9:0] MmuPlugin_ports_0_cacheLine_physicalAddress_0;
  wire [9:0] MmuPlugin_ports_0_cacheLine_physicalAddress_1;
  wire  MmuPlugin_ports_0_cacheLine_allowRead;
  wire  MmuPlugin_ports_0_cacheLine_allowWrite;
  wire  MmuPlugin_ports_0_cacheLine_allowExecute;
  wire  MmuPlugin_ports_0_cacheLine_allowUser;
  reg  MmuPlugin_ports_0_entryToReplace_willIncrement;
  wire  MmuPlugin_ports_0_entryToReplace_willClear;
  reg [2:0] MmuPlugin_ports_0_entryToReplace_valueNext;
  reg [2:0] MmuPlugin_ports_0_entryToReplace_value;
  wire  MmuPlugin_ports_0_entryToReplace_willOverflowIfInc;
  wire  MmuPlugin_ports_0_entryToReplace_willOverflow;
  reg  MmuPlugin_ports_0_requireMmuLockup;
  reg  MmuPlugin_ports_1_cache_0_valid;
  reg  MmuPlugin_ports_1_cache_0_exception;
  reg  MmuPlugin_ports_1_cache_0_superPage;
  reg [9:0] MmuPlugin_ports_1_cache_0_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_1_cache_0_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_1_cache_0_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_1_cache_0_physicalAddress_1;
  reg  MmuPlugin_ports_1_cache_0_allowRead;
  reg  MmuPlugin_ports_1_cache_0_allowWrite;
  reg  MmuPlugin_ports_1_cache_0_allowExecute;
  reg  MmuPlugin_ports_1_cache_0_allowUser;
  reg  MmuPlugin_ports_1_cache_1_valid;
  reg  MmuPlugin_ports_1_cache_1_exception;
  reg  MmuPlugin_ports_1_cache_1_superPage;
  reg [9:0] MmuPlugin_ports_1_cache_1_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_1_cache_1_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_1_cache_1_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_1_cache_1_physicalAddress_1;
  reg  MmuPlugin_ports_1_cache_1_allowRead;
  reg  MmuPlugin_ports_1_cache_1_allowWrite;
  reg  MmuPlugin_ports_1_cache_1_allowExecute;
  reg  MmuPlugin_ports_1_cache_1_allowUser;
  reg  MmuPlugin_ports_1_cache_2_valid;
  reg  MmuPlugin_ports_1_cache_2_exception;
  reg  MmuPlugin_ports_1_cache_2_superPage;
  reg [9:0] MmuPlugin_ports_1_cache_2_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_1_cache_2_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_1_cache_2_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_1_cache_2_physicalAddress_1;
  reg  MmuPlugin_ports_1_cache_2_allowRead;
  reg  MmuPlugin_ports_1_cache_2_allowWrite;
  reg  MmuPlugin_ports_1_cache_2_allowExecute;
  reg  MmuPlugin_ports_1_cache_2_allowUser;
  reg  MmuPlugin_ports_1_cache_3_valid;
  reg  MmuPlugin_ports_1_cache_3_exception;
  reg  MmuPlugin_ports_1_cache_3_superPage;
  reg [9:0] MmuPlugin_ports_1_cache_3_virtualAddress_0;
  reg [9:0] MmuPlugin_ports_1_cache_3_virtualAddress_1;
  reg [9:0] MmuPlugin_ports_1_cache_3_physicalAddress_0;
  reg [9:0] MmuPlugin_ports_1_cache_3_physicalAddress_1;
  reg  MmuPlugin_ports_1_cache_3_allowRead;
  reg  MmuPlugin_ports_1_cache_3_allowWrite;
  reg  MmuPlugin_ports_1_cache_3_allowExecute;
  reg  MmuPlugin_ports_1_cache_3_allowUser;
  wire  MmuPlugin_ports_1_cacheHits_0;
  wire  MmuPlugin_ports_1_cacheHits_1;
  wire  MmuPlugin_ports_1_cacheHits_2;
  wire  MmuPlugin_ports_1_cacheHits_3;
  wire  MmuPlugin_ports_1_cacheHit;
  wire  _zz_157_;
  wire  _zz_158_;
  wire [1:0] _zz_159_;
  wire  MmuPlugin_ports_1_cacheLine_valid;
  wire  MmuPlugin_ports_1_cacheLine_exception;
  wire  MmuPlugin_ports_1_cacheLine_superPage;
  wire [9:0] MmuPlugin_ports_1_cacheLine_virtualAddress_0;
  wire [9:0] MmuPlugin_ports_1_cacheLine_virtualAddress_1;
  wire [9:0] MmuPlugin_ports_1_cacheLine_physicalAddress_0;
  wire [9:0] MmuPlugin_ports_1_cacheLine_physicalAddress_1;
  wire  MmuPlugin_ports_1_cacheLine_allowRead;
  wire  MmuPlugin_ports_1_cacheLine_allowWrite;
  wire  MmuPlugin_ports_1_cacheLine_allowExecute;
  wire  MmuPlugin_ports_1_cacheLine_allowUser;
  reg  MmuPlugin_ports_1_entryToReplace_willIncrement;
  wire  MmuPlugin_ports_1_entryToReplace_willClear;
  reg [1:0] MmuPlugin_ports_1_entryToReplace_valueNext;
  reg [1:0] MmuPlugin_ports_1_entryToReplace_value;
  wire  MmuPlugin_ports_1_entryToReplace_willOverflowIfInc;
  wire  MmuPlugin_ports_1_entryToReplace_willOverflow;
  reg  MmuPlugin_ports_1_requireMmuLockup;
  reg `MmuPlugin_shared_State_defaultEncoding_type MmuPlugin_shared_state_1_;
  reg [9:0] MmuPlugin_shared_vpn_0;
  reg [9:0] MmuPlugin_shared_vpn_1;
  reg [0:0] MmuPlugin_shared_portId;
  wire  MmuPlugin_shared_dBusRsp_pte_V;
  wire  MmuPlugin_shared_dBusRsp_pte_R;
  wire  MmuPlugin_shared_dBusRsp_pte_W;
  wire  MmuPlugin_shared_dBusRsp_pte_X;
  wire  MmuPlugin_shared_dBusRsp_pte_U;
  wire  MmuPlugin_shared_dBusRsp_pte_G;
  wire  MmuPlugin_shared_dBusRsp_pte_A;
  wire  MmuPlugin_shared_dBusRsp_pte_D;
  wire [1:0] MmuPlugin_shared_dBusRsp_pte_RSW;
  wire [9:0] MmuPlugin_shared_dBusRsp_pte_PPN0;
  wire [11:0] MmuPlugin_shared_dBusRsp_pte_PPN1;
  wire  MmuPlugin_shared_dBusRsp_exception;
  wire  MmuPlugin_shared_dBusRsp_leaf;
  reg  MmuPlugin_shared_pteBuffer_V;
  reg  MmuPlugin_shared_pteBuffer_R;
  reg  MmuPlugin_shared_pteBuffer_W;
  reg  MmuPlugin_shared_pteBuffer_X;
  reg  MmuPlugin_shared_pteBuffer_U;
  reg  MmuPlugin_shared_pteBuffer_G;
  reg  MmuPlugin_shared_pteBuffer_A;
  reg  MmuPlugin_shared_pteBuffer_D;
  reg [1:0] MmuPlugin_shared_pteBuffer_RSW;
  reg [9:0] MmuPlugin_shared_pteBuffer_PPN0;
  reg [11:0] MmuPlugin_shared_pteBuffer_PPN1;
  wire [32:0] _zz_160_;
  wire  _zz_161_;
  wire  _zz_162_;
  wire  _zz_163_;
  wire  _zz_164_;
  wire `Src2CtrlEnum_defaultEncoding_type _zz_165_;
  wire `EnvCtrlEnum_defaultEncoding_type _zz_166_;
  wire `AluBitwiseCtrlEnum_defaultEncoding_type _zz_167_;
  wire `AluCtrlEnum_defaultEncoding_type _zz_168_;
  wire `ShiftCtrlEnum_defaultEncoding_type _zz_169_;
  wire `BranchCtrlEnum_defaultEncoding_type _zz_170_;
  wire `Src1CtrlEnum_defaultEncoding_type _zz_171_;
  wire [4:0] decode_RegFilePlugin_regFileReadAddress1;
  wire [4:0] decode_RegFilePlugin_regFileReadAddress2;
  wire [31:0] decode_RegFilePlugin_rs1Data;
  wire [31:0] decode_RegFilePlugin_rs2Data;
  reg  lastStageRegFileWrite_valid /* verilator public */ ;
  wire [4:0] lastStageRegFileWrite_payload_address /* verilator public */ ;
  wire [31:0] lastStageRegFileWrite_payload_data /* verilator public */ ;
  reg  _zz_172_;
  reg [31:0] execute_IntAluPlugin_bitwise;
  reg [31:0] _zz_173_;
  reg [31:0] _zz_174_;
  wire  _zz_175_;
  reg [19:0] _zz_176_;
  wire  _zz_177_;
  reg [19:0] _zz_178_;
  reg [31:0] _zz_179_;
  reg [31:0] execute_SrcPlugin_addSub;
  wire  execute_SrcPlugin_less;
  wire [4:0] execute_FullBarrelShifterPlugin_amplitude;
  reg [31:0] _zz_180_;
  wire [31:0] execute_FullBarrelShifterPlugin_reversed;
  reg [31:0] _zz_181_;
  reg  _zz_182_;
  reg  _zz_183_;
  wire  _zz_184_;
  reg  _zz_185_;
  reg [4:0] _zz_186_;
  reg [31:0] _zz_187_;
  wire  _zz_188_;
  wire  _zz_189_;
  wire  _zz_190_;
  wire  _zz_191_;
  wire  _zz_192_;
  wire  _zz_193_;
  reg  execute_MulPlugin_aSigned;
  reg  execute_MulPlugin_bSigned;
  wire [31:0] execute_MulPlugin_a;
  wire [31:0] execute_MulPlugin_b;
  wire [15:0] execute_MulPlugin_aULow;
  wire [15:0] execute_MulPlugin_bULow;
  wire [16:0] execute_MulPlugin_aSLow;
  wire [16:0] execute_MulPlugin_bSLow;
  wire [16:0] execute_MulPlugin_aHigh;
  wire [16:0] execute_MulPlugin_bHigh;
  wire [65:0] writeBack_MulPlugin_result;
  reg [32:0] memory_DivPlugin_rs1;
  reg [31:0] memory_DivPlugin_rs2;
  reg [64:0] memory_DivPlugin_accumulator;
  reg  memory_DivPlugin_div_needRevert;
  reg  memory_DivPlugin_div_counter_willIncrement;
  reg  memory_DivPlugin_div_counter_willClear;
  reg [5:0] memory_DivPlugin_div_counter_valueNext;
  reg [5:0] memory_DivPlugin_div_counter_value;
  wire  memory_DivPlugin_div_counter_willOverflowIfInc;
  wire  memory_DivPlugin_div_counter_willOverflow;
  reg  memory_DivPlugin_div_done;
  reg [31:0] memory_DivPlugin_div_result;
  wire [31:0] _zz_194_;
  wire [32:0] _zz_195_;
  wire [32:0] _zz_196_;
  wire [31:0] _zz_197_;
  wire  _zz_198_;
  wire  _zz_199_;
  reg [32:0] _zz_200_;
  wire [1:0] CsrPlugin_misa_base;
  wire [25:0] CsrPlugin_misa_extensions;
  wire [1:0] CsrPlugin_mtvec_mode;
  wire [29:0] CsrPlugin_mtvec_base;
  reg [31:0] CsrPlugin_mepc;
  reg  CsrPlugin_mstatus_MIE;
  reg  CsrPlugin_mstatus_MPIE;
  reg [1:0] CsrPlugin_mstatus_MPP;
  reg  CsrPlugin_mip_MEIP;
  reg  CsrPlugin_mip_MTIP;
  reg  CsrPlugin_mip_MSIP;
  reg  CsrPlugin_mie_MEIE;
  reg  CsrPlugin_mie_MTIE;
  reg  CsrPlugin_mie_MSIE;
  reg  CsrPlugin_mcause_interrupt;
  reg [3:0] CsrPlugin_mcause_exceptionCode;
  reg [31:0] CsrPlugin_mtval;
  reg [63:0] CsrPlugin_mcycle = 64'b0000000000000000000000000000000000000000000000000000000000000000;
  reg [63:0] CsrPlugin_minstret = 64'b0000000000000000000000000000000000000000000000000000000000000000;
  reg  CsrPlugin_exceptionPortCtrl_exceptionValids_decode;
  reg  CsrPlugin_exceptionPortCtrl_exceptionValids_execute;
  reg  CsrPlugin_exceptionPortCtrl_exceptionValids_memory;
  reg  CsrPlugin_exceptionPortCtrl_exceptionValids_writeBack;
  reg  CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_decode;
  reg  CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_execute;
  reg  CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_memory;
  reg  CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_writeBack;
  reg [3:0] CsrPlugin_exceptionPortCtrl_exceptionContext_code;
  reg [31:0] CsrPlugin_exceptionPortCtrl_exceptionContext_badAddr;
  wire [1:0] CsrPlugin_exceptionPortCtrl_exceptionTargetPrivilegeUncapped;
  wire [1:0] CsrPlugin_exceptionPortCtrl_exceptionTargetPrivilege;
  wire [1:0] _zz_201_;
  wire  _zz_202_;
  reg  CsrPlugin_interrupt;
  reg [3:0] CsrPlugin_interruptCode /* verilator public */ ;
  reg [1:0] CsrPlugin_interruptTargetPrivilege;
  wire  CsrPlugin_exception;
  wire  CsrPlugin_lastStageWasWfi;
  reg  CsrPlugin_pipelineLiberator_done;
  wire  CsrPlugin_interruptJump /* verilator public */ ;
  reg  CsrPlugin_hadException;
  reg [1:0] CsrPlugin_targetPrivilege;
  reg [3:0] CsrPlugin_trapCause;
  reg [1:0] CsrPlugin_xtvec_mode;
  reg [29:0] CsrPlugin_xtvec_base;
  wire  execute_CsrPlugin_inWfi /* verilator public */ ;
  wire  execute_CsrPlugin_blockedBySideEffects;
  reg  execute_CsrPlugin_illegalAccess;
  reg  execute_CsrPlugin_illegalInstruction;
  reg [31:0] execute_CsrPlugin_readData;
  wire  execute_CsrPlugin_writeInstruction;
  wire  execute_CsrPlugin_readInstruction;
  wire  execute_CsrPlugin_writeEnable;
  wire  execute_CsrPlugin_readEnable;
  wire [31:0] execute_CsrPlugin_readToWriteData;
  reg [31:0] execute_CsrPlugin_writeData;
  wire [11:0] execute_CsrPlugin_csrAddress;
  reg  DebugPlugin_firstCycle;
  reg  DebugPlugin_secondCycle;
  reg  DebugPlugin_resetIt;
  reg  DebugPlugin_haltIt;
  reg  DebugPlugin_stepIt;
  reg  DebugPlugin_isPipBusy;
  reg  DebugPlugin_godmode;
  reg  DebugPlugin_haltedByBreak;
  reg [31:0] DebugPlugin_busReadDataReg;
  reg  _zz_203_;
  reg  DebugPlugin_resetIt_regNext;
  wire  execute_BranchPlugin_eq;
  wire [2:0] _zz_204_;
  reg  _zz_205_;
  reg  _zz_206_;
  wire  _zz_207_;
  reg [19:0] _zz_208_;
  wire  _zz_209_;
  reg [10:0] _zz_210_;
  wire  _zz_211_;
  reg [18:0] _zz_212_;
  reg  _zz_213_;
  wire  execute_BranchPlugin_missAlignedTarget;
  reg [31:0] execute_BranchPlugin_branch_src1;
  reg [31:0] execute_BranchPlugin_branch_src2;
  wire  _zz_214_;
  reg [19:0] _zz_215_;
  wire  _zz_216_;
  reg [10:0] _zz_217_;
  wire  _zz_218_;
  reg [18:0] _zz_219_;
  wire [31:0] execute_BranchPlugin_branchAdder;
  reg  decode_to_execute_IS_SFENCE_VMA;
  reg  execute_to_memory_IS_SFENCE_VMA;
  reg  memory_to_writeBack_IS_SFENCE_VMA;
  reg  decode_to_execute_MEMORY_MANAGMENT;
  reg [33:0] execute_to_memory_MUL_HL;
  reg [33:0] execute_to_memory_MUL_LH;
  reg [31:0] execute_to_memory_SHIFT_RIGHT;
  reg  decode_to_execute_IS_MUL;
  reg  execute_to_memory_IS_MUL;
  reg  memory_to_writeBack_IS_MUL;
  reg  decode_to_execute_BYPASSABLE_MEMORY_STAGE;
  reg  execute_to_memory_BYPASSABLE_MEMORY_STAGE;
  reg [31:0] decode_to_execute_INSTRUCTION;
  reg [31:0] execute_to_memory_INSTRUCTION;
  reg [31:0] memory_to_writeBack_INSTRUCTION;
  reg `BranchCtrlEnum_defaultEncoding_type decode_to_execute_BRANCH_CTRL;
  reg `BranchCtrlEnum_defaultEncoding_type execute_to_memory_BRANCH_CTRL;
  reg [51:0] memory_to_writeBack_MUL_LOW;
  reg  execute_to_memory_BRANCH_DO;
  reg `EnvCtrlEnum_defaultEncoding_type decode_to_execute_ENV_CTRL;
  reg `EnvCtrlEnum_defaultEncoding_type execute_to_memory_ENV_CTRL;
  reg `EnvCtrlEnum_defaultEncoding_type memory_to_writeBack_ENV_CTRL;
  reg  decode_to_execute_CSR_WRITE_OPCODE;
  reg  decode_to_execute_REGFILE_WRITE_VALID;
  reg  execute_to_memory_REGFILE_WRITE_VALID;
  reg  memory_to_writeBack_REGFILE_WRITE_VALID;
  reg  decode_to_execute_PREDICTION_CONTEXT_hazard;
  reg [1:0] decode_to_execute_PREDICTION_CONTEXT_line_history;
  reg  execute_to_memory_PREDICTION_CONTEXT_hazard;
  reg [1:0] execute_to_memory_PREDICTION_CONTEXT_line_history;
  reg  decode_to_execute_DO_EBREAK;
  reg [31:0] execute_to_memory_MUL_LL;
  reg [31:0] execute_to_memory_BRANCH_CALC;
  reg  decode_to_execute_PREDICTION_HAD_BRANCHED2;
  reg [1:0] execute_to_memory_MEMORY_ADDRESS_LOW;
  reg [1:0] memory_to_writeBack_MEMORY_ADDRESS_LOW;
  reg [31:0] execute_to_memory_REGFILE_WRITE_DATA;
  reg [31:0] memory_to_writeBack_REGFILE_WRITE_DATA;
  reg  execute_to_memory_IS_DBUS_SHARING;
  reg  memory_to_writeBack_IS_DBUS_SHARING;
  reg  decode_to_execute_SRC_USE_SUB_LESS;
  reg  decode_to_execute_MEMORY_ENABLE;
  reg  execute_to_memory_MEMORY_ENABLE;
  reg  memory_to_writeBack_MEMORY_ENABLE;
  reg `AluCtrlEnum_defaultEncoding_type decode_to_execute_ALU_CTRL;
  reg [31:0] decode_to_execute_RS2;
  reg  decode_to_execute_CSR_READ_OPCODE;
  reg [31:0] decode_to_execute_RS1;
  reg [31:0] decode_to_execute_FORMAL_PC_NEXT;
  reg [31:0] execute_to_memory_FORMAL_PC_NEXT;
  reg [31:0] memory_to_writeBack_FORMAL_PC_NEXT;
  reg  decode_to_execute_IS_DIV;
  reg  execute_to_memory_IS_DIV;
  reg `Src2CtrlEnum_defaultEncoding_type decode_to_execute_SRC2_CTRL;
  reg [31:0] decode_to_execute_PC;
  reg [31:0] execute_to_memory_PC;
  reg [31:0] memory_to_writeBack_PC;
  reg  decode_to_execute_IS_RS1_SIGNED;
  reg [33:0] execute_to_memory_MUL_HH;
  reg [33:0] memory_to_writeBack_MUL_HH;
  reg `Src1CtrlEnum_defaultEncoding_type decode_to_execute_SRC1_CTRL;
  reg  decode_to_execute_IS_RS2_SIGNED;
  reg `AluBitwiseCtrlEnum_defaultEncoding_type decode_to_execute_ALU_BITWISE_CTRL;
  reg  decode_to_execute_MEMORY_WR;
  reg  execute_to_memory_MEMORY_WR;
  reg  memory_to_writeBack_MEMORY_WR;
  reg  decode_to_execute_SRC2_FORCE_ZERO;
  reg  decode_to_execute_BYPASSABLE_EXECUTE_STAGE;
  reg  decode_to_execute_IS_CSR;
  reg  decode_to_execute_SRC_LESS_UNSIGNED;
  reg `ShiftCtrlEnum_defaultEncoding_type decode_to_execute_SHIFT_CTRL;
  reg `ShiftCtrlEnum_defaultEncoding_type execute_to_memory_SHIFT_CTRL;
  reg [2:0] _zz_220_;
  reg [31:0] IBusCachedPlugin_injectionPort_payload_regNext;
  `ifndef SYNTHESIS
  reg [71:0] _zz_1__string;
  reg [71:0] _zz_2__string;
  reg [71:0] decode_SHIFT_CTRL_string;
  reg [71:0] _zz_3__string;
  reg [71:0] _zz_4__string;
  reg [71:0] _zz_5__string;
  reg [39:0] decode_ALU_BITWISE_CTRL_string;
  reg [39:0] _zz_6__string;
  reg [39:0] _zz_7__string;
  reg [39:0] _zz_8__string;
  reg [95:0] decode_SRC1_CTRL_string;
  reg [95:0] _zz_9__string;
  reg [95:0] _zz_10__string;
  reg [95:0] _zz_11__string;
  reg [23:0] decode_SRC2_CTRL_string;
  reg [23:0] _zz_12__string;
  reg [23:0] _zz_13__string;
  reg [23:0] _zz_14__string;
  reg [63:0] decode_ALU_CTRL_string;
  reg [63:0] _zz_15__string;
  reg [63:0] _zz_16__string;
  reg [63:0] _zz_17__string;
  reg [31:0] _zz_18__string;
  reg [31:0] _zz_19__string;
  reg [31:0] _zz_20__string;
  reg [31:0] _zz_21__string;
  reg [31:0] decode_ENV_CTRL_string;
  reg [31:0] _zz_22__string;
  reg [31:0] _zz_23__string;
  reg [31:0] _zz_24__string;
  reg [31:0] _zz_25__string;
  reg [31:0] _zz_26__string;
  reg [31:0] _zz_27__string;
  reg [31:0] _zz_28__string;
  reg [31:0] execute_BRANCH_CTRL_string;
  reg [31:0] _zz_31__string;
  reg [31:0] memory_ENV_CTRL_string;
  reg [31:0] _zz_35__string;
  reg [31:0] execute_ENV_CTRL_string;
  reg [31:0] _zz_36__string;
  reg [31:0] writeBack_ENV_CTRL_string;
  reg [31:0] _zz_39__string;
  reg [71:0] memory_SHIFT_CTRL_string;
  reg [71:0] _zz_47__string;
  reg [71:0] execute_SHIFT_CTRL_string;
  reg [71:0] _zz_49__string;
  reg [23:0] execute_SRC2_CTRL_string;
  reg [23:0] _zz_54__string;
  reg [95:0] execute_SRC1_CTRL_string;
  reg [95:0] _zz_56__string;
  reg [63:0] execute_ALU_CTRL_string;
  reg [63:0] _zz_59__string;
  reg [39:0] execute_ALU_BITWISE_CTRL_string;
  reg [39:0] _zz_61__string;
  reg [95:0] _zz_68__string;
  reg [31:0] _zz_75__string;
  reg [71:0] _zz_78__string;
  reg [63:0] _zz_84__string;
  reg [39:0] _zz_87__string;
  reg [31:0] _zz_90__string;
  reg [23:0] _zz_91__string;
  reg [31:0] decode_BRANCH_CTRL_string;
  reg [31:0] _zz_101__string;
  reg [31:0] memory_BRANCH_CTRL_string;
  reg [31:0] _zz_102__string;
  reg [47:0] MmuPlugin_shared_state_1__string;
  reg [23:0] _zz_165__string;
  reg [31:0] _zz_166__string;
  reg [39:0] _zz_167__string;
  reg [63:0] _zz_168__string;
  reg [71:0] _zz_169__string;
  reg [31:0] _zz_170__string;
  reg [95:0] _zz_171__string;
  reg [31:0] decode_to_execute_BRANCH_CTRL_string;
  reg [31:0] execute_to_memory_BRANCH_CTRL_string;
  reg [31:0] decode_to_execute_ENV_CTRL_string;
  reg [31:0] execute_to_memory_ENV_CTRL_string;
  reg [31:0] memory_to_writeBack_ENV_CTRL_string;
  reg [63:0] decode_to_execute_ALU_CTRL_string;
  reg [23:0] decode_to_execute_SRC2_CTRL_string;
  reg [95:0] decode_to_execute_SRC1_CTRL_string;
  reg [39:0] decode_to_execute_ALU_BITWISE_CTRL_string;
  reg [71:0] decode_to_execute_SHIFT_CTRL_string;
  reg [71:0] execute_to_memory_SHIFT_CTRL_string;
  `endif

  reg [1:0] _zz_129_ [0:1023];
  reg [31:0] RegFilePlugin_regFile [0:31] /* verilator public */ ;
  assign _zz_269_ = (execute_arbitration_isValid && execute_IS_CSR);
  assign _zz_270_ = (writeBack_arbitration_isValid && writeBack_REGFILE_WRITE_VALID);
  assign _zz_271_ = 1'b1;
  assign _zz_272_ = (memory_arbitration_isValid && memory_REGFILE_WRITE_VALID);
  assign _zz_273_ = (execute_arbitration_isValid && execute_REGFILE_WRITE_VALID);
  assign _zz_274_ = (memory_arbitration_isValid && memory_IS_DIV);
  assign _zz_275_ = ((_zz_227_ && IBusCachedPlugin_cache_io_cpu_decode_error) && (! _zz_97_));
  assign _zz_276_ = ((_zz_227_ && IBusCachedPlugin_cache_io_cpu_decode_cacheMiss) && (! _zz_98_));
  assign _zz_277_ = ((_zz_227_ && IBusCachedPlugin_cache_io_cpu_decode_mmuException) && (! _zz_99_));
  assign _zz_278_ = ((_zz_227_ && IBusCachedPlugin_cache_io_cpu_decode_mmuRefilling) && (! 1'b0));
  assign _zz_279_ = ({decodeExceptionPort_valid,IBusCachedPlugin_decodeExceptionPort_valid} != (2'b00));
  assign _zz_280_ = (execute_arbitration_isValid && execute_DO_EBREAK);
  assign _zz_281_ = (({writeBack_arbitration_isValid,memory_arbitration_isValid} != (2'b00)) == 1'b0);
  assign _zz_282_ = (! memory_DivPlugin_div_done);
  assign _zz_283_ = (CsrPlugin_hadException || CsrPlugin_interruptJump);
  assign _zz_284_ = (writeBack_arbitration_isValid && (writeBack_ENV_CTRL == `EnvCtrlEnum_defaultEncoding_XRET));
  assign _zz_285_ = (DebugPlugin_stepIt && IBusCachedPlugin_incomingInstruction);
  assign _zz_286_ = writeBack_INSTRUCTION[29 : 28];
  assign _zz_287_ = (IBusCachedPlugin_fetchPc_preOutput_valid && IBusCachedPlugin_fetchPc_preOutput_ready);
  assign _zz_288_ = (! ({(writeBack_arbitration_isValid || CsrPlugin_exceptionPendings_3),{(memory_arbitration_isValid || CsrPlugin_exceptionPendings_2),(execute_arbitration_isValid || CsrPlugin_exceptionPendings_1)}} != (3'b000)));
  assign _zz_289_ = (! dataCache_1__io_cpu_redo);
  assign _zz_290_ = (writeBack_arbitration_isValid && writeBack_MEMORY_ENABLE);
  assign _zz_291_ = ((MmuPlugin_dBusAccess_rsp_valid && (! MmuPlugin_dBusAccess_rsp_payload_redo)) && (MmuPlugin_shared_dBusRsp_leaf || MmuPlugin_shared_dBusRsp_exception));
  assign _zz_292_ = (MmuPlugin_shared_portId == (1'b1));
  assign _zz_293_ = (MmuPlugin_shared_portId == (1'b0));
  assign _zz_294_ = (writeBack_arbitration_isValid && writeBack_REGFILE_WRITE_VALID);
  assign _zz_295_ = (1'b0 || (! 1'b1));
  assign _zz_296_ = (memory_arbitration_isValid && memory_REGFILE_WRITE_VALID);
  assign _zz_297_ = (1'b0 || (! memory_BYPASSABLE_MEMORY_STAGE));
  assign _zz_298_ = (execute_arbitration_isValid && execute_REGFILE_WRITE_VALID);
  assign _zz_299_ = (1'b0 || (! execute_BYPASSABLE_EXECUTE_STAGE));
  assign _zz_300_ = execute_INSTRUCTION[13 : 12];
  assign _zz_301_ = (! memory_arbitration_isStuck);
  assign _zz_302_ = (CsrPlugin_mstatus_MIE || (CsrPlugin_privilege < (2'b11)));
  assign _zz_303_ = (((CsrPlugin_mip_MTIP && CsrPlugin_mie_MTIE) && 1'b1) && (! 1'b0));
  assign _zz_304_ = (((CsrPlugin_mip_MSIP && CsrPlugin_mie_MSIE) && 1'b1) && (! 1'b0));
  assign _zz_305_ = (((CsrPlugin_mip_MEIP && CsrPlugin_mie_MEIE) && 1'b1) && (! 1'b0));
  assign _zz_306_ = debug_bus_cmd_payload_address[7 : 2];
  assign _zz_307_ = (IBusCachedPlugin_mmuBus_cmd_isValid && IBusCachedPlugin_mmuBus_rsp_refilling);
  assign _zz_308_ = (DBusCachedPlugin_mmuBus_cmd_isValid && DBusCachedPlugin_mmuBus_rsp_refilling);
  assign _zz_309_ = (MmuPlugin_ports_0_entryToReplace_value == (3'b000));
  assign _zz_310_ = (MmuPlugin_ports_0_entryToReplace_value == (3'b001));
  assign _zz_311_ = (MmuPlugin_ports_0_entryToReplace_value == (3'b010));
  assign _zz_312_ = (MmuPlugin_ports_0_entryToReplace_value == (3'b011));
  assign _zz_313_ = (MmuPlugin_ports_0_entryToReplace_value == (3'b100));
  assign _zz_314_ = (MmuPlugin_ports_0_entryToReplace_value == (3'b101));
  assign _zz_315_ = (MmuPlugin_ports_1_entryToReplace_value == (2'b00));
  assign _zz_316_ = (MmuPlugin_ports_1_entryToReplace_value == (2'b01));
  assign _zz_317_ = (MmuPlugin_ports_1_entryToReplace_value == (2'b10));
  assign _zz_318_ = (MmuPlugin_ports_1_entryToReplace_value == (2'b11));
  assign _zz_319_ = writeBack_INSTRUCTION[13 : 12];
  assign _zz_320_ = writeBack_INSTRUCTION[13 : 12];
  assign _zz_321_ = execute_INSTRUCTION[13];
  assign _zz_322_ = (_zz_112_ - (5'b00001));
  assign _zz_323_ = {IBusCachedPlugin_fetchPc_inc,(2'b00)};
  assign _zz_324_ = {29'd0, _zz_323_};
  assign _zz_325_ = ($signed(memory_PREDICTION_CONTEXT_line_history) + $signed(_zz_326_));
  assign _zz_326_ = (_zz_138_ ? _zz_327_ : _zz_328_);
  assign _zz_327_ = (2'b11);
  assign _zz_328_ = (2'b01);
  assign _zz_329_ = _zz_134_[9:0];
  assign _zz_330_ = (IBusCachedPlugin_iBusRsp_stages_0_input_payload >>> 2);
  assign _zz_331_ = _zz_330_[9:0];
  assign _zz_332_ = (_zz_138_ ? _zz_333_ : _zz_334_);
  assign _zz_333_ = (2'b10);
  assign _zz_334_ = (2'b01);
  assign _zz_335_ = {{{decode_INSTRUCTION[31],decode_INSTRUCTION[19 : 12]},decode_INSTRUCTION[20]},decode_INSTRUCTION[30 : 21]};
  assign _zz_336_ = {{{decode_INSTRUCTION[31],decode_INSTRUCTION[7]},decode_INSTRUCTION[30 : 25]},decode_INSTRUCTION[11 : 8]};
  assign _zz_337_ = {{_zz_140_,{{{decode_INSTRUCTION[31],decode_INSTRUCTION[19 : 12]},decode_INSTRUCTION[20]},decode_INSTRUCTION[30 : 21]}},1'b0};
  assign _zz_338_ = {{_zz_142_,{{{decode_INSTRUCTION[31],decode_INSTRUCTION[7]},decode_INSTRUCTION[30 : 25]},decode_INSTRUCTION[11 : 8]}},1'b0};
  assign _zz_339_ = {{{decode_INSTRUCTION[31],decode_INSTRUCTION[19 : 12]},decode_INSTRUCTION[20]},decode_INSTRUCTION[30 : 21]};
  assign _zz_340_ = {{{decode_INSTRUCTION[31],decode_INSTRUCTION[7]},decode_INSTRUCTION[30 : 25]},decode_INSTRUCTION[11 : 8]};
  assign _zz_341_ = (writeBack_MEMORY_WR ? (3'b111) : (3'b101));
  assign _zz_342_ = (writeBack_MEMORY_WR ? (3'b110) : (3'b100));
  assign _zz_343_ = MmuPlugin_ports_0_entryToReplace_willIncrement;
  assign _zz_344_ = {2'd0, _zz_343_};
  assign _zz_345_ = MmuPlugin_ports_1_entryToReplace_willIncrement;
  assign _zz_346_ = {1'd0, _zz_345_};
  assign _zz_347_ = MmuPlugin_dBusAccess_rsp_payload_data[0 : 0];
  assign _zz_348_ = MmuPlugin_dBusAccess_rsp_payload_data[1 : 1];
  assign _zz_349_ = MmuPlugin_dBusAccess_rsp_payload_data[2 : 2];
  assign _zz_350_ = MmuPlugin_dBusAccess_rsp_payload_data[3 : 3];
  assign _zz_351_ = MmuPlugin_dBusAccess_rsp_payload_data[4 : 4];
  assign _zz_352_ = MmuPlugin_dBusAccess_rsp_payload_data[5 : 5];
  assign _zz_353_ = MmuPlugin_dBusAccess_rsp_payload_data[6 : 6];
  assign _zz_354_ = MmuPlugin_dBusAccess_rsp_payload_data[7 : 7];
  assign _zz_355_ = _zz_160_[0 : 0];
  assign _zz_356_ = _zz_160_[4 : 4];
  assign _zz_357_ = _zz_160_[5 : 5];
  assign _zz_358_ = _zz_160_[8 : 8];
  assign _zz_359_ = _zz_160_[9 : 9];
  assign _zz_360_ = _zz_160_[13 : 13];
  assign _zz_361_ = _zz_160_[14 : 14];
  assign _zz_362_ = _zz_160_[15 : 15];
  assign _zz_363_ = _zz_160_[16 : 16];
  assign _zz_364_ = _zz_160_[17 : 17];
  assign _zz_365_ = _zz_160_[20 : 20];
  assign _zz_366_ = _zz_160_[21 : 21];
  assign _zz_367_ = _zz_160_[24 : 24];
  assign _zz_368_ = _zz_160_[25 : 25];
  assign _zz_369_ = _zz_160_[26 : 26];
  assign _zz_370_ = _zz_160_[27 : 27];
  assign _zz_371_ = _zz_160_[28 : 28];
  assign _zz_372_ = _zz_160_[29 : 29];
  assign _zz_373_ = _zz_160_[32 : 32];
  assign _zz_374_ = execute_SRC_LESS;
  assign _zz_375_ = (3'b100);
  assign _zz_376_ = execute_INSTRUCTION[19 : 15];
  assign _zz_377_ = execute_INSTRUCTION[31 : 20];
  assign _zz_378_ = {execute_INSTRUCTION[31 : 25],execute_INSTRUCTION[11 : 7]};
  assign _zz_379_ = ($signed(_zz_380_) + $signed(_zz_383_));
  assign _zz_380_ = ($signed(_zz_381_) + $signed(_zz_382_));
  assign _zz_381_ = execute_SRC1;
  assign _zz_382_ = (execute_SRC_USE_SUB_LESS ? (~ execute_SRC2) : execute_SRC2);
  assign _zz_383_ = (execute_SRC_USE_SUB_LESS ? _zz_384_ : _zz_385_);
  assign _zz_384_ = (32'b00000000000000000000000000000001);
  assign _zz_385_ = (32'b00000000000000000000000000000000);
  assign _zz_386_ = ($signed(_zz_388_) >>> execute_FullBarrelShifterPlugin_amplitude);
  assign _zz_387_ = _zz_386_[31 : 0];
  assign _zz_388_ = {((execute_SHIFT_CTRL == `ShiftCtrlEnum_defaultEncoding_SRA_1) && execute_FullBarrelShifterPlugin_reversed[31]),execute_FullBarrelShifterPlugin_reversed};
  assign _zz_389_ = ($signed(_zz_390_) + $signed(_zz_395_));
  assign _zz_390_ = ($signed(_zz_391_) + $signed(_zz_393_));
  assign _zz_391_ = (52'b0000000000000000000000000000000000000000000000000000);
  assign _zz_392_ = {1'b0,memory_MUL_LL};
  assign _zz_393_ = {{19{_zz_392_[32]}}, _zz_392_};
  assign _zz_394_ = ({16'd0,memory_MUL_LH} <<< 16);
  assign _zz_395_ = {{2{_zz_394_[49]}}, _zz_394_};
  assign _zz_396_ = ({16'd0,memory_MUL_HL} <<< 16);
  assign _zz_397_ = {{2{_zz_396_[49]}}, _zz_396_};
  assign _zz_398_ = {{14{writeBack_MUL_LOW[51]}}, writeBack_MUL_LOW};
  assign _zz_399_ = ({32'd0,writeBack_MUL_HH} <<< 32);
  assign _zz_400_ = writeBack_MUL_LOW[31 : 0];
  assign _zz_401_ = writeBack_MulPlugin_result[63 : 32];
  assign _zz_402_ = memory_DivPlugin_div_counter_willIncrement;
  assign _zz_403_ = {5'd0, _zz_402_};
  assign _zz_404_ = {1'd0, memory_DivPlugin_rs2};
  assign _zz_405_ = {_zz_194_,(! _zz_196_[32])};
  assign _zz_406_ = _zz_196_[31:0];
  assign _zz_407_ = _zz_195_[31:0];
  assign _zz_408_ = _zz_409_;
  assign _zz_409_ = _zz_410_;
  assign _zz_410_ = ({1'b0,(memory_DivPlugin_div_needRevert ? (~ _zz_197_) : _zz_197_)} + _zz_412_);
  assign _zz_411_ = memory_DivPlugin_div_needRevert;
  assign _zz_412_ = {32'd0, _zz_411_};
  assign _zz_413_ = _zz_199_;
  assign _zz_414_ = {32'd0, _zz_413_};
  assign _zz_415_ = _zz_198_;
  assign _zz_416_ = {31'd0, _zz_415_};
  assign _zz_417_ = (_zz_201_ & (~ _zz_418_));
  assign _zz_418_ = (_zz_201_ - (2'b01));
  assign _zz_419_ = execute_INSTRUCTION[31 : 20];
  assign _zz_420_ = {{{execute_INSTRUCTION[31],execute_INSTRUCTION[19 : 12]},execute_INSTRUCTION[20]},execute_INSTRUCTION[30 : 21]};
  assign _zz_421_ = {{{execute_INSTRUCTION[31],execute_INSTRUCTION[7]},execute_INSTRUCTION[30 : 25]},execute_INSTRUCTION[11 : 8]};
  assign _zz_422_ = {_zz_208_,execute_INSTRUCTION[31 : 20]};
  assign _zz_423_ = {{_zz_210_,{{{execute_INSTRUCTION[31],execute_INSTRUCTION[19 : 12]},execute_INSTRUCTION[20]},execute_INSTRUCTION[30 : 21]}},1'b0};
  assign _zz_424_ = {{_zz_212_,{{{execute_INSTRUCTION[31],execute_INSTRUCTION[7]},execute_INSTRUCTION[30 : 25]},execute_INSTRUCTION[11 : 8]}},1'b0};
  assign _zz_425_ = execute_INSTRUCTION[31 : 20];
  assign _zz_426_ = {{{execute_INSTRUCTION[31],execute_INSTRUCTION[19 : 12]},execute_INSTRUCTION[20]},execute_INSTRUCTION[30 : 21]};
  assign _zz_427_ = {{{execute_INSTRUCTION[31],execute_INSTRUCTION[7]},execute_INSTRUCTION[30 : 25]},execute_INSTRUCTION[11 : 8]};
  assign _zz_428_ = (3'b100);
  assign _zz_429_ = execute_CsrPlugin_writeData[19 : 19];
  assign _zz_430_ = execute_CsrPlugin_writeData[18 : 18];
  assign _zz_431_ = execute_CsrPlugin_writeData[17 : 17];
  assign _zz_432_ = execute_CsrPlugin_writeData[7 : 7];
  assign _zz_433_ = execute_CsrPlugin_writeData[3 : 3];
  assign _zz_434_ = execute_CsrPlugin_writeData[19 : 19];
  assign _zz_435_ = execute_CsrPlugin_writeData[18 : 18];
  assign _zz_436_ = execute_CsrPlugin_writeData[17 : 17];
  assign _zz_437_ = execute_CsrPlugin_writeData[3 : 3];
  assign _zz_438_ = execute_CsrPlugin_writeData[31 : 31];
  assign _zz_439_ = execute_CsrPlugin_writeData[11 : 11];
  assign _zz_440_ = execute_CsrPlugin_writeData[7 : 7];
  assign _zz_441_ = execute_CsrPlugin_writeData[3 : 3];
  assign _zz_442_ = _zz_325_;
  assign _zz_443_ = 1'b1;
  assign _zz_444_ = 1'b1;
  assign _zz_445_ = {_zz_115_,{_zz_117_,_zz_116_}};
  assign _zz_446_ = decode_INSTRUCTION[31];
  assign _zz_447_ = decode_INSTRUCTION[31];
  assign _zz_448_ = decode_INSTRUCTION[7];
  assign _zz_449_ = (32'b00000000000000000000000000100000);
  assign _zz_450_ = ((decode_INSTRUCTION & (32'b00000000000000000000000000010100)) == (32'b00000000000000000000000000000100));
  assign _zz_451_ = ((decode_INSTRUCTION & _zz_458_) == (32'b00000000000000000000000000000100));
  assign _zz_452_ = _zz_164_;
  assign _zz_453_ = {(_zz_459_ == _zz_460_),{_zz_461_,{_zz_462_,_zz_463_}}};
  assign _zz_454_ = (4'b0000);
  assign _zz_455_ = ((_zz_464_ == _zz_465_) != (1'b0));
  assign _zz_456_ = ({_zz_466_,_zz_467_} != (6'b000000));
  assign _zz_457_ = {(_zz_468_ != _zz_469_),{_zz_470_,{_zz_471_,_zz_472_}}};
  assign _zz_458_ = (32'b00000000000000000000000001000100);
  assign _zz_459_ = (decode_INSTRUCTION & (32'b00000000000000000000000001000100));
  assign _zz_460_ = (32'b00000000000000000000000000000000);
  assign _zz_461_ = ((decode_INSTRUCTION & _zz_473_) == (32'b00000000000000000000000000000000));
  assign _zz_462_ = (_zz_474_ == _zz_475_);
  assign _zz_463_ = (_zz_476_ == _zz_477_);
  assign _zz_464_ = (decode_INSTRUCTION & (32'b00000000000000000101000001001000));
  assign _zz_465_ = (32'b00000000000000000001000000001000);
  assign _zz_466_ = _zz_163_;
  assign _zz_467_ = {_zz_478_,{_zz_479_,_zz_480_}};
  assign _zz_468_ = {_zz_481_,{_zz_482_,_zz_483_}};
  assign _zz_469_ = (5'b00000);
  assign _zz_470_ = ({_zz_484_,_zz_485_} != (2'b00));
  assign _zz_471_ = (_zz_486_ != _zz_487_);
  assign _zz_472_ = {_zz_488_,{_zz_489_,_zz_490_}};
  assign _zz_473_ = (32'b00000000000000000000000000011000);
  assign _zz_474_ = (decode_INSTRUCTION & (32'b00000000000000000110000000000100));
  assign _zz_475_ = (32'b00000000000000000010000000000000);
  assign _zz_476_ = (decode_INSTRUCTION & (32'b00000000000000000101000000000100));
  assign _zz_477_ = (32'b00000000000000000001000000000000);
  assign _zz_478_ = ((decode_INSTRUCTION & _zz_491_) == (32'b00000000000000000001000000010000));
  assign _zz_479_ = (_zz_492_ == _zz_493_);
  assign _zz_480_ = {_zz_494_,{_zz_495_,_zz_496_}};
  assign _zz_481_ = ((decode_INSTRUCTION & _zz_497_) == (32'b00000000000000000000000001000000));
  assign _zz_482_ = _zz_161_;
  assign _zz_483_ = {_zz_498_,{_zz_499_,_zz_500_}};
  assign _zz_484_ = (_zz_501_ == _zz_502_);
  assign _zz_485_ = (_zz_503_ == _zz_504_);
  assign _zz_486_ = (_zz_505_ == _zz_506_);
  assign _zz_487_ = (1'b0);
  assign _zz_488_ = ({_zz_507_,_zz_508_} != (2'b00));
  assign _zz_489_ = (_zz_509_ != _zz_510_);
  assign _zz_490_ = {_zz_511_,{_zz_512_,_zz_513_}};
  assign _zz_491_ = (32'b00000000000000000001000000010000);
  assign _zz_492_ = (decode_INSTRUCTION & (32'b00000000000000000010000000010000));
  assign _zz_493_ = (32'b00000000000000000010000000010000);
  assign _zz_494_ = ((decode_INSTRUCTION & _zz_514_) == (32'b00000000000000000000000000010000));
  assign _zz_495_ = (_zz_515_ == _zz_516_);
  assign _zz_496_ = (_zz_517_ == _zz_518_);
  assign _zz_497_ = (32'b00000000000000000000000001000000);
  assign _zz_498_ = ((decode_INSTRUCTION & _zz_519_) == (32'b00000000000000000100000000100000));
  assign _zz_499_ = (_zz_520_ == _zz_521_);
  assign _zz_500_ = (_zz_522_ == _zz_523_);
  assign _zz_501_ = (decode_INSTRUCTION & (32'b00000000000000000010000000010000));
  assign _zz_502_ = (32'b00000000000000000010000000000000);
  assign _zz_503_ = (decode_INSTRUCTION & (32'b00000000000000000101000000000000));
  assign _zz_504_ = (32'b00000000000000000001000000000000);
  assign _zz_505_ = (decode_INSTRUCTION & (32'b00000010000000000100000001110100));
  assign _zz_506_ = (32'b00000010000000000000000000110000);
  assign _zz_507_ = _zz_163_;
  assign _zz_508_ = (_zz_524_ == _zz_525_);
  assign _zz_509_ = (_zz_526_ == _zz_527_);
  assign _zz_510_ = (1'b0);
  assign _zz_511_ = (_zz_162_ != (1'b0));
  assign _zz_512_ = (_zz_528_ != _zz_529_);
  assign _zz_513_ = {_zz_530_,{_zz_531_,_zz_532_}};
  assign _zz_514_ = (32'b00000000000000000000000001010000);
  assign _zz_515_ = (decode_INSTRUCTION & (32'b00000000000000000000000000001100));
  assign _zz_516_ = (32'b00000000000000000000000000000100);
  assign _zz_517_ = (decode_INSTRUCTION & (32'b00000000000000000000000000101000));
  assign _zz_518_ = (32'b00000000000000000000000000000000);
  assign _zz_519_ = (32'b00000000000000000100000000100000);
  assign _zz_520_ = (decode_INSTRUCTION & (32'b00000000000000000000000000110000));
  assign _zz_521_ = (32'b00000000000000000000000000010000);
  assign _zz_522_ = (decode_INSTRUCTION & (32'b00000010000000000000000000100000));
  assign _zz_523_ = (32'b00000000000000000000000000100000);
  assign _zz_524_ = (decode_INSTRUCTION & (32'b00000000000000000000000000011100));
  assign _zz_525_ = (32'b00000000000000000000000000000100);
  assign _zz_526_ = (decode_INSTRUCTION & (32'b00000000000000000000000001011000));
  assign _zz_527_ = (32'b00000000000000000000000001000000);
  assign _zz_528_ = ((decode_INSTRUCTION & (32'b00010000000000000011000001010000)) == (32'b00000000000000000000000001010000));
  assign _zz_529_ = (1'b0);
  assign _zz_530_ = ({(_zz_533_ == _zz_534_),(_zz_535_ == _zz_536_)} != (2'b00));
  assign _zz_531_ = ({_zz_537_,{_zz_538_,_zz_539_}} != (3'b000));
  assign _zz_532_ = {(_zz_540_ != (1'b0)),{(_zz_541_ != _zz_542_),{_zz_543_,{_zz_544_,_zz_545_}}}};
  assign _zz_533_ = (decode_INSTRUCTION & (32'b00000000000000000111000000110100));
  assign _zz_534_ = (32'b00000000000000000101000000010000);
  assign _zz_535_ = (decode_INSTRUCTION & (32'b00000010000000000111000001100100));
  assign _zz_536_ = (32'b00000000000000000101000000100000);
  assign _zz_537_ = ((decode_INSTRUCTION & (32'b01000000000000000011000001010100)) == (32'b01000000000000000001000000010000));
  assign _zz_538_ = ((decode_INSTRUCTION & _zz_546_) == (32'b00000000000000000001000000010000));
  assign _zz_539_ = ((decode_INSTRUCTION & _zz_547_) == (32'b00000000000000000001000000010000));
  assign _zz_540_ = ((decode_INSTRUCTION & (32'b00000010000000000011000001010000)) == (32'b00000010000000000000000001010000));
  assign _zz_541_ = ((decode_INSTRUCTION & _zz_548_) == (32'b00000010000000000100000000100000));
  assign _zz_542_ = (1'b0);
  assign _zz_543_ = ({_zz_549_,{_zz_550_,_zz_551_}} != (3'b000));
  assign _zz_544_ = ({_zz_552_,_zz_553_} != (2'b00));
  assign _zz_545_ = {(_zz_554_ != _zz_555_),{_zz_556_,{_zz_557_,_zz_558_}}};
  assign _zz_546_ = (32'b00000000000000000111000000110100);
  assign _zz_547_ = (32'b00000010000000000111000001010100);
  assign _zz_548_ = (32'b00000010000000000100000001100100);
  assign _zz_549_ = ((decode_INSTRUCTION & (32'b00000000000000000000000001000100)) == (32'b00000000000000000000000001000000));
  assign _zz_550_ = ((decode_INSTRUCTION & _zz_559_) == (32'b00000000000000000010000000010000));
  assign _zz_551_ = ((decode_INSTRUCTION & _zz_560_) == (32'b01000000000000000000000000110000));
  assign _zz_552_ = ((decode_INSTRUCTION & _zz_561_) == (32'b00000000000000000001000001010000));
  assign _zz_553_ = ((decode_INSTRUCTION & _zz_562_) == (32'b00000000000000000010000001010000));
  assign _zz_554_ = ((decode_INSTRUCTION & _zz_563_) == (32'b00000000000000000000000000000000));
  assign _zz_555_ = (1'b0);
  assign _zz_556_ = ((_zz_564_ == _zz_565_) != (1'b0));
  assign _zz_557_ = (_zz_566_ != (1'b0));
  assign _zz_558_ = {(_zz_567_ != _zz_568_),{_zz_569_,{_zz_570_,_zz_571_}}};
  assign _zz_559_ = (32'b00000000000000000010000000010100);
  assign _zz_560_ = (32'b01000000000000000000000000110100);
  assign _zz_561_ = (32'b00000000000000000001000001010000);
  assign _zz_562_ = (32'b00000000000000000010000001010000);
  assign _zz_563_ = (32'b00000000000000000000000001011000);
  assign _zz_564_ = (decode_INSTRUCTION & (32'b00000000000000000100000000010100));
  assign _zz_565_ = (32'b00000000000000000100000000010000);
  assign _zz_566_ = ((decode_INSTRUCTION & (32'b00000000000000000110000000010100)) == (32'b00000000000000000010000000010000));
  assign _zz_567_ = {(_zz_572_ == _zz_573_),{_zz_574_,_zz_575_}};
  assign _zz_568_ = (3'b000);
  assign _zz_569_ = ((_zz_576_ == _zz_577_) != (1'b0));
  assign _zz_570_ = ({_zz_578_,_zz_579_} != (5'b00000));
  assign _zz_571_ = {(_zz_580_ != _zz_581_),{_zz_582_,{_zz_583_,_zz_584_}}};
  assign _zz_572_ = (decode_INSTRUCTION & (32'b00000000000000000000000001010000));
  assign _zz_573_ = (32'b00000000000000000000000001000000);
  assign _zz_574_ = ((decode_INSTRUCTION & (32'b00000000000000000000000000111000)) == (32'b00000000000000000000000000000000));
  assign _zz_575_ = ((decode_INSTRUCTION & (32'b00000010000100000011000001000000)) == (32'b00000000000000000000000001000000));
  assign _zz_576_ = (decode_INSTRUCTION & (32'b00000000000000000000000001100100));
  assign _zz_577_ = (32'b00000000000000000000000000100100);
  assign _zz_578_ = _zz_161_;
  assign _zz_579_ = {(_zz_585_ == _zz_586_),{_zz_587_,{_zz_588_,_zz_589_}}};
  assign _zz_580_ = ((decode_INSTRUCTION & _zz_590_) == (32'b00000000000000000001000000000000));
  assign _zz_581_ = (1'b0);
  assign _zz_582_ = ((_zz_591_ == _zz_592_) != (1'b0));
  assign _zz_583_ = ({_zz_593_,_zz_594_} != (2'b00));
  assign _zz_584_ = {(_zz_595_ != _zz_596_),{_zz_597_,{_zz_598_,_zz_599_}}};
  assign _zz_585_ = (decode_INSTRUCTION & (32'b00000000000000000010000000110000));
  assign _zz_586_ = (32'b00000000000000000010000000010000);
  assign _zz_587_ = ((decode_INSTRUCTION & (32'b00000000000000000001000000110000)) == (32'b00000000000000000000000000010000));
  assign _zz_588_ = ((decode_INSTRUCTION & _zz_600_) == (32'b00000000000000000010000000100000));
  assign _zz_589_ = ((decode_INSTRUCTION & _zz_601_) == (32'b00000000000000000000000000100000));
  assign _zz_590_ = (32'b00000000000000000001000000000000);
  assign _zz_591_ = (decode_INSTRUCTION & (32'b00000000000000000011000000000000));
  assign _zz_592_ = (32'b00000000000000000010000000000000);
  assign _zz_593_ = ((decode_INSTRUCTION & _zz_602_) == (32'b00000000000000000000000000100000));
  assign _zz_594_ = ((decode_INSTRUCTION & _zz_603_) == (32'b00000000000000000000000000100000));
  assign _zz_595_ = _zz_162_;
  assign _zz_596_ = (1'b0);
  assign _zz_597_ = ((_zz_604_ == _zz_605_) != (1'b0));
  assign _zz_598_ = ({_zz_606_,_zz_607_} != (2'b00));
  assign _zz_599_ = {(_zz_608_ != _zz_609_),(_zz_610_ != _zz_611_)};
  assign _zz_600_ = (32'b00000010000000000010000001100000);
  assign _zz_601_ = (32'b00000010000000000011000000100000);
  assign _zz_602_ = (32'b00000000000000000000000000110100);
  assign _zz_603_ = (32'b00000000000000000000000001100100);
  assign _zz_604_ = (decode_INSTRUCTION & (32'b00000010000100000011000001010000));
  assign _zz_605_ = (32'b00000000000000000000000001010000);
  assign _zz_606_ = _zz_161_;
  assign _zz_607_ = ((decode_INSTRUCTION & (32'b00000000000000000000000001110000)) == (32'b00000000000000000000000000100000));
  assign _zz_608_ = {_zz_161_,((decode_INSTRUCTION & (32'b00000000000000000000000000100000)) == (32'b00000000000000000000000000000000))};
  assign _zz_609_ = (2'b00);
  assign _zz_610_ = ((decode_INSTRUCTION & (32'b00000000000000000100000001001000)) == (32'b00000000000000000100000000001000));
  assign _zz_611_ = (1'b0);
  assign _zz_612_ = (32'b00000000000000000001000001111111);
  assign _zz_613_ = (decode_INSTRUCTION & (32'b00000000000000000010000001111111));
  assign _zz_614_ = (32'b00000000000000000010000001110011);
  assign _zz_615_ = ((decode_INSTRUCTION & (32'b00000000000000000100000001111111)) == (32'b00000000000000000100000001100011));
  assign _zz_616_ = ((decode_INSTRUCTION & (32'b00000000000000000010000001111111)) == (32'b00000000000000000010000000010011));
  assign _zz_617_ = {((decode_INSTRUCTION & (32'b00000000000000000110000000111111)) == (32'b00000000000000000000000000100011)),{((decode_INSTRUCTION & (32'b00000000000000000010000001111111)) == (32'b00000000000000000000000000000011)),{((decode_INSTRUCTION & _zz_618_) == (32'b00000000000000000000000000000011)),{(_zz_619_ == _zz_620_),{_zz_621_,{_zz_622_,_zz_623_}}}}}};
  assign _zz_618_ = (32'b00000000000000000101000001011111);
  assign _zz_619_ = (decode_INSTRUCTION & (32'b00000000000000000111000001111011));
  assign _zz_620_ = (32'b00000000000000000000000001100011);
  assign _zz_621_ = ((decode_INSTRUCTION & (32'b00000000000000000110000001111111)) == (32'b00000000000000000000000000001111));
  assign _zz_622_ = ((decode_INSTRUCTION & (32'b11111100000000000000000001111111)) == (32'b00000000000000000000000000110011));
  assign _zz_623_ = {((decode_INSTRUCTION & (32'b00000001111100000111000001111111)) == (32'b00000000000000000101000000001111)),{((decode_INSTRUCTION & (32'b10111100000000000111000001111111)) == (32'b00000000000000000101000000010011)),{((decode_INSTRUCTION & _zz_624_) == (32'b00000000000000000001000000010011)),{(_zz_625_ == _zz_626_),{_zz_627_,{_zz_628_,_zz_629_}}}}}};
  assign _zz_624_ = (32'b11111100000000000011000001111111);
  assign _zz_625_ = (decode_INSTRUCTION & (32'b10111110000000000111000001111111));
  assign _zz_626_ = (32'b00000000000000000101000000110011);
  assign _zz_627_ = ((decode_INSTRUCTION & (32'b10111110000000000111000001111111)) == (32'b00000000000000000000000000110011));
  assign _zz_628_ = ((decode_INSTRUCTION & (32'b11111110000000000111111111111111)) == (32'b00010010000000000000000001110011));
  assign _zz_629_ = {((decode_INSTRUCTION & (32'b11011111111111111111111111111111)) == (32'b00010000001000000000000001110011)),((decode_INSTRUCTION & (32'b11111111111111111111111111111111)) == (32'b00000000000100000000000001110011))};
  assign _zz_630_ = execute_INSTRUCTION[31];
  assign _zz_631_ = execute_INSTRUCTION[31];
  assign _zz_632_ = execute_INSTRUCTION[7];
  always @ (posedge clk) begin
    if(_zz_105_) begin
      _zz_129_[_zz_131_] <= _zz_442_;
    end
  end

  always @ (posedge clk) begin
    if(_zz_135_) begin
      _zz_243_ <= _zz_129_[_zz_329_];
    end
  end

  always @ (posedge clk) begin
    if(_zz_64_) begin
      RegFilePlugin_regFile[lastStageRegFileWrite_payload_address] <= lastStageRegFileWrite_payload_data;
    end
  end

  always @ (posedge clk) begin
    if(_zz_443_) begin
      _zz_244_ <= RegFilePlugin_regFile[decode_RegFilePlugin_regFileReadAddress1];
    end
  end

  always @ (posedge clk) begin
    if(_zz_444_) begin
      _zz_245_ <= RegFilePlugin_regFile[decode_RegFilePlugin_regFileReadAddress2];
    end
  end

  InstructionCache IBusCachedPlugin_cache ( 
    .io_flush(_zz_221_),
    .io_cpu_prefetch_isValid(_zz_222_),
    .io_cpu_prefetch_haltIt(IBusCachedPlugin_cache_io_cpu_prefetch_haltIt),
    .io_cpu_prefetch_pc(IBusCachedPlugin_iBusRsp_stages_0_input_payload),
    .io_cpu_fetch_isValid(_zz_223_),
    .io_cpu_fetch_isStuck(_zz_224_),
    .io_cpu_fetch_isRemoved(_zz_225_),
    .io_cpu_fetch_pc(IBusCachedPlugin_iBusRsp_stages_1_input_payload),
    .io_cpu_fetch_data(IBusCachedPlugin_cache_io_cpu_fetch_data),
    .io_cpu_fetch_dataBypassValid(IBusCachedPlugin_s1_tightlyCoupledHit),
    .io_cpu_fetch_dataBypass(_zz_226_),
    .io_cpu_fetch_mmuBus_cmd_isValid(IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_cmd_isValid),
    .io_cpu_fetch_mmuBus_cmd_virtualAddress(IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_cmd_virtualAddress),
    .io_cpu_fetch_mmuBus_cmd_bypassTranslation(IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_cmd_bypassTranslation),
    .io_cpu_fetch_mmuBus_rsp_physicalAddress(IBusCachedPlugin_mmuBus_rsp_physicalAddress),
    .io_cpu_fetch_mmuBus_rsp_isIoAccess(IBusCachedPlugin_mmuBus_rsp_isIoAccess),
    .io_cpu_fetch_mmuBus_rsp_allowRead(IBusCachedPlugin_mmuBus_rsp_allowRead),
    .io_cpu_fetch_mmuBus_rsp_allowWrite(IBusCachedPlugin_mmuBus_rsp_allowWrite),
    .io_cpu_fetch_mmuBus_rsp_allowExecute(IBusCachedPlugin_mmuBus_rsp_allowExecute),
    .io_cpu_fetch_mmuBus_rsp_exception(IBusCachedPlugin_mmuBus_rsp_exception),
    .io_cpu_fetch_mmuBus_rsp_refilling(IBusCachedPlugin_mmuBus_rsp_refilling),
    .io_cpu_fetch_mmuBus_end(IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_end),
    .io_cpu_fetch_mmuBus_busy(IBusCachedPlugin_mmuBus_busy),
    .io_cpu_fetch_physicalAddress(IBusCachedPlugin_cache_io_cpu_fetch_physicalAddress),
    .io_cpu_fetch_haltIt(IBusCachedPlugin_cache_io_cpu_fetch_haltIt),
    .io_cpu_decode_isValid(_zz_227_),
    .io_cpu_decode_isStuck(_zz_228_),
    .io_cpu_decode_pc(IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_payload),
    .io_cpu_decode_physicalAddress(IBusCachedPlugin_cache_io_cpu_decode_physicalAddress),
    .io_cpu_decode_data(IBusCachedPlugin_cache_io_cpu_decode_data),
    .io_cpu_decode_cacheMiss(IBusCachedPlugin_cache_io_cpu_decode_cacheMiss),
    .io_cpu_decode_error(IBusCachedPlugin_cache_io_cpu_decode_error),
    .io_cpu_decode_mmuRefilling(IBusCachedPlugin_cache_io_cpu_decode_mmuRefilling),
    .io_cpu_decode_mmuException(IBusCachedPlugin_cache_io_cpu_decode_mmuException),
    .io_cpu_decode_isUser(_zz_229_),
    .io_cpu_fill_valid(_zz_230_),
    .io_cpu_fill_payload(IBusCachedPlugin_cache_io_cpu_decode_physicalAddress),
    .io_mem_cmd_valid(IBusCachedPlugin_cache_io_mem_cmd_valid),
    .io_mem_cmd_ready(iBus_cmd_ready),
    .io_mem_cmd_payload_address(IBusCachedPlugin_cache_io_mem_cmd_payload_address),
    .io_mem_cmd_payload_size(IBusCachedPlugin_cache_io_mem_cmd_payload_size),
    .io_mem_rsp_valid(iBus_rsp_valid),
    .io_mem_rsp_payload_data(iBus_rsp_payload_data),
    .io_mem_rsp_payload_error(iBus_rsp_payload_error),
    .clk(clk),
    .reset(reset) 
  );
  DataCache dataCache_1_ ( 
    .io_cpu_execute_isValid(_zz_231_),
    .io_cpu_execute_address(_zz_232_),
    .io_cpu_execute_args_wr(_zz_233_),
    .io_cpu_execute_args_data(_zz_234_),
    .io_cpu_execute_args_size(_zz_235_),
    .io_cpu_memory_isValid(_zz_236_),
    .io_cpu_memory_isStuck(memory_arbitration_isStuck),
    .io_cpu_memory_isRemoved(memory_arbitration_removeIt),
    .io_cpu_memory_isWrite(dataCache_1__io_cpu_memory_isWrite),
    .io_cpu_memory_address(_zz_237_),
    .io_cpu_memory_mmuBus_cmd_isValid(dataCache_1__io_cpu_memory_mmuBus_cmd_isValid),
    .io_cpu_memory_mmuBus_cmd_virtualAddress(dataCache_1__io_cpu_memory_mmuBus_cmd_virtualAddress),
    .io_cpu_memory_mmuBus_cmd_bypassTranslation(dataCache_1__io_cpu_memory_mmuBus_cmd_bypassTranslation),
    .io_cpu_memory_mmuBus_rsp_physicalAddress(DBusCachedPlugin_mmuBus_rsp_physicalAddress),
    .io_cpu_memory_mmuBus_rsp_isIoAccess(_zz_238_),
    .io_cpu_memory_mmuBus_rsp_allowRead(DBusCachedPlugin_mmuBus_rsp_allowRead),
    .io_cpu_memory_mmuBus_rsp_allowWrite(DBusCachedPlugin_mmuBus_rsp_allowWrite),
    .io_cpu_memory_mmuBus_rsp_allowExecute(DBusCachedPlugin_mmuBus_rsp_allowExecute),
    .io_cpu_memory_mmuBus_rsp_exception(DBusCachedPlugin_mmuBus_rsp_exception),
    .io_cpu_memory_mmuBus_rsp_refilling(DBusCachedPlugin_mmuBus_rsp_refilling),
    .io_cpu_memory_mmuBus_end(dataCache_1__io_cpu_memory_mmuBus_end),
    .io_cpu_memory_mmuBus_busy(DBusCachedPlugin_mmuBus_busy),
    .io_cpu_writeBack_isValid(_zz_239_),
    .io_cpu_writeBack_isStuck(writeBack_arbitration_isStuck),
    .io_cpu_writeBack_isUser(_zz_240_),
    .io_cpu_writeBack_haltIt(dataCache_1__io_cpu_writeBack_haltIt),
    .io_cpu_writeBack_isWrite(dataCache_1__io_cpu_writeBack_isWrite),
    .io_cpu_writeBack_data(dataCache_1__io_cpu_writeBack_data),
    .io_cpu_writeBack_address(_zz_241_),
    .io_cpu_writeBack_mmuException(dataCache_1__io_cpu_writeBack_mmuException),
    .io_cpu_writeBack_unalignedAccess(dataCache_1__io_cpu_writeBack_unalignedAccess),
    .io_cpu_writeBack_accessError(dataCache_1__io_cpu_writeBack_accessError),
    .io_cpu_redo(dataCache_1__io_cpu_redo),
    .io_cpu_flush_valid(_zz_242_),
    .io_cpu_flush_ready(dataCache_1__io_cpu_flush_ready),
    .io_mem_cmd_valid(dataCache_1__io_mem_cmd_valid),
    .io_mem_cmd_ready(dBus_cmd_ready),
    .io_mem_cmd_payload_wr(dataCache_1__io_mem_cmd_payload_wr),
    .io_mem_cmd_payload_address(dataCache_1__io_mem_cmd_payload_address),
    .io_mem_cmd_payload_data(dataCache_1__io_mem_cmd_payload_data),
    .io_mem_cmd_payload_mask(dataCache_1__io_mem_cmd_payload_mask),
    .io_mem_cmd_payload_length(dataCache_1__io_mem_cmd_payload_length),
    .io_mem_cmd_payload_last(dataCache_1__io_mem_cmd_payload_last),
    .io_mem_rsp_valid(dBus_rsp_valid),
    .io_mem_rsp_payload_data(dBus_rsp_payload_data),
    .io_mem_rsp_payload_error(dBus_rsp_payload_error),
    .clk(clk),
    .reset(reset) 
  );
  always @(*) begin
    case(_zz_445_)
      3'b000 : begin
        _zz_246_ = DBusCachedPlugin_redoBranch_payload;
      end
      3'b001 : begin
        _zz_246_ = CsrPlugin_jumpInterface_payload;
      end
      3'b010 : begin
        _zz_246_ = BranchPlugin_jumpInterface_payload;
      end
      3'b011 : begin
        _zz_246_ = IBusCachedPlugin_redoBranch_payload;
      end
      default : begin
        _zz_246_ = IBusCachedPlugin_pcs_4;
      end
    endcase
  end

  always @(*) begin
    case(_zz_156_)
      3'b000 : begin
        _zz_247_ = MmuPlugin_ports_0_cache_0_valid;
        _zz_248_ = MmuPlugin_ports_0_cache_0_exception;
        _zz_249_ = MmuPlugin_ports_0_cache_0_superPage;
        _zz_250_ = MmuPlugin_ports_0_cache_0_virtualAddress_0;
        _zz_251_ = MmuPlugin_ports_0_cache_0_virtualAddress_1;
        _zz_252_ = MmuPlugin_ports_0_cache_0_physicalAddress_0;
        _zz_253_ = MmuPlugin_ports_0_cache_0_physicalAddress_1;
        _zz_254_ = MmuPlugin_ports_0_cache_0_allowRead;
        _zz_255_ = MmuPlugin_ports_0_cache_0_allowWrite;
        _zz_256_ = MmuPlugin_ports_0_cache_0_allowExecute;
        _zz_257_ = MmuPlugin_ports_0_cache_0_allowUser;
      end
      3'b001 : begin
        _zz_247_ = MmuPlugin_ports_0_cache_1_valid;
        _zz_248_ = MmuPlugin_ports_0_cache_1_exception;
        _zz_249_ = MmuPlugin_ports_0_cache_1_superPage;
        _zz_250_ = MmuPlugin_ports_0_cache_1_virtualAddress_0;
        _zz_251_ = MmuPlugin_ports_0_cache_1_virtualAddress_1;
        _zz_252_ = MmuPlugin_ports_0_cache_1_physicalAddress_0;
        _zz_253_ = MmuPlugin_ports_0_cache_1_physicalAddress_1;
        _zz_254_ = MmuPlugin_ports_0_cache_1_allowRead;
        _zz_255_ = MmuPlugin_ports_0_cache_1_allowWrite;
        _zz_256_ = MmuPlugin_ports_0_cache_1_allowExecute;
        _zz_257_ = MmuPlugin_ports_0_cache_1_allowUser;
      end
      3'b010 : begin
        _zz_247_ = MmuPlugin_ports_0_cache_2_valid;
        _zz_248_ = MmuPlugin_ports_0_cache_2_exception;
        _zz_249_ = MmuPlugin_ports_0_cache_2_superPage;
        _zz_250_ = MmuPlugin_ports_0_cache_2_virtualAddress_0;
        _zz_251_ = MmuPlugin_ports_0_cache_2_virtualAddress_1;
        _zz_252_ = MmuPlugin_ports_0_cache_2_physicalAddress_0;
        _zz_253_ = MmuPlugin_ports_0_cache_2_physicalAddress_1;
        _zz_254_ = MmuPlugin_ports_0_cache_2_allowRead;
        _zz_255_ = MmuPlugin_ports_0_cache_2_allowWrite;
        _zz_256_ = MmuPlugin_ports_0_cache_2_allowExecute;
        _zz_257_ = MmuPlugin_ports_0_cache_2_allowUser;
      end
      3'b011 : begin
        _zz_247_ = MmuPlugin_ports_0_cache_3_valid;
        _zz_248_ = MmuPlugin_ports_0_cache_3_exception;
        _zz_249_ = MmuPlugin_ports_0_cache_3_superPage;
        _zz_250_ = MmuPlugin_ports_0_cache_3_virtualAddress_0;
        _zz_251_ = MmuPlugin_ports_0_cache_3_virtualAddress_1;
        _zz_252_ = MmuPlugin_ports_0_cache_3_physicalAddress_0;
        _zz_253_ = MmuPlugin_ports_0_cache_3_physicalAddress_1;
        _zz_254_ = MmuPlugin_ports_0_cache_3_allowRead;
        _zz_255_ = MmuPlugin_ports_0_cache_3_allowWrite;
        _zz_256_ = MmuPlugin_ports_0_cache_3_allowExecute;
        _zz_257_ = MmuPlugin_ports_0_cache_3_allowUser;
      end
      3'b100 : begin
        _zz_247_ = MmuPlugin_ports_0_cache_4_valid;
        _zz_248_ = MmuPlugin_ports_0_cache_4_exception;
        _zz_249_ = MmuPlugin_ports_0_cache_4_superPage;
        _zz_250_ = MmuPlugin_ports_0_cache_4_virtualAddress_0;
        _zz_251_ = MmuPlugin_ports_0_cache_4_virtualAddress_1;
        _zz_252_ = MmuPlugin_ports_0_cache_4_physicalAddress_0;
        _zz_253_ = MmuPlugin_ports_0_cache_4_physicalAddress_1;
        _zz_254_ = MmuPlugin_ports_0_cache_4_allowRead;
        _zz_255_ = MmuPlugin_ports_0_cache_4_allowWrite;
        _zz_256_ = MmuPlugin_ports_0_cache_4_allowExecute;
        _zz_257_ = MmuPlugin_ports_0_cache_4_allowUser;
      end
      default : begin
        _zz_247_ = MmuPlugin_ports_0_cache_5_valid;
        _zz_248_ = MmuPlugin_ports_0_cache_5_exception;
        _zz_249_ = MmuPlugin_ports_0_cache_5_superPage;
        _zz_250_ = MmuPlugin_ports_0_cache_5_virtualAddress_0;
        _zz_251_ = MmuPlugin_ports_0_cache_5_virtualAddress_1;
        _zz_252_ = MmuPlugin_ports_0_cache_5_physicalAddress_0;
        _zz_253_ = MmuPlugin_ports_0_cache_5_physicalAddress_1;
        _zz_254_ = MmuPlugin_ports_0_cache_5_allowRead;
        _zz_255_ = MmuPlugin_ports_0_cache_5_allowWrite;
        _zz_256_ = MmuPlugin_ports_0_cache_5_allowExecute;
        _zz_257_ = MmuPlugin_ports_0_cache_5_allowUser;
      end
    endcase
  end

  always @(*) begin
    case(_zz_159_)
      2'b00 : begin
        _zz_258_ = MmuPlugin_ports_1_cache_0_valid;
        _zz_259_ = MmuPlugin_ports_1_cache_0_exception;
        _zz_260_ = MmuPlugin_ports_1_cache_0_superPage;
        _zz_261_ = MmuPlugin_ports_1_cache_0_virtualAddress_0;
        _zz_262_ = MmuPlugin_ports_1_cache_0_virtualAddress_1;
        _zz_263_ = MmuPlugin_ports_1_cache_0_physicalAddress_0;
        _zz_264_ = MmuPlugin_ports_1_cache_0_physicalAddress_1;
        _zz_265_ = MmuPlugin_ports_1_cache_0_allowRead;
        _zz_266_ = MmuPlugin_ports_1_cache_0_allowWrite;
        _zz_267_ = MmuPlugin_ports_1_cache_0_allowExecute;
        _zz_268_ = MmuPlugin_ports_1_cache_0_allowUser;
      end
      2'b01 : begin
        _zz_258_ = MmuPlugin_ports_1_cache_1_valid;
        _zz_259_ = MmuPlugin_ports_1_cache_1_exception;
        _zz_260_ = MmuPlugin_ports_1_cache_1_superPage;
        _zz_261_ = MmuPlugin_ports_1_cache_1_virtualAddress_0;
        _zz_262_ = MmuPlugin_ports_1_cache_1_virtualAddress_1;
        _zz_263_ = MmuPlugin_ports_1_cache_1_physicalAddress_0;
        _zz_264_ = MmuPlugin_ports_1_cache_1_physicalAddress_1;
        _zz_265_ = MmuPlugin_ports_1_cache_1_allowRead;
        _zz_266_ = MmuPlugin_ports_1_cache_1_allowWrite;
        _zz_267_ = MmuPlugin_ports_1_cache_1_allowExecute;
        _zz_268_ = MmuPlugin_ports_1_cache_1_allowUser;
      end
      2'b10 : begin
        _zz_258_ = MmuPlugin_ports_1_cache_2_valid;
        _zz_259_ = MmuPlugin_ports_1_cache_2_exception;
        _zz_260_ = MmuPlugin_ports_1_cache_2_superPage;
        _zz_261_ = MmuPlugin_ports_1_cache_2_virtualAddress_0;
        _zz_262_ = MmuPlugin_ports_1_cache_2_virtualAddress_1;
        _zz_263_ = MmuPlugin_ports_1_cache_2_physicalAddress_0;
        _zz_264_ = MmuPlugin_ports_1_cache_2_physicalAddress_1;
        _zz_265_ = MmuPlugin_ports_1_cache_2_allowRead;
        _zz_266_ = MmuPlugin_ports_1_cache_2_allowWrite;
        _zz_267_ = MmuPlugin_ports_1_cache_2_allowExecute;
        _zz_268_ = MmuPlugin_ports_1_cache_2_allowUser;
      end
      default : begin
        _zz_258_ = MmuPlugin_ports_1_cache_3_valid;
        _zz_259_ = MmuPlugin_ports_1_cache_3_exception;
        _zz_260_ = MmuPlugin_ports_1_cache_3_superPage;
        _zz_261_ = MmuPlugin_ports_1_cache_3_virtualAddress_0;
        _zz_262_ = MmuPlugin_ports_1_cache_3_virtualAddress_1;
        _zz_263_ = MmuPlugin_ports_1_cache_3_physicalAddress_0;
        _zz_264_ = MmuPlugin_ports_1_cache_3_physicalAddress_1;
        _zz_265_ = MmuPlugin_ports_1_cache_3_allowRead;
        _zz_266_ = MmuPlugin_ports_1_cache_3_allowWrite;
        _zz_267_ = MmuPlugin_ports_1_cache_3_allowExecute;
        _zz_268_ = MmuPlugin_ports_1_cache_3_allowUser;
      end
    endcase
  end

  `ifndef SYNTHESIS
  always @(*) begin
    case(_zz_1_)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : _zz_1__string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : _zz_1__string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : _zz_1__string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : _zz_1__string = "SRA_1    ";
      default : _zz_1__string = "?????????";
    endcase
  end
  always @(*) begin
    case(_zz_2_)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : _zz_2__string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : _zz_2__string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : _zz_2__string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : _zz_2__string = "SRA_1    ";
      default : _zz_2__string = "?????????";
    endcase
  end
  always @(*) begin
    case(decode_SHIFT_CTRL)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : decode_SHIFT_CTRL_string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : decode_SHIFT_CTRL_string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : decode_SHIFT_CTRL_string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : decode_SHIFT_CTRL_string = "SRA_1    ";
      default : decode_SHIFT_CTRL_string = "?????????";
    endcase
  end
  always @(*) begin
    case(_zz_3_)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : _zz_3__string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : _zz_3__string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : _zz_3__string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : _zz_3__string = "SRA_1    ";
      default : _zz_3__string = "?????????";
    endcase
  end
  always @(*) begin
    case(_zz_4_)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : _zz_4__string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : _zz_4__string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : _zz_4__string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : _zz_4__string = "SRA_1    ";
      default : _zz_4__string = "?????????";
    endcase
  end
  always @(*) begin
    case(_zz_5_)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : _zz_5__string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : _zz_5__string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : _zz_5__string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : _zz_5__string = "SRA_1    ";
      default : _zz_5__string = "?????????";
    endcase
  end
  always @(*) begin
    case(decode_ALU_BITWISE_CTRL)
      `AluBitwiseCtrlEnum_defaultEncoding_XOR_1 : decode_ALU_BITWISE_CTRL_string = "XOR_1";
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : decode_ALU_BITWISE_CTRL_string = "OR_1 ";
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : decode_ALU_BITWISE_CTRL_string = "AND_1";
      default : decode_ALU_BITWISE_CTRL_string = "?????";
    endcase
  end
  always @(*) begin
    case(_zz_6_)
      `AluBitwiseCtrlEnum_defaultEncoding_XOR_1 : _zz_6__string = "XOR_1";
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : _zz_6__string = "OR_1 ";
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : _zz_6__string = "AND_1";
      default : _zz_6__string = "?????";
    endcase
  end
  always @(*) begin
    case(_zz_7_)
      `AluBitwiseCtrlEnum_defaultEncoding_XOR_1 : _zz_7__string = "XOR_1";
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : _zz_7__string = "OR_1 ";
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : _zz_7__string = "AND_1";
      default : _zz_7__string = "?????";
    endcase
  end
  always @(*) begin
    case(_zz_8_)
      `AluBitwiseCtrlEnum_defaultEncoding_XOR_1 : _zz_8__string = "XOR_1";
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : _zz_8__string = "OR_1 ";
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : _zz_8__string = "AND_1";
      default : _zz_8__string = "?????";
    endcase
  end
  always @(*) begin
    case(decode_SRC1_CTRL)
      `Src1CtrlEnum_defaultEncoding_RS : decode_SRC1_CTRL_string = "RS          ";
      `Src1CtrlEnum_defaultEncoding_IMU : decode_SRC1_CTRL_string = "IMU         ";
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : decode_SRC1_CTRL_string = "PC_INCREMENT";
      `Src1CtrlEnum_defaultEncoding_URS1 : decode_SRC1_CTRL_string = "URS1        ";
      default : decode_SRC1_CTRL_string = "????????????";
    endcase
  end
  always @(*) begin
    case(_zz_9_)
      `Src1CtrlEnum_defaultEncoding_RS : _zz_9__string = "RS          ";
      `Src1CtrlEnum_defaultEncoding_IMU : _zz_9__string = "IMU         ";
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : _zz_9__string = "PC_INCREMENT";
      `Src1CtrlEnum_defaultEncoding_URS1 : _zz_9__string = "URS1        ";
      default : _zz_9__string = "????????????";
    endcase
  end
  always @(*) begin
    case(_zz_10_)
      `Src1CtrlEnum_defaultEncoding_RS : _zz_10__string = "RS          ";
      `Src1CtrlEnum_defaultEncoding_IMU : _zz_10__string = "IMU         ";
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : _zz_10__string = "PC_INCREMENT";
      `Src1CtrlEnum_defaultEncoding_URS1 : _zz_10__string = "URS1        ";
      default : _zz_10__string = "????????????";
    endcase
  end
  always @(*) begin
    case(_zz_11_)
      `Src1CtrlEnum_defaultEncoding_RS : _zz_11__string = "RS          ";
      `Src1CtrlEnum_defaultEncoding_IMU : _zz_11__string = "IMU         ";
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : _zz_11__string = "PC_INCREMENT";
      `Src1CtrlEnum_defaultEncoding_URS1 : _zz_11__string = "URS1        ";
      default : _zz_11__string = "????????????";
    endcase
  end
  always @(*) begin
    case(decode_SRC2_CTRL)
      `Src2CtrlEnum_defaultEncoding_RS : decode_SRC2_CTRL_string = "RS ";
      `Src2CtrlEnum_defaultEncoding_IMI : decode_SRC2_CTRL_string = "IMI";
      `Src2CtrlEnum_defaultEncoding_IMS : decode_SRC2_CTRL_string = "IMS";
      `Src2CtrlEnum_defaultEncoding_PC : decode_SRC2_CTRL_string = "PC ";
      default : decode_SRC2_CTRL_string = "???";
    endcase
  end
  always @(*) begin
    case(_zz_12_)
      `Src2CtrlEnum_defaultEncoding_RS : _zz_12__string = "RS ";
      `Src2CtrlEnum_defaultEncoding_IMI : _zz_12__string = "IMI";
      `Src2CtrlEnum_defaultEncoding_IMS : _zz_12__string = "IMS";
      `Src2CtrlEnum_defaultEncoding_PC : _zz_12__string = "PC ";
      default : _zz_12__string = "???";
    endcase
  end
  always @(*) begin
    case(_zz_13_)
      `Src2CtrlEnum_defaultEncoding_RS : _zz_13__string = "RS ";
      `Src2CtrlEnum_defaultEncoding_IMI : _zz_13__string = "IMI";
      `Src2CtrlEnum_defaultEncoding_IMS : _zz_13__string = "IMS";
      `Src2CtrlEnum_defaultEncoding_PC : _zz_13__string = "PC ";
      default : _zz_13__string = "???";
    endcase
  end
  always @(*) begin
    case(_zz_14_)
      `Src2CtrlEnum_defaultEncoding_RS : _zz_14__string = "RS ";
      `Src2CtrlEnum_defaultEncoding_IMI : _zz_14__string = "IMI";
      `Src2CtrlEnum_defaultEncoding_IMS : _zz_14__string = "IMS";
      `Src2CtrlEnum_defaultEncoding_PC : _zz_14__string = "PC ";
      default : _zz_14__string = "???";
    endcase
  end
  always @(*) begin
    case(decode_ALU_CTRL)
      `AluCtrlEnum_defaultEncoding_ADD_SUB : decode_ALU_CTRL_string = "ADD_SUB ";
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : decode_ALU_CTRL_string = "SLT_SLTU";
      `AluCtrlEnum_defaultEncoding_BITWISE : decode_ALU_CTRL_string = "BITWISE ";
      default : decode_ALU_CTRL_string = "????????";
    endcase
  end
  always @(*) begin
    case(_zz_15_)
      `AluCtrlEnum_defaultEncoding_ADD_SUB : _zz_15__string = "ADD_SUB ";
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : _zz_15__string = "SLT_SLTU";
      `AluCtrlEnum_defaultEncoding_BITWISE : _zz_15__string = "BITWISE ";
      default : _zz_15__string = "????????";
    endcase
  end
  always @(*) begin
    case(_zz_16_)
      `AluCtrlEnum_defaultEncoding_ADD_SUB : _zz_16__string = "ADD_SUB ";
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : _zz_16__string = "SLT_SLTU";
      `AluCtrlEnum_defaultEncoding_BITWISE : _zz_16__string = "BITWISE ";
      default : _zz_16__string = "????????";
    endcase
  end
  always @(*) begin
    case(_zz_17_)
      `AluCtrlEnum_defaultEncoding_ADD_SUB : _zz_17__string = "ADD_SUB ";
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : _zz_17__string = "SLT_SLTU";
      `AluCtrlEnum_defaultEncoding_BITWISE : _zz_17__string = "BITWISE ";
      default : _zz_17__string = "????????";
    endcase
  end
  always @(*) begin
    case(_zz_18_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_18__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_18__string = "XRET";
      default : _zz_18__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_19_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_19__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_19__string = "XRET";
      default : _zz_19__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_20_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_20__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_20__string = "XRET";
      default : _zz_20__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_21_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_21__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_21__string = "XRET";
      default : _zz_21__string = "????";
    endcase
  end
  always @(*) begin
    case(decode_ENV_CTRL)
      `EnvCtrlEnum_defaultEncoding_NONE : decode_ENV_CTRL_string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : decode_ENV_CTRL_string = "XRET";
      default : decode_ENV_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_22_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_22__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_22__string = "XRET";
      default : _zz_22__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_23_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_23__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_23__string = "XRET";
      default : _zz_23__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_24_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_24__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_24__string = "XRET";
      default : _zz_24__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_25_)
      `BranchCtrlEnum_defaultEncoding_INC : _zz_25__string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : _zz_25__string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : _zz_25__string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : _zz_25__string = "JALR";
      default : _zz_25__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_26_)
      `BranchCtrlEnum_defaultEncoding_INC : _zz_26__string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : _zz_26__string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : _zz_26__string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : _zz_26__string = "JALR";
      default : _zz_26__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_27_)
      `BranchCtrlEnum_defaultEncoding_INC : _zz_27__string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : _zz_27__string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : _zz_27__string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : _zz_27__string = "JALR";
      default : _zz_27__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_28_)
      `BranchCtrlEnum_defaultEncoding_INC : _zz_28__string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : _zz_28__string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : _zz_28__string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : _zz_28__string = "JALR";
      default : _zz_28__string = "????";
    endcase
  end
  always @(*) begin
    case(execute_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_INC : execute_BRANCH_CTRL_string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : execute_BRANCH_CTRL_string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : execute_BRANCH_CTRL_string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : execute_BRANCH_CTRL_string = "JALR";
      default : execute_BRANCH_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_31_)
      `BranchCtrlEnum_defaultEncoding_INC : _zz_31__string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : _zz_31__string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : _zz_31__string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : _zz_31__string = "JALR";
      default : _zz_31__string = "????";
    endcase
  end
  always @(*) begin
    case(memory_ENV_CTRL)
      `EnvCtrlEnum_defaultEncoding_NONE : memory_ENV_CTRL_string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : memory_ENV_CTRL_string = "XRET";
      default : memory_ENV_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_35_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_35__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_35__string = "XRET";
      default : _zz_35__string = "????";
    endcase
  end
  always @(*) begin
    case(execute_ENV_CTRL)
      `EnvCtrlEnum_defaultEncoding_NONE : execute_ENV_CTRL_string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : execute_ENV_CTRL_string = "XRET";
      default : execute_ENV_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_36_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_36__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_36__string = "XRET";
      default : _zz_36__string = "????";
    endcase
  end
  always @(*) begin
    case(writeBack_ENV_CTRL)
      `EnvCtrlEnum_defaultEncoding_NONE : writeBack_ENV_CTRL_string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : writeBack_ENV_CTRL_string = "XRET";
      default : writeBack_ENV_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_39_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_39__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_39__string = "XRET";
      default : _zz_39__string = "????";
    endcase
  end
  always @(*) begin
    case(memory_SHIFT_CTRL)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : memory_SHIFT_CTRL_string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : memory_SHIFT_CTRL_string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : memory_SHIFT_CTRL_string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : memory_SHIFT_CTRL_string = "SRA_1    ";
      default : memory_SHIFT_CTRL_string = "?????????";
    endcase
  end
  always @(*) begin
    case(_zz_47_)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : _zz_47__string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : _zz_47__string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : _zz_47__string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : _zz_47__string = "SRA_1    ";
      default : _zz_47__string = "?????????";
    endcase
  end
  always @(*) begin
    case(execute_SHIFT_CTRL)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : execute_SHIFT_CTRL_string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : execute_SHIFT_CTRL_string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : execute_SHIFT_CTRL_string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : execute_SHIFT_CTRL_string = "SRA_1    ";
      default : execute_SHIFT_CTRL_string = "?????????";
    endcase
  end
  always @(*) begin
    case(_zz_49_)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : _zz_49__string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : _zz_49__string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : _zz_49__string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : _zz_49__string = "SRA_1    ";
      default : _zz_49__string = "?????????";
    endcase
  end
  always @(*) begin
    case(execute_SRC2_CTRL)
      `Src2CtrlEnum_defaultEncoding_RS : execute_SRC2_CTRL_string = "RS ";
      `Src2CtrlEnum_defaultEncoding_IMI : execute_SRC2_CTRL_string = "IMI";
      `Src2CtrlEnum_defaultEncoding_IMS : execute_SRC2_CTRL_string = "IMS";
      `Src2CtrlEnum_defaultEncoding_PC : execute_SRC2_CTRL_string = "PC ";
      default : execute_SRC2_CTRL_string = "???";
    endcase
  end
  always @(*) begin
    case(_zz_54_)
      `Src2CtrlEnum_defaultEncoding_RS : _zz_54__string = "RS ";
      `Src2CtrlEnum_defaultEncoding_IMI : _zz_54__string = "IMI";
      `Src2CtrlEnum_defaultEncoding_IMS : _zz_54__string = "IMS";
      `Src2CtrlEnum_defaultEncoding_PC : _zz_54__string = "PC ";
      default : _zz_54__string = "???";
    endcase
  end
  always @(*) begin
    case(execute_SRC1_CTRL)
      `Src1CtrlEnum_defaultEncoding_RS : execute_SRC1_CTRL_string = "RS          ";
      `Src1CtrlEnum_defaultEncoding_IMU : execute_SRC1_CTRL_string = "IMU         ";
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : execute_SRC1_CTRL_string = "PC_INCREMENT";
      `Src1CtrlEnum_defaultEncoding_URS1 : execute_SRC1_CTRL_string = "URS1        ";
      default : execute_SRC1_CTRL_string = "????????????";
    endcase
  end
  always @(*) begin
    case(_zz_56_)
      `Src1CtrlEnum_defaultEncoding_RS : _zz_56__string = "RS          ";
      `Src1CtrlEnum_defaultEncoding_IMU : _zz_56__string = "IMU         ";
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : _zz_56__string = "PC_INCREMENT";
      `Src1CtrlEnum_defaultEncoding_URS1 : _zz_56__string = "URS1        ";
      default : _zz_56__string = "????????????";
    endcase
  end
  always @(*) begin
    case(execute_ALU_CTRL)
      `AluCtrlEnum_defaultEncoding_ADD_SUB : execute_ALU_CTRL_string = "ADD_SUB ";
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : execute_ALU_CTRL_string = "SLT_SLTU";
      `AluCtrlEnum_defaultEncoding_BITWISE : execute_ALU_CTRL_string = "BITWISE ";
      default : execute_ALU_CTRL_string = "????????";
    endcase
  end
  always @(*) begin
    case(_zz_59_)
      `AluCtrlEnum_defaultEncoding_ADD_SUB : _zz_59__string = "ADD_SUB ";
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : _zz_59__string = "SLT_SLTU";
      `AluCtrlEnum_defaultEncoding_BITWISE : _zz_59__string = "BITWISE ";
      default : _zz_59__string = "????????";
    endcase
  end
  always @(*) begin
    case(execute_ALU_BITWISE_CTRL)
      `AluBitwiseCtrlEnum_defaultEncoding_XOR_1 : execute_ALU_BITWISE_CTRL_string = "XOR_1";
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : execute_ALU_BITWISE_CTRL_string = "OR_1 ";
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : execute_ALU_BITWISE_CTRL_string = "AND_1";
      default : execute_ALU_BITWISE_CTRL_string = "?????";
    endcase
  end
  always @(*) begin
    case(_zz_61_)
      `AluBitwiseCtrlEnum_defaultEncoding_XOR_1 : _zz_61__string = "XOR_1";
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : _zz_61__string = "OR_1 ";
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : _zz_61__string = "AND_1";
      default : _zz_61__string = "?????";
    endcase
  end
  always @(*) begin
    case(_zz_68_)
      `Src1CtrlEnum_defaultEncoding_RS : _zz_68__string = "RS          ";
      `Src1CtrlEnum_defaultEncoding_IMU : _zz_68__string = "IMU         ";
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : _zz_68__string = "PC_INCREMENT";
      `Src1CtrlEnum_defaultEncoding_URS1 : _zz_68__string = "URS1        ";
      default : _zz_68__string = "????????????";
    endcase
  end
  always @(*) begin
    case(_zz_75_)
      `BranchCtrlEnum_defaultEncoding_INC : _zz_75__string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : _zz_75__string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : _zz_75__string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : _zz_75__string = "JALR";
      default : _zz_75__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_78_)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : _zz_78__string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : _zz_78__string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : _zz_78__string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : _zz_78__string = "SRA_1    ";
      default : _zz_78__string = "?????????";
    endcase
  end
  always @(*) begin
    case(_zz_84_)
      `AluCtrlEnum_defaultEncoding_ADD_SUB : _zz_84__string = "ADD_SUB ";
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : _zz_84__string = "SLT_SLTU";
      `AluCtrlEnum_defaultEncoding_BITWISE : _zz_84__string = "BITWISE ";
      default : _zz_84__string = "????????";
    endcase
  end
  always @(*) begin
    case(_zz_87_)
      `AluBitwiseCtrlEnum_defaultEncoding_XOR_1 : _zz_87__string = "XOR_1";
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : _zz_87__string = "OR_1 ";
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : _zz_87__string = "AND_1";
      default : _zz_87__string = "?????";
    endcase
  end
  always @(*) begin
    case(_zz_90_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_90__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_90__string = "XRET";
      default : _zz_90__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_91_)
      `Src2CtrlEnum_defaultEncoding_RS : _zz_91__string = "RS ";
      `Src2CtrlEnum_defaultEncoding_IMI : _zz_91__string = "IMI";
      `Src2CtrlEnum_defaultEncoding_IMS : _zz_91__string = "IMS";
      `Src2CtrlEnum_defaultEncoding_PC : _zz_91__string = "PC ";
      default : _zz_91__string = "???";
    endcase
  end
  always @(*) begin
    case(decode_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_INC : decode_BRANCH_CTRL_string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : decode_BRANCH_CTRL_string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : decode_BRANCH_CTRL_string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : decode_BRANCH_CTRL_string = "JALR";
      default : decode_BRANCH_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_101_)
      `BranchCtrlEnum_defaultEncoding_INC : _zz_101__string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : _zz_101__string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : _zz_101__string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : _zz_101__string = "JALR";
      default : _zz_101__string = "????";
    endcase
  end
  always @(*) begin
    case(memory_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_INC : memory_BRANCH_CTRL_string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : memory_BRANCH_CTRL_string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : memory_BRANCH_CTRL_string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : memory_BRANCH_CTRL_string = "JALR";
      default : memory_BRANCH_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_102_)
      `BranchCtrlEnum_defaultEncoding_INC : _zz_102__string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : _zz_102__string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : _zz_102__string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : _zz_102__string = "JALR";
      default : _zz_102__string = "????";
    endcase
  end
  always @(*) begin
    case(MmuPlugin_shared_state_1_)
      `MmuPlugin_shared_State_defaultEncoding_IDLE : MmuPlugin_shared_state_1__string = "IDLE  ";
      `MmuPlugin_shared_State_defaultEncoding_L1_CMD : MmuPlugin_shared_state_1__string = "L1_CMD";
      `MmuPlugin_shared_State_defaultEncoding_L1_RSP : MmuPlugin_shared_state_1__string = "L1_RSP";
      `MmuPlugin_shared_State_defaultEncoding_L0_CMD : MmuPlugin_shared_state_1__string = "L0_CMD";
      `MmuPlugin_shared_State_defaultEncoding_L0_RSP : MmuPlugin_shared_state_1__string = "L0_RSP";
      default : MmuPlugin_shared_state_1__string = "??????";
    endcase
  end
  always @(*) begin
    case(_zz_165_)
      `Src2CtrlEnum_defaultEncoding_RS : _zz_165__string = "RS ";
      `Src2CtrlEnum_defaultEncoding_IMI : _zz_165__string = "IMI";
      `Src2CtrlEnum_defaultEncoding_IMS : _zz_165__string = "IMS";
      `Src2CtrlEnum_defaultEncoding_PC : _zz_165__string = "PC ";
      default : _zz_165__string = "???";
    endcase
  end
  always @(*) begin
    case(_zz_166_)
      `EnvCtrlEnum_defaultEncoding_NONE : _zz_166__string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : _zz_166__string = "XRET";
      default : _zz_166__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_167_)
      `AluBitwiseCtrlEnum_defaultEncoding_XOR_1 : _zz_167__string = "XOR_1";
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : _zz_167__string = "OR_1 ";
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : _zz_167__string = "AND_1";
      default : _zz_167__string = "?????";
    endcase
  end
  always @(*) begin
    case(_zz_168_)
      `AluCtrlEnum_defaultEncoding_ADD_SUB : _zz_168__string = "ADD_SUB ";
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : _zz_168__string = "SLT_SLTU";
      `AluCtrlEnum_defaultEncoding_BITWISE : _zz_168__string = "BITWISE ";
      default : _zz_168__string = "????????";
    endcase
  end
  always @(*) begin
    case(_zz_169_)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : _zz_169__string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : _zz_169__string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : _zz_169__string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : _zz_169__string = "SRA_1    ";
      default : _zz_169__string = "?????????";
    endcase
  end
  always @(*) begin
    case(_zz_170_)
      `BranchCtrlEnum_defaultEncoding_INC : _zz_170__string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : _zz_170__string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : _zz_170__string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : _zz_170__string = "JALR";
      default : _zz_170__string = "????";
    endcase
  end
  always @(*) begin
    case(_zz_171_)
      `Src1CtrlEnum_defaultEncoding_RS : _zz_171__string = "RS          ";
      `Src1CtrlEnum_defaultEncoding_IMU : _zz_171__string = "IMU         ";
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : _zz_171__string = "PC_INCREMENT";
      `Src1CtrlEnum_defaultEncoding_URS1 : _zz_171__string = "URS1        ";
      default : _zz_171__string = "????????????";
    endcase
  end
  always @(*) begin
    case(decode_to_execute_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_INC : decode_to_execute_BRANCH_CTRL_string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : decode_to_execute_BRANCH_CTRL_string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : decode_to_execute_BRANCH_CTRL_string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : decode_to_execute_BRANCH_CTRL_string = "JALR";
      default : decode_to_execute_BRANCH_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(execute_to_memory_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_INC : execute_to_memory_BRANCH_CTRL_string = "INC ";
      `BranchCtrlEnum_defaultEncoding_B : execute_to_memory_BRANCH_CTRL_string = "B   ";
      `BranchCtrlEnum_defaultEncoding_JAL : execute_to_memory_BRANCH_CTRL_string = "JAL ";
      `BranchCtrlEnum_defaultEncoding_JALR : execute_to_memory_BRANCH_CTRL_string = "JALR";
      default : execute_to_memory_BRANCH_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(decode_to_execute_ENV_CTRL)
      `EnvCtrlEnum_defaultEncoding_NONE : decode_to_execute_ENV_CTRL_string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : decode_to_execute_ENV_CTRL_string = "XRET";
      default : decode_to_execute_ENV_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(execute_to_memory_ENV_CTRL)
      `EnvCtrlEnum_defaultEncoding_NONE : execute_to_memory_ENV_CTRL_string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : execute_to_memory_ENV_CTRL_string = "XRET";
      default : execute_to_memory_ENV_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(memory_to_writeBack_ENV_CTRL)
      `EnvCtrlEnum_defaultEncoding_NONE : memory_to_writeBack_ENV_CTRL_string = "NONE";
      `EnvCtrlEnum_defaultEncoding_XRET : memory_to_writeBack_ENV_CTRL_string = "XRET";
      default : memory_to_writeBack_ENV_CTRL_string = "????";
    endcase
  end
  always @(*) begin
    case(decode_to_execute_ALU_CTRL)
      `AluCtrlEnum_defaultEncoding_ADD_SUB : decode_to_execute_ALU_CTRL_string = "ADD_SUB ";
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : decode_to_execute_ALU_CTRL_string = "SLT_SLTU";
      `AluCtrlEnum_defaultEncoding_BITWISE : decode_to_execute_ALU_CTRL_string = "BITWISE ";
      default : decode_to_execute_ALU_CTRL_string = "????????";
    endcase
  end
  always @(*) begin
    case(decode_to_execute_SRC2_CTRL)
      `Src2CtrlEnum_defaultEncoding_RS : decode_to_execute_SRC2_CTRL_string = "RS ";
      `Src2CtrlEnum_defaultEncoding_IMI : decode_to_execute_SRC2_CTRL_string = "IMI";
      `Src2CtrlEnum_defaultEncoding_IMS : decode_to_execute_SRC2_CTRL_string = "IMS";
      `Src2CtrlEnum_defaultEncoding_PC : decode_to_execute_SRC2_CTRL_string = "PC ";
      default : decode_to_execute_SRC2_CTRL_string = "???";
    endcase
  end
  always @(*) begin
    case(decode_to_execute_SRC1_CTRL)
      `Src1CtrlEnum_defaultEncoding_RS : decode_to_execute_SRC1_CTRL_string = "RS          ";
      `Src1CtrlEnum_defaultEncoding_IMU : decode_to_execute_SRC1_CTRL_string = "IMU         ";
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : decode_to_execute_SRC1_CTRL_string = "PC_INCREMENT";
      `Src1CtrlEnum_defaultEncoding_URS1 : decode_to_execute_SRC1_CTRL_string = "URS1        ";
      default : decode_to_execute_SRC1_CTRL_string = "????????????";
    endcase
  end
  always @(*) begin
    case(decode_to_execute_ALU_BITWISE_CTRL)
      `AluBitwiseCtrlEnum_defaultEncoding_XOR_1 : decode_to_execute_ALU_BITWISE_CTRL_string = "XOR_1";
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : decode_to_execute_ALU_BITWISE_CTRL_string = "OR_1 ";
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : decode_to_execute_ALU_BITWISE_CTRL_string = "AND_1";
      default : decode_to_execute_ALU_BITWISE_CTRL_string = "?????";
    endcase
  end
  always @(*) begin
    case(decode_to_execute_SHIFT_CTRL)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : decode_to_execute_SHIFT_CTRL_string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : decode_to_execute_SHIFT_CTRL_string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : decode_to_execute_SHIFT_CTRL_string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : decode_to_execute_SHIFT_CTRL_string = "SRA_1    ";
      default : decode_to_execute_SHIFT_CTRL_string = "?????????";
    endcase
  end
  always @(*) begin
    case(execute_to_memory_SHIFT_CTRL)
      `ShiftCtrlEnum_defaultEncoding_DISABLE_1 : execute_to_memory_SHIFT_CTRL_string = "DISABLE_1";
      `ShiftCtrlEnum_defaultEncoding_SLL_1 : execute_to_memory_SHIFT_CTRL_string = "SLL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRL_1 : execute_to_memory_SHIFT_CTRL_string = "SRL_1    ";
      `ShiftCtrlEnum_defaultEncoding_SRA_1 : execute_to_memory_SHIFT_CTRL_string = "SRA_1    ";
      default : execute_to_memory_SHIFT_CTRL_string = "?????????";
    endcase
  end
  `endif

  assign _zz_1_ = _zz_2_;
  assign decode_SHIFT_CTRL = _zz_3_;
  assign _zz_4_ = _zz_5_;
  assign decode_SRC_LESS_UNSIGNED = _zz_73_;
  assign decode_IS_CSR = _zz_82_;
  assign decode_BYPASSABLE_EXECUTE_STAGE = _zz_86_;
  assign decode_SRC2_FORCE_ZERO = _zz_58_;
  assign memory_MEMORY_WR = execute_to_memory_MEMORY_WR;
  assign decode_MEMORY_WR = _zz_67_;
  assign decode_ALU_BITWISE_CTRL = _zz_6_;
  assign _zz_7_ = _zz_8_;
  assign decode_IS_RS2_SIGNED = _zz_89_;
  assign decode_SRC1_CTRL = _zz_9_;
  assign _zz_10_ = _zz_11_;
  assign memory_MUL_HH = execute_to_memory_MUL_HH;
  assign execute_MUL_HH = _zz_41_;
  assign decode_IS_RS1_SIGNED = _zz_76_;
  assign decode_SRC2_CTRL = _zz_12_;
  assign _zz_13_ = _zz_14_;
  assign decode_IS_DIV = _zz_80_;
  assign writeBack_FORMAL_PC_NEXT = memory_to_writeBack_FORMAL_PC_NEXT;
  assign memory_FORMAL_PC_NEXT = execute_to_memory_FORMAL_PC_NEXT;
  assign execute_FORMAL_PC_NEXT = decode_to_execute_FORMAL_PC_NEXT;
  assign decode_FORMAL_PC_NEXT = _zz_108_;
  assign decode_CSR_READ_OPCODE = _zz_37_;
  assign decode_ALU_CTRL = _zz_15_;
  assign _zz_16_ = _zz_17_;
  assign execute_IS_DBUS_SHARING = _zz_94_;
  assign execute_REGFILE_WRITE_DATA = _zz_60_;
  assign memory_MEMORY_ADDRESS_LOW = execute_to_memory_MEMORY_ADDRESS_LOW;
  assign execute_MEMORY_ADDRESS_LOW = _zz_96_;
  assign decode_PREDICTION_HAD_BRANCHED2 = _zz_33_;
  assign execute_BRANCH_CALC = _zz_29_;
  assign execute_MUL_LL = _zz_44_;
  assign decode_DO_EBREAK = _zz_34_;
  assign execute_PREDICTION_CONTEXT_hazard = decode_to_execute_PREDICTION_CONTEXT_hazard;
  assign execute_PREDICTION_CONTEXT_line_history = decode_to_execute_PREDICTION_CONTEXT_line_history;
  assign decode_CSR_WRITE_OPCODE = _zz_38_;
  assign _zz_18_ = _zz_19_;
  assign _zz_20_ = _zz_21_;
  assign decode_ENV_CTRL = _zz_22_;
  assign _zz_23_ = _zz_24_;
  assign execute_BRANCH_DO = _zz_30_;
  assign memory_MUL_LOW = _zz_40_;
  assign _zz_25_ = _zz_26_;
  assign _zz_27_ = _zz_28_;
  assign execute_BYPASSABLE_MEMORY_STAGE = decode_to_execute_BYPASSABLE_MEMORY_STAGE;
  assign decode_BYPASSABLE_MEMORY_STAGE = _zz_72_;
  assign memory_IS_MUL = execute_to_memory_IS_MUL;
  assign execute_IS_MUL = decode_to_execute_IS_MUL;
  assign decode_IS_MUL = _zz_74_;
  assign execute_SHIFT_RIGHT = _zz_48_;
  assign execute_MUL_LH = _zz_43_;
  assign execute_MUL_HL = _zz_42_;
  assign decode_MEMORY_MANAGMENT = _zz_92_;
  assign memory_IS_SFENCE_VMA = execute_to_memory_IS_SFENCE_VMA;
  assign execute_IS_SFENCE_VMA = decode_to_execute_IS_SFENCE_VMA;
  assign decode_IS_SFENCE_VMA = _zz_79_;
  assign memory_BRANCH_CALC = execute_to_memory_BRANCH_CALC;
  assign memory_BRANCH_DO = execute_to_memory_BRANCH_DO;
  assign execute_PREDICTION_HAD_BRANCHED2 = decode_to_execute_PREDICTION_HAD_BRANCHED2;
  assign execute_BRANCH_COND_RESULT = _zz_32_;
  assign execute_BRANCH_CTRL = _zz_31_;
  assign execute_PC = decode_to_execute_PC;
  assign execute_DO_EBREAK = decode_to_execute_DO_EBREAK;
  assign decode_IS_EBREAK = _zz_77_;
  assign execute_CSR_READ_OPCODE = decode_to_execute_CSR_READ_OPCODE;
  assign execute_CSR_WRITE_OPCODE = decode_to_execute_CSR_WRITE_OPCODE;
  assign execute_IS_CSR = decode_to_execute_IS_CSR;
  assign memory_ENV_CTRL = _zz_35_;
  assign execute_ENV_CTRL = _zz_36_;
  assign writeBack_ENV_CTRL = _zz_39_;
  assign execute_IS_RS1_SIGNED = decode_to_execute_IS_RS1_SIGNED;
  assign execute_RS1 = decode_to_execute_RS1;
  assign execute_IS_DIV = decode_to_execute_IS_DIV;
  assign execute_IS_RS2_SIGNED = decode_to_execute_IS_RS2_SIGNED;
  assign memory_IS_DIV = execute_to_memory_IS_DIV;
  assign writeBack_IS_MUL = memory_to_writeBack_IS_MUL;
  assign writeBack_MUL_HH = memory_to_writeBack_MUL_HH;
  assign writeBack_MUL_LOW = memory_to_writeBack_MUL_LOW;
  assign memory_MUL_HL = execute_to_memory_MUL_HL;
  assign memory_MUL_LH = execute_to_memory_MUL_LH;
  assign memory_MUL_LL = execute_to_memory_MUL_LL;
  assign decode_RS2_USE = _zz_88_;
  assign decode_RS1_USE = _zz_69_;
  always @ (*) begin
    _zz_45_ = execute_REGFILE_WRITE_DATA;
    if(_zz_269_)begin
      _zz_45_ = execute_CsrPlugin_readData;
    end
    if(DBusCachedPlugin_forceDatapath)begin
      _zz_45_ = MmuPlugin_dBusAccess_cmd_payload_address;
    end
  end

  assign execute_REGFILE_WRITE_VALID = decode_to_execute_REGFILE_WRITE_VALID;
  assign execute_BYPASSABLE_EXECUTE_STAGE = decode_to_execute_BYPASSABLE_EXECUTE_STAGE;
  assign memory_REGFILE_WRITE_VALID = execute_to_memory_REGFILE_WRITE_VALID;
  assign memory_INSTRUCTION = execute_to_memory_INSTRUCTION;
  assign memory_BYPASSABLE_MEMORY_STAGE = execute_to_memory_BYPASSABLE_MEMORY_STAGE;
  assign writeBack_REGFILE_WRITE_VALID = memory_to_writeBack_REGFILE_WRITE_VALID;
  always @ (*) begin
    decode_RS2 = _zz_65_;
    if(_zz_185_)begin
      if((_zz_186_ == decode_INSTRUCTION[24 : 20]))begin
        decode_RS2 = _zz_187_;
      end
    end
    if(_zz_270_)begin
      if(_zz_271_)begin
        if(_zz_189_)begin
          decode_RS2 = _zz_95_;
        end
      end
    end
    if(_zz_272_)begin
      if(memory_BYPASSABLE_MEMORY_STAGE)begin
        if(_zz_191_)begin
          decode_RS2 = _zz_46_;
        end
      end
    end
    if(_zz_273_)begin
      if(execute_BYPASSABLE_EXECUTE_STAGE)begin
        if(_zz_193_)begin
          decode_RS2 = _zz_45_;
        end
      end
    end
  end

  always @ (*) begin
    decode_RS1 = _zz_66_;
    if(_zz_185_)begin
      if((_zz_186_ == decode_INSTRUCTION[19 : 15]))begin
        decode_RS1 = _zz_187_;
      end
    end
    if(_zz_270_)begin
      if(_zz_271_)begin
        if(_zz_188_)begin
          decode_RS1 = _zz_95_;
        end
      end
    end
    if(_zz_272_)begin
      if(memory_BYPASSABLE_MEMORY_STAGE)begin
        if(_zz_190_)begin
          decode_RS1 = _zz_46_;
        end
      end
    end
    if(_zz_273_)begin
      if(execute_BYPASSABLE_EXECUTE_STAGE)begin
        if(_zz_192_)begin
          decode_RS1 = _zz_45_;
        end
      end
    end
  end

  assign memory_SHIFT_RIGHT = execute_to_memory_SHIFT_RIGHT;
  always @ (*) begin
    _zz_46_ = memory_REGFILE_WRITE_DATA;
    if(memory_arbitration_isValid)begin
      case(memory_SHIFT_CTRL)
        `ShiftCtrlEnum_defaultEncoding_SLL_1 : begin
          _zz_46_ = _zz_181_;
        end
        `ShiftCtrlEnum_defaultEncoding_SRL_1, `ShiftCtrlEnum_defaultEncoding_SRA_1 : begin
          _zz_46_ = memory_SHIFT_RIGHT;
        end
        default : begin
        end
      endcase
    end
    if(_zz_274_)begin
      _zz_46_ = memory_DivPlugin_div_result;
    end
  end

  assign memory_SHIFT_CTRL = _zz_47_;
  assign execute_SHIFT_CTRL = _zz_49_;
  assign execute_SRC_LESS_UNSIGNED = decode_to_execute_SRC_LESS_UNSIGNED;
  assign execute_SRC2_FORCE_ZERO = decode_to_execute_SRC2_FORCE_ZERO;
  assign execute_SRC_USE_SUB_LESS = decode_to_execute_SRC_USE_SUB_LESS;
  assign _zz_53_ = execute_PC;
  assign execute_SRC2_CTRL = _zz_54_;
  assign execute_SRC1_CTRL = _zz_56_;
  assign decode_SRC_USE_SUB_LESS = _zz_81_;
  assign decode_SRC_ADD_ZERO = _zz_85_;
  assign execute_SRC_ADD_SUB = _zz_52_;
  assign execute_SRC_LESS = _zz_50_;
  assign execute_ALU_CTRL = _zz_59_;
  assign execute_SRC2 = _zz_55_;
  assign execute_SRC1 = _zz_57_;
  assign execute_ALU_BITWISE_CTRL = _zz_61_;
  assign _zz_62_ = writeBack_INSTRUCTION;
  assign _zz_63_ = writeBack_REGFILE_WRITE_VALID;
  always @ (*) begin
    _zz_64_ = 1'b0;
    if(lastStageRegFileWrite_valid)begin
      _zz_64_ = 1'b1;
    end
  end

  assign decode_INSTRUCTION_ANTICIPATED = _zz_100_;
  always @ (*) begin
    decode_REGFILE_WRITE_VALID = _zz_71_;
    if((decode_INSTRUCTION[11 : 7] == (5'b00000)))begin
      decode_REGFILE_WRITE_VALID = 1'b0;
    end
  end

  assign decode_LEGAL_INSTRUCTION = _zz_93_;
  assign decode_INSTRUCTION_READY = 1'b1;
  assign writeBack_IS_SFENCE_VMA = memory_to_writeBack_IS_SFENCE_VMA;
  assign writeBack_IS_DBUS_SHARING = memory_to_writeBack_IS_DBUS_SHARING;
  assign memory_IS_DBUS_SHARING = execute_to_memory_IS_DBUS_SHARING;
  always @ (*) begin
    _zz_95_ = writeBack_REGFILE_WRITE_DATA;
    if((writeBack_arbitration_isValid && writeBack_MEMORY_ENABLE))begin
      _zz_95_ = writeBack_DBusCachedPlugin_rspFormated;
    end
    if((writeBack_arbitration_isValid && writeBack_IS_MUL))begin
      case(_zz_320_)
        2'b00 : begin
          _zz_95_ = _zz_400_;
        end
        default : begin
          _zz_95_ = _zz_401_;
        end
      endcase
    end
  end

  assign writeBack_MEMORY_ADDRESS_LOW = memory_to_writeBack_MEMORY_ADDRESS_LOW;
  assign writeBack_MEMORY_WR = memory_to_writeBack_MEMORY_WR;
  assign writeBack_REGFILE_WRITE_DATA = memory_to_writeBack_REGFILE_WRITE_DATA;
  assign writeBack_MEMORY_ENABLE = memory_to_writeBack_MEMORY_ENABLE;
  assign memory_REGFILE_WRITE_DATA = execute_to_memory_REGFILE_WRITE_DATA;
  assign memory_MEMORY_ENABLE = execute_to_memory_MEMORY_ENABLE;
  assign execute_MEMORY_MANAGMENT = decode_to_execute_MEMORY_MANAGMENT;
  assign execute_RS2 = decode_to_execute_RS2;
  assign execute_MEMORY_WR = decode_to_execute_MEMORY_WR;
  assign execute_SRC_ADD = _zz_51_;
  assign execute_MEMORY_ENABLE = decode_to_execute_MEMORY_ENABLE;
  assign execute_INSTRUCTION = decode_to_execute_INSTRUCTION;
  assign decode_MEMORY_ENABLE = _zz_83_;
  assign decode_FLUSH_ALL = _zz_70_;
  always @ (*) begin
    IBusCachedPlugin_rsp_issueDetected = _zz_97_;
    if(_zz_275_)begin
      IBusCachedPlugin_rsp_issueDetected = 1'b1;
    end
  end

  always @ (*) begin
    _zz_97_ = _zz_98_;
    if(_zz_276_)begin
      _zz_97_ = 1'b1;
    end
  end

  always @ (*) begin
    _zz_98_ = _zz_99_;
    if(_zz_277_)begin
      _zz_98_ = 1'b1;
    end
  end

  always @ (*) begin
    _zz_99_ = 1'b0;
    if(_zz_278_)begin
      _zz_99_ = 1'b1;
    end
  end

  assign decode_BRANCH_CTRL = _zz_101_;
  always @ (*) begin
    decode_INSTRUCTION = _zz_109_;
    if((_zz_220_ != (3'b000)))begin
      decode_INSTRUCTION = IBusCachedPlugin_injectionPort_payload_regNext;
    end
  end

  assign memory_BRANCH_CTRL = _zz_102_;
  assign memory_PC = execute_to_memory_PC;
  assign memory_PREDICTION_CONTEXT_hazard = execute_to_memory_PREDICTION_CONTEXT_hazard;
  assign memory_PREDICTION_CONTEXT_line_history = execute_to_memory_PREDICTION_CONTEXT_line_history;
  assign decode_PREDICTION_CONTEXT_hazard = _zz_103_;
  assign decode_PREDICTION_CONTEXT_line_history = _zz_104_;
  always @ (*) begin
    _zz_105_ = 1'b0;
    if(_zz_130_)begin
      _zz_105_ = 1'b1;
    end
  end

  always @ (*) begin
    _zz_106_ = memory_FORMAL_PC_NEXT;
    if(BranchPlugin_jumpInterface_valid)begin
      _zz_106_ = BranchPlugin_jumpInterface_payload;
    end
  end

  always @ (*) begin
    _zz_107_ = decode_FORMAL_PC_NEXT;
    if(IBusCachedPlugin_predictionJumpInterface_valid)begin
      _zz_107_ = IBusCachedPlugin_pcs_4;
    end
    if(IBusCachedPlugin_redoBranch_valid)begin
      _zz_107_ = IBusCachedPlugin_redoBranch_payload;
    end
  end

  assign decode_PC = _zz_110_;
  assign writeBack_PC = memory_to_writeBack_PC;
  assign writeBack_INSTRUCTION = memory_to_writeBack_INSTRUCTION;
  always @ (*) begin
    decode_arbitration_haltItself = 1'b0;
    if(((DBusCachedPlugin_mmuBus_busy && decode_arbitration_isValid) && decode_MEMORY_ENABLE))begin
      decode_arbitration_haltItself = 1'b1;
    end
    case(_zz_220_)
      3'b000 : begin
      end
      3'b001 : begin
      end
      3'b010 : begin
        decode_arbitration_haltItself = 1'b1;
      end
      3'b011 : begin
      end
      3'b100 : begin
      end
      default : begin
      end
    endcase
  end

  always @ (*) begin
    decode_arbitration_haltByOther = 1'b0;
    if(MmuPlugin_dBusAccess_cmd_valid)begin
      decode_arbitration_haltByOther = 1'b1;
    end
    if((decode_arbitration_isValid && (_zz_182_ || _zz_183_)))begin
      decode_arbitration_haltByOther = 1'b1;
    end
    if(CsrPlugin_interrupt)begin
      decode_arbitration_haltByOther = decode_arbitration_isValid;
    end
    if(({(writeBack_arbitration_isValid && (writeBack_ENV_CTRL == `EnvCtrlEnum_defaultEncoding_XRET)),{(memory_arbitration_isValid && (memory_ENV_CTRL == `EnvCtrlEnum_defaultEncoding_XRET)),(execute_arbitration_isValid && (execute_ENV_CTRL == `EnvCtrlEnum_defaultEncoding_XRET))}} != (3'b000)))begin
      decode_arbitration_haltByOther = 1'b1;
    end
  end

  always @ (*) begin
    decode_arbitration_removeIt = 1'b0;
    if(_zz_279_)begin
      decode_arbitration_removeIt = 1'b1;
    end
    if(decode_arbitration_isFlushed)begin
      decode_arbitration_removeIt = 1'b1;
    end
  end

  assign decode_arbitration_flushAll = 1'b0;
  always @ (*) begin
    execute_arbitration_haltItself = 1'b0;
    if((_zz_242_ && (! dataCache_1__io_cpu_flush_ready)))begin
      execute_arbitration_haltItself = 1'b1;
    end
    if(((dataCache_1__io_cpu_redo && execute_arbitration_isValid) && execute_MEMORY_ENABLE))begin
      execute_arbitration_haltItself = 1'b1;
    end
    if(_zz_269_)begin
      if(execute_CsrPlugin_blockedBySideEffects)begin
        execute_arbitration_haltItself = 1'b1;
      end
    end
  end

  always @ (*) begin
    execute_arbitration_haltByOther = 1'b0;
    if(_zz_280_)begin
      execute_arbitration_haltByOther = 1'b1;
    end
  end

  always @ (*) begin
    execute_arbitration_removeIt = 1'b0;
    if(execute_arbitration_isFlushed)begin
      execute_arbitration_removeIt = 1'b1;
    end
  end

  always @ (*) begin
    execute_arbitration_flushAll = 1'b0;
    if(BranchPlugin_branchExceptionPort_valid)begin
      execute_arbitration_flushAll = 1'b1;
    end
    if(_zz_280_)begin
      if(_zz_281_)begin
        execute_arbitration_flushAll = 1'b1;
      end
    end
    if(BranchPlugin_jumpInterface_valid)begin
      execute_arbitration_flushAll = 1'b1;
    end
  end

  always @ (*) begin
    memory_arbitration_haltItself = 1'b0;
    if(_zz_274_)begin
      if(_zz_282_)begin
        memory_arbitration_haltItself = 1'b1;
      end
    end
  end

  assign memory_arbitration_haltByOther = 1'b0;
  always @ (*) begin
    memory_arbitration_removeIt = 1'b0;
    if(BranchPlugin_branchExceptionPort_valid)begin
      memory_arbitration_removeIt = 1'b1;
    end
    if(memory_arbitration_isFlushed)begin
      memory_arbitration_removeIt = 1'b1;
    end
  end

  always @ (*) begin
    memory_arbitration_flushAll = 1'b0;
    if(DBusCachedPlugin_exceptionBus_valid)begin
      memory_arbitration_flushAll = 1'b1;
    end
    if(_zz_283_)begin
      memory_arbitration_flushAll = 1'b1;
    end
    if(_zz_284_)begin
      memory_arbitration_flushAll = 1'b1;
    end
  end

  always @ (*) begin
    writeBack_arbitration_haltItself = 1'b0;
    if(dataCache_1__io_cpu_writeBack_haltIt)begin
      writeBack_arbitration_haltItself = 1'b1;
    end
  end

  assign writeBack_arbitration_haltByOther = 1'b0;
  always @ (*) begin
    writeBack_arbitration_removeIt = 1'b0;
    if(DBusCachedPlugin_exceptionBus_valid)begin
      writeBack_arbitration_removeIt = 1'b1;
    end
    if(writeBack_arbitration_isFlushed)begin
      writeBack_arbitration_removeIt = 1'b1;
    end
  end

  always @ (*) begin
    writeBack_arbitration_flushAll = 1'b0;
    if(DBusCachedPlugin_redoBranch_valid)begin
      writeBack_arbitration_flushAll = 1'b1;
    end
  end

  assign lastStageInstruction = writeBack_INSTRUCTION;
  assign lastStagePc = writeBack_PC;
  assign lastStageIsValid = writeBack_arbitration_isValid;
  assign lastStageIsFiring = writeBack_arbitration_isFiring;
  always @ (*) begin
    IBusCachedPlugin_fetcherHalt = 1'b0;
    if(({CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_writeBack,{CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_memory,{CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_execute,CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_decode}}} != (4'b0000)))begin
      IBusCachedPlugin_fetcherHalt = 1'b1;
    end
    if(_zz_283_)begin
      IBusCachedPlugin_fetcherHalt = 1'b1;
    end
    if(_zz_284_)begin
      IBusCachedPlugin_fetcherHalt = 1'b1;
    end
    if(_zz_280_)begin
      if(_zz_281_)begin
        IBusCachedPlugin_fetcherHalt = 1'b1;
      end
    end
    if(DebugPlugin_haltIt)begin
      IBusCachedPlugin_fetcherHalt = 1'b1;
    end
    if(_zz_285_)begin
      IBusCachedPlugin_fetcherHalt = 1'b1;
    end
  end

  always @ (*) begin
    IBusCachedPlugin_fetcherflushIt = 1'b0;
    if(_zz_280_)begin
      if(_zz_281_)begin
        IBusCachedPlugin_fetcherflushIt = 1'b1;
      end
    end
  end

  always @ (*) begin
    IBusCachedPlugin_incomingInstruction = 1'b0;
    if((IBusCachedPlugin_iBusRsp_stages_1_input_valid || IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_valid))begin
      IBusCachedPlugin_incomingInstruction = 1'b1;
    end
  end

  always @ (*) begin
    _zz_111_ = 1'b0;
    if(DebugPlugin_godmode)begin
      _zz_111_ = 1'b1;
    end
  end

  always @ (*) begin
    CsrPlugin_jumpInterface_valid = 1'b0;
    if(_zz_283_)begin
      CsrPlugin_jumpInterface_valid = 1'b1;
    end
    if(_zz_284_)begin
      CsrPlugin_jumpInterface_valid = 1'b1;
    end
  end

  always @ (*) begin
    CsrPlugin_jumpInterface_payload = (32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx);
    if(_zz_283_)begin
      CsrPlugin_jumpInterface_payload = {CsrPlugin_xtvec_base,(2'b00)};
    end
    if(_zz_284_)begin
      case(_zz_286_)
        2'b11 : begin
          CsrPlugin_jumpInterface_payload = CsrPlugin_mepc;
        end
        default : begin
        end
      endcase
    end
  end

  always @ (*) begin
    CsrPlugin_forceMachineWire = 1'b0;
    if(DebugPlugin_godmode)begin
      CsrPlugin_forceMachineWire = 1'b1;
    end
  end

  always @ (*) begin
    CsrPlugin_allowInterrupts = 1'b1;
    if((DebugPlugin_haltIt || DebugPlugin_stepIt))begin
      CsrPlugin_allowInterrupts = 1'b0;
    end
  end

  always @ (*) begin
    CsrPlugin_allowException = 1'b1;
    if(DebugPlugin_godmode)begin
      CsrPlugin_allowException = 1'b0;
    end
  end

  assign IBusCachedPlugin_jump_pcLoad_valid = ({BranchPlugin_jumpInterface_valid,{CsrPlugin_jumpInterface_valid,{DBusCachedPlugin_redoBranch_valid,{IBusCachedPlugin_redoBranch_valid,IBusCachedPlugin_predictionJumpInterface_valid}}}} != (5'b00000));
  assign _zz_112_ = {IBusCachedPlugin_predictionJumpInterface_valid,{IBusCachedPlugin_redoBranch_valid,{BranchPlugin_jumpInterface_valid,{CsrPlugin_jumpInterface_valid,DBusCachedPlugin_redoBranch_valid}}}};
  assign _zz_113_ = (_zz_112_ & (~ _zz_322_));
  assign _zz_114_ = _zz_113_[3];
  assign _zz_115_ = _zz_113_[4];
  assign _zz_116_ = (_zz_113_[1] || _zz_114_);
  assign _zz_117_ = (_zz_113_[2] || _zz_114_);
  assign IBusCachedPlugin_jump_pcLoad_payload = _zz_246_;
  assign _zz_118_ = (! IBusCachedPlugin_fetcherHalt);
  assign IBusCachedPlugin_fetchPc_output_valid = (IBusCachedPlugin_fetchPc_preOutput_valid && _zz_118_);
  assign IBusCachedPlugin_fetchPc_preOutput_ready = (IBusCachedPlugin_fetchPc_output_ready && _zz_118_);
  assign IBusCachedPlugin_fetchPc_output_payload = IBusCachedPlugin_fetchPc_preOutput_payload;
  always @ (*) begin
    IBusCachedPlugin_fetchPc_propagatePc = 1'b0;
    if((IBusCachedPlugin_iBusRsp_stages_1_input_valid && IBusCachedPlugin_iBusRsp_stages_1_input_ready))begin
      IBusCachedPlugin_fetchPc_propagatePc = 1'b1;
    end
  end

  always @ (*) begin
    IBusCachedPlugin_fetchPc_pc = (IBusCachedPlugin_fetchPc_pcReg + _zz_324_);
    if(IBusCachedPlugin_jump_pcLoad_valid)begin
      IBusCachedPlugin_fetchPc_pc = IBusCachedPlugin_jump_pcLoad_payload;
    end
    IBusCachedPlugin_fetchPc_pc[0] = 1'b0;
    IBusCachedPlugin_fetchPc_pc[1] = 1'b0;
  end

  always @ (*) begin
    IBusCachedPlugin_fetchPc_samplePcNext = 1'b0;
    if(IBusCachedPlugin_fetchPc_propagatePc)begin
      IBusCachedPlugin_fetchPc_samplePcNext = 1'b1;
    end
    if(IBusCachedPlugin_jump_pcLoad_valid)begin
      IBusCachedPlugin_fetchPc_samplePcNext = 1'b1;
    end
    if(_zz_287_)begin
      IBusCachedPlugin_fetchPc_samplePcNext = 1'b1;
    end
  end

  assign IBusCachedPlugin_fetchPc_preOutput_valid = _zz_119_;
  assign IBusCachedPlugin_fetchPc_preOutput_payload = IBusCachedPlugin_fetchPc_pc;
  assign IBusCachedPlugin_iBusRsp_stages_0_input_valid = IBusCachedPlugin_fetchPc_output_valid;
  assign IBusCachedPlugin_fetchPc_output_ready = IBusCachedPlugin_iBusRsp_stages_0_input_ready;
  assign IBusCachedPlugin_iBusRsp_stages_0_input_payload = IBusCachedPlugin_fetchPc_output_payload;
  assign IBusCachedPlugin_iBusRsp_stages_0_inputSample = 1'b1;
  always @ (*) begin
    IBusCachedPlugin_iBusRsp_stages_0_halt = 1'b0;
    if(IBusCachedPlugin_cache_io_cpu_prefetch_haltIt)begin
      IBusCachedPlugin_iBusRsp_stages_0_halt = 1'b1;
    end
  end

  assign _zz_120_ = (! IBusCachedPlugin_iBusRsp_stages_0_halt);
  assign IBusCachedPlugin_iBusRsp_stages_0_input_ready = (IBusCachedPlugin_iBusRsp_stages_0_output_ready && _zz_120_);
  assign IBusCachedPlugin_iBusRsp_stages_0_output_valid = (IBusCachedPlugin_iBusRsp_stages_0_input_valid && _zz_120_);
  assign IBusCachedPlugin_iBusRsp_stages_0_output_payload = IBusCachedPlugin_iBusRsp_stages_0_input_payload;
  always @ (*) begin
    IBusCachedPlugin_iBusRsp_stages_1_halt = 1'b0;
    if(IBusCachedPlugin_cache_io_cpu_fetch_haltIt)begin
      IBusCachedPlugin_iBusRsp_stages_1_halt = 1'b1;
    end
  end

  assign _zz_121_ = (! IBusCachedPlugin_iBusRsp_stages_1_halt);
  assign IBusCachedPlugin_iBusRsp_stages_1_input_ready = (IBusCachedPlugin_iBusRsp_stages_1_output_ready && _zz_121_);
  assign IBusCachedPlugin_iBusRsp_stages_1_output_valid = (IBusCachedPlugin_iBusRsp_stages_1_input_valid && _zz_121_);
  assign IBusCachedPlugin_iBusRsp_stages_1_output_payload = IBusCachedPlugin_iBusRsp_stages_1_input_payload;
  always @ (*) begin
    IBusCachedPlugin_iBusRsp_cacheRspArbitration_halt = 1'b0;
    if((IBusCachedPlugin_rsp_issueDetected || IBusCachedPlugin_rsp_iBusRspOutputHalt))begin
      IBusCachedPlugin_iBusRsp_cacheRspArbitration_halt = 1'b1;
    end
  end

  assign _zz_122_ = (! IBusCachedPlugin_iBusRsp_cacheRspArbitration_halt);
  assign IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_ready = (IBusCachedPlugin_iBusRsp_cacheRspArbitration_output_ready && _zz_122_);
  assign IBusCachedPlugin_iBusRsp_cacheRspArbitration_output_valid = (IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_valid && _zz_122_);
  assign IBusCachedPlugin_iBusRsp_cacheRspArbitration_output_payload = IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_payload;
  assign IBusCachedPlugin_iBusRsp_stages_0_output_ready = _zz_123_;
  assign _zz_123_ = ((1'b0 && (! _zz_124_)) || IBusCachedPlugin_iBusRsp_stages_1_input_ready);
  assign _zz_124_ = _zz_125_;
  assign IBusCachedPlugin_iBusRsp_stages_1_input_valid = _zz_124_;
  assign IBusCachedPlugin_iBusRsp_stages_1_input_payload = IBusCachedPlugin_fetchPc_pcReg;
  assign IBusCachedPlugin_iBusRsp_stages_1_output_ready = ((1'b0 && (! _zz_126_)) || IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_ready);
  assign _zz_126_ = _zz_127_;
  assign IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_valid = _zz_126_;
  assign IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_payload = _zz_128_;
  always @ (*) begin
    IBusCachedPlugin_iBusRsp_readyForError = 1'b1;
    if((! IBusCachedPlugin_pcValids_0))begin
      IBusCachedPlugin_iBusRsp_readyForError = 1'b0;
    end
  end

  assign IBusCachedPlugin_pcValids_0 = IBusCachedPlugin_injector_nextPcCalc_valids_1;
  assign IBusCachedPlugin_pcValids_1 = IBusCachedPlugin_injector_nextPcCalc_valids_2;
  assign IBusCachedPlugin_pcValids_2 = IBusCachedPlugin_injector_nextPcCalc_valids_3;
  assign IBusCachedPlugin_pcValids_3 = IBusCachedPlugin_injector_nextPcCalc_valids_4;
  assign IBusCachedPlugin_iBusRsp_decodeInput_ready = (! decode_arbitration_isStuck);
  always @ (*) begin
    decode_arbitration_isValid = (IBusCachedPlugin_iBusRsp_decodeInput_valid && (! IBusCachedPlugin_injector_decodeRemoved));
    case(_zz_220_)
      3'b000 : begin
      end
      3'b001 : begin
      end
      3'b010 : begin
        decode_arbitration_isValid = 1'b1;
      end
      3'b011 : begin
        decode_arbitration_isValid = 1'b1;
      end
      3'b100 : begin
      end
      default : begin
      end
    endcase
  end

  assign _zz_110_ = IBusCachedPlugin_iBusRsp_decodeInput_payload_pc;
  assign _zz_109_ = IBusCachedPlugin_iBusRsp_decodeInput_payload_rsp_inst;
  assign _zz_108_ = (decode_PC + (32'b00000000000000000000000000000100));
  assign _zz_134_ = (IBusCachedPlugin_fetchPc_output_payload >>> 2);
  assign _zz_135_ = (IBusCachedPlugin_iBusRsp_stages_0_output_ready || (IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt));
  assign _zz_103_ = _zz_136_;
  assign _zz_104_ = _zz_137_;
  assign _zz_138_ = (IBusCachedPlugin_decodePrediction_rsp_wasWrong ^ memory_PREDICTION_CONTEXT_line_history[1]);
  assign _zz_131_ = (memory_PC[11 : 2] + (10'b0000000000));
  assign _zz_130_ = ((((! memory_PREDICTION_CONTEXT_hazard) && memory_arbitration_isFiring) && (memory_BRANCH_CTRL == `BranchCtrlEnum_defaultEncoding_B)) && (! ($signed(memory_PREDICTION_CONTEXT_line_history) == $signed(_zz_332_))));
  always @ (*) begin
    IBusCachedPlugin_decodePrediction_cmd_hadBranch = ((decode_BRANCH_CTRL == `BranchCtrlEnum_defaultEncoding_JAL) || ((decode_BRANCH_CTRL == `BranchCtrlEnum_defaultEncoding_B) && decode_PREDICTION_CONTEXT_line_history[1]));
    if(_zz_143_)begin
      IBusCachedPlugin_decodePrediction_cmd_hadBranch = 1'b0;
    end
  end

  assign _zz_139_ = _zz_335_[19];
  always @ (*) begin
    _zz_140_[10] = _zz_139_;
    _zz_140_[9] = _zz_139_;
    _zz_140_[8] = _zz_139_;
    _zz_140_[7] = _zz_139_;
    _zz_140_[6] = _zz_139_;
    _zz_140_[5] = _zz_139_;
    _zz_140_[4] = _zz_139_;
    _zz_140_[3] = _zz_139_;
    _zz_140_[2] = _zz_139_;
    _zz_140_[1] = _zz_139_;
    _zz_140_[0] = _zz_139_;
  end

  assign _zz_141_ = _zz_336_[11];
  always @ (*) begin
    _zz_142_[18] = _zz_141_;
    _zz_142_[17] = _zz_141_;
    _zz_142_[16] = _zz_141_;
    _zz_142_[15] = _zz_141_;
    _zz_142_[14] = _zz_141_;
    _zz_142_[13] = _zz_141_;
    _zz_142_[12] = _zz_141_;
    _zz_142_[11] = _zz_141_;
    _zz_142_[10] = _zz_141_;
    _zz_142_[9] = _zz_141_;
    _zz_142_[8] = _zz_141_;
    _zz_142_[7] = _zz_141_;
    _zz_142_[6] = _zz_141_;
    _zz_142_[5] = _zz_141_;
    _zz_142_[4] = _zz_141_;
    _zz_142_[3] = _zz_141_;
    _zz_142_[2] = _zz_141_;
    _zz_142_[1] = _zz_141_;
    _zz_142_[0] = _zz_141_;
  end

  always @ (*) begin
    case(decode_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_JAL : begin
        _zz_143_ = _zz_337_[1];
      end
      default : begin
        _zz_143_ = _zz_338_[1];
      end
    endcase
  end

  assign IBusCachedPlugin_predictionJumpInterface_valid = (IBusCachedPlugin_decodePrediction_cmd_hadBranch && decode_arbitration_isFiring);
  assign _zz_144_ = _zz_339_[19];
  always @ (*) begin
    _zz_145_[10] = _zz_144_;
    _zz_145_[9] = _zz_144_;
    _zz_145_[8] = _zz_144_;
    _zz_145_[7] = _zz_144_;
    _zz_145_[6] = _zz_144_;
    _zz_145_[5] = _zz_144_;
    _zz_145_[4] = _zz_144_;
    _zz_145_[3] = _zz_144_;
    _zz_145_[2] = _zz_144_;
    _zz_145_[1] = _zz_144_;
    _zz_145_[0] = _zz_144_;
  end

  assign _zz_146_ = _zz_340_[11];
  always @ (*) begin
    _zz_147_[18] = _zz_146_;
    _zz_147_[17] = _zz_146_;
    _zz_147_[16] = _zz_146_;
    _zz_147_[15] = _zz_146_;
    _zz_147_[14] = _zz_146_;
    _zz_147_[13] = _zz_146_;
    _zz_147_[12] = _zz_146_;
    _zz_147_[11] = _zz_146_;
    _zz_147_[10] = _zz_146_;
    _zz_147_[9] = _zz_146_;
    _zz_147_[8] = _zz_146_;
    _zz_147_[7] = _zz_146_;
    _zz_147_[6] = _zz_146_;
    _zz_147_[5] = _zz_146_;
    _zz_147_[4] = _zz_146_;
    _zz_147_[3] = _zz_146_;
    _zz_147_[2] = _zz_146_;
    _zz_147_[1] = _zz_146_;
    _zz_147_[0] = _zz_146_;
  end

  assign IBusCachedPlugin_pcs_4 = (decode_PC + ((decode_BRANCH_CTRL == `BranchCtrlEnum_defaultEncoding_JAL) ? {{_zz_145_,{{{_zz_446_,decode_INSTRUCTION[19 : 12]},decode_INSTRUCTION[20]},decode_INSTRUCTION[30 : 21]}},1'b0} : {{_zz_147_,{{{_zz_447_,_zz_448_},decode_INSTRUCTION[30 : 25]},decode_INSTRUCTION[11 : 8]}},1'b0}));
  assign iBus_cmd_valid = IBusCachedPlugin_cache_io_mem_cmd_valid;
  always @ (*) begin
    iBus_cmd_payload_address = IBusCachedPlugin_cache_io_mem_cmd_payload_address;
    iBus_cmd_payload_address = IBusCachedPlugin_cache_io_mem_cmd_payload_address;
  end

  assign iBus_cmd_payload_size = IBusCachedPlugin_cache_io_mem_cmd_payload_size;
  assign IBusCachedPlugin_s0_tightlyCoupledHit = 1'b0;
  assign _zz_222_ = (IBusCachedPlugin_iBusRsp_stages_0_input_valid && (! IBusCachedPlugin_s0_tightlyCoupledHit));
  assign _zz_225_ = (IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt);
  assign _zz_226_ = (32'b00000000000000000000000000000000);
  assign _zz_223_ = (IBusCachedPlugin_iBusRsp_stages_1_input_valid && (! IBusCachedPlugin_s1_tightlyCoupledHit));
  assign _zz_224_ = (! IBusCachedPlugin_iBusRsp_stages_1_input_ready);
  assign _zz_227_ = (IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_valid && (! IBusCachedPlugin_s2_tightlyCoupledHit));
  assign _zz_228_ = (! IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_ready);
  assign _zz_229_ = (CsrPlugin_privilege == (2'b00));
  assign _zz_100_ = (decode_arbitration_isStuck ? decode_INSTRUCTION : IBusCachedPlugin_cache_io_cpu_fetch_data);
  assign IBusCachedPlugin_rsp_iBusRspOutputHalt = 1'b0;
  always @ (*) begin
    IBusCachedPlugin_rsp_redoFetch = 1'b0;
    if(_zz_278_)begin
      IBusCachedPlugin_rsp_redoFetch = 1'b1;
    end
    if(_zz_276_)begin
      IBusCachedPlugin_rsp_redoFetch = 1'b1;
    end
    if((! IBusCachedPlugin_iBusRsp_readyForError))begin
      IBusCachedPlugin_rsp_redoFetch = 1'b0;
    end
  end

  always @ (*) begin
    _zz_230_ = (IBusCachedPlugin_rsp_redoFetch && (! IBusCachedPlugin_cache_io_cpu_decode_mmuRefilling));
    if(_zz_276_)begin
      _zz_230_ = 1'b1;
    end
    if((! IBusCachedPlugin_iBusRsp_readyForError))begin
      _zz_230_ = 1'b0;
    end
  end

  always @ (*) begin
    IBusCachedPlugin_decodeExceptionPort_valid = 1'b0;
    if(_zz_277_)begin
      IBusCachedPlugin_decodeExceptionPort_valid = IBusCachedPlugin_iBusRsp_readyForError;
    end
    if(_zz_275_)begin
      IBusCachedPlugin_decodeExceptionPort_valid = IBusCachedPlugin_iBusRsp_readyForError;
    end
    if(IBusCachedPlugin_fetcherHalt)begin
      IBusCachedPlugin_decodeExceptionPort_valid = 1'b0;
    end
  end

  always @ (*) begin
    IBusCachedPlugin_decodeExceptionPort_payload_code = (4'bxxxx);
    if(_zz_277_)begin
      IBusCachedPlugin_decodeExceptionPort_payload_code = (4'b1100);
    end
    if(_zz_275_)begin
      IBusCachedPlugin_decodeExceptionPort_payload_code = (4'b0001);
    end
  end

  assign IBusCachedPlugin_decodeExceptionPort_payload_badAddr = {IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_payload[31 : 2],(2'b00)};
  assign IBusCachedPlugin_redoBranch_valid = IBusCachedPlugin_rsp_redoFetch;
  assign IBusCachedPlugin_redoBranch_payload = IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_payload;
  assign IBusCachedPlugin_iBusRsp_decodeInput_valid = IBusCachedPlugin_iBusRsp_cacheRspArbitration_output_valid;
  assign IBusCachedPlugin_iBusRsp_cacheRspArbitration_output_ready = IBusCachedPlugin_iBusRsp_decodeInput_ready;
  assign IBusCachedPlugin_iBusRsp_decodeInput_payload_rsp_inst = IBusCachedPlugin_cache_io_cpu_decode_data;
  assign IBusCachedPlugin_iBusRsp_decodeInput_payload_pc = IBusCachedPlugin_iBusRsp_cacheRspArbitration_output_payload;
  assign IBusCachedPlugin_mmuBus_cmd_isValid = IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_cmd_isValid;
  assign IBusCachedPlugin_mmuBus_cmd_virtualAddress = IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_cmd_virtualAddress;
  assign IBusCachedPlugin_mmuBus_cmd_bypassTranslation = IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_cmd_bypassTranslation;
  assign IBusCachedPlugin_mmuBus_end = IBusCachedPlugin_cache_io_cpu_fetch_mmuBus_end;
  assign _zz_221_ = (decode_arbitration_isValid && decode_FLUSH_ALL);
  assign dBus_cmd_valid = dataCache_1__io_mem_cmd_valid;
  assign dBus_cmd_payload_wr = dataCache_1__io_mem_cmd_payload_wr;
  assign dBus_cmd_payload_address = dataCache_1__io_mem_cmd_payload_address;
  assign dBus_cmd_payload_data = dataCache_1__io_mem_cmd_payload_data;
  assign dBus_cmd_payload_mask = dataCache_1__io_mem_cmd_payload_mask;
  assign dBus_cmd_payload_length = dataCache_1__io_mem_cmd_payload_length;
  assign dBus_cmd_payload_last = dataCache_1__io_mem_cmd_payload_last;
  assign execute_DBusCachedPlugin_size = execute_INSTRUCTION[13 : 12];
  always @ (*) begin
    _zz_231_ = (execute_arbitration_isValid && execute_MEMORY_ENABLE);
    if(MmuPlugin_dBusAccess_cmd_valid)begin
      if(_zz_288_)begin
        if(_zz_289_)begin
          _zz_231_ = 1'b1;
        end
      end
    end
  end

  always @ (*) begin
    _zz_232_ = execute_SRC_ADD;
    if(MmuPlugin_dBusAccess_cmd_valid)begin
      if(_zz_288_)begin
        _zz_232_ = MmuPlugin_dBusAccess_cmd_payload_address;
      end
    end
  end

  always @ (*) begin
    _zz_233_ = execute_MEMORY_WR;
    if(MmuPlugin_dBusAccess_cmd_valid)begin
      if(_zz_288_)begin
        _zz_233_ = MmuPlugin_dBusAccess_cmd_payload_write;
      end
    end
  end

  always @ (*) begin
    case(execute_DBusCachedPlugin_size)
      2'b00 : begin
        _zz_148_ = {{{execute_RS2[7 : 0],execute_RS2[7 : 0]},execute_RS2[7 : 0]},execute_RS2[7 : 0]};
      end
      2'b01 : begin
        _zz_148_ = {execute_RS2[15 : 0],execute_RS2[15 : 0]};
      end
      default : begin
        _zz_148_ = execute_RS2[31 : 0];
      end
    endcase
  end

  always @ (*) begin
    _zz_234_ = _zz_148_;
    if(MmuPlugin_dBusAccess_cmd_valid)begin
      if(_zz_288_)begin
        _zz_234_ = MmuPlugin_dBusAccess_cmd_payload_data;
      end
    end
  end

  always @ (*) begin
    _zz_235_ = execute_DBusCachedPlugin_size;
    if(MmuPlugin_dBusAccess_cmd_valid)begin
      if(_zz_288_)begin
        _zz_235_ = MmuPlugin_dBusAccess_cmd_payload_size;
      end
    end
  end

  assign _zz_242_ = (execute_arbitration_isValid && execute_MEMORY_MANAGMENT);
  assign _zz_96_ = _zz_232_[1 : 0];
  always @ (*) begin
    _zz_236_ = (memory_arbitration_isValid && memory_MEMORY_ENABLE);
    if(memory_IS_DBUS_SHARING)begin
      _zz_236_ = 1'b1;
    end
  end

  assign _zz_237_ = memory_REGFILE_WRITE_DATA;
  assign DBusCachedPlugin_mmuBus_cmd_isValid = dataCache_1__io_cpu_memory_mmuBus_cmd_isValid;
  assign DBusCachedPlugin_mmuBus_cmd_virtualAddress = dataCache_1__io_cpu_memory_mmuBus_cmd_virtualAddress;
  always @ (*) begin
    DBusCachedPlugin_mmuBus_cmd_bypassTranslation = dataCache_1__io_cpu_memory_mmuBus_cmd_bypassTranslation;
    if(memory_IS_DBUS_SHARING)begin
      DBusCachedPlugin_mmuBus_cmd_bypassTranslation = 1'b1;
    end
  end

  always @ (*) begin
    _zz_238_ = DBusCachedPlugin_mmuBus_rsp_isIoAccess;
    if((_zz_111_ && (! dataCache_1__io_cpu_memory_isWrite)))begin
      _zz_238_ = 1'b1;
    end
  end

  assign DBusCachedPlugin_mmuBus_end = dataCache_1__io_cpu_memory_mmuBus_end;
  always @ (*) begin
    _zz_239_ = (writeBack_arbitration_isValid && writeBack_MEMORY_ENABLE);
    if(writeBack_IS_DBUS_SHARING)begin
      _zz_239_ = 1'b1;
    end
  end

  assign _zz_240_ = (CsrPlugin_privilege == (2'b00));
  assign _zz_241_ = writeBack_REGFILE_WRITE_DATA;
  always @ (*) begin
    DBusCachedPlugin_redoBranch_valid = 1'b0;
    if(_zz_290_)begin
      if(dataCache_1__io_cpu_redo)begin
        DBusCachedPlugin_redoBranch_valid = 1'b1;
      end
    end
  end

  assign DBusCachedPlugin_redoBranch_payload = writeBack_PC;
  always @ (*) begin
    DBusCachedPlugin_exceptionBus_valid = 1'b0;
    if(_zz_290_)begin
      if(dataCache_1__io_cpu_writeBack_accessError)begin
        DBusCachedPlugin_exceptionBus_valid = 1'b1;
      end
      if(dataCache_1__io_cpu_writeBack_unalignedAccess)begin
        DBusCachedPlugin_exceptionBus_valid = 1'b1;
      end
      if(dataCache_1__io_cpu_writeBack_mmuException)begin
        DBusCachedPlugin_exceptionBus_valid = 1'b1;
      end
      if(dataCache_1__io_cpu_redo)begin
        DBusCachedPlugin_exceptionBus_valid = 1'b0;
      end
    end
  end

  assign DBusCachedPlugin_exceptionBus_payload_badAddr = writeBack_REGFILE_WRITE_DATA;
  always @ (*) begin
    DBusCachedPlugin_exceptionBus_payload_code = (4'bxxxx);
    if(_zz_290_)begin
      if(dataCache_1__io_cpu_writeBack_accessError)begin
        DBusCachedPlugin_exceptionBus_payload_code = {1'd0, _zz_341_};
      end
      if(dataCache_1__io_cpu_writeBack_unalignedAccess)begin
        DBusCachedPlugin_exceptionBus_payload_code = {1'd0, _zz_342_};
      end
      if(dataCache_1__io_cpu_writeBack_mmuException)begin
        DBusCachedPlugin_exceptionBus_payload_code = (writeBack_MEMORY_WR ? (4'b1111) : (4'b1101));
      end
    end
  end

  always @ (*) begin
    writeBack_DBusCachedPlugin_rspShifted = dataCache_1__io_cpu_writeBack_data;
    case(writeBack_MEMORY_ADDRESS_LOW)
      2'b01 : begin
        writeBack_DBusCachedPlugin_rspShifted[7 : 0] = dataCache_1__io_cpu_writeBack_data[15 : 8];
      end
      2'b10 : begin
        writeBack_DBusCachedPlugin_rspShifted[15 : 0] = dataCache_1__io_cpu_writeBack_data[31 : 16];
      end
      2'b11 : begin
        writeBack_DBusCachedPlugin_rspShifted[7 : 0] = dataCache_1__io_cpu_writeBack_data[31 : 24];
      end
      default : begin
      end
    endcase
  end

  assign _zz_149_ = (writeBack_DBusCachedPlugin_rspShifted[7] && (! writeBack_INSTRUCTION[14]));
  always @ (*) begin
    _zz_150_[31] = _zz_149_;
    _zz_150_[30] = _zz_149_;
    _zz_150_[29] = _zz_149_;
    _zz_150_[28] = _zz_149_;
    _zz_150_[27] = _zz_149_;
    _zz_150_[26] = _zz_149_;
    _zz_150_[25] = _zz_149_;
    _zz_150_[24] = _zz_149_;
    _zz_150_[23] = _zz_149_;
    _zz_150_[22] = _zz_149_;
    _zz_150_[21] = _zz_149_;
    _zz_150_[20] = _zz_149_;
    _zz_150_[19] = _zz_149_;
    _zz_150_[18] = _zz_149_;
    _zz_150_[17] = _zz_149_;
    _zz_150_[16] = _zz_149_;
    _zz_150_[15] = _zz_149_;
    _zz_150_[14] = _zz_149_;
    _zz_150_[13] = _zz_149_;
    _zz_150_[12] = _zz_149_;
    _zz_150_[11] = _zz_149_;
    _zz_150_[10] = _zz_149_;
    _zz_150_[9] = _zz_149_;
    _zz_150_[8] = _zz_149_;
    _zz_150_[7 : 0] = writeBack_DBusCachedPlugin_rspShifted[7 : 0];
  end

  assign _zz_151_ = (writeBack_DBusCachedPlugin_rspShifted[15] && (! writeBack_INSTRUCTION[14]));
  always @ (*) begin
    _zz_152_[31] = _zz_151_;
    _zz_152_[30] = _zz_151_;
    _zz_152_[29] = _zz_151_;
    _zz_152_[28] = _zz_151_;
    _zz_152_[27] = _zz_151_;
    _zz_152_[26] = _zz_151_;
    _zz_152_[25] = _zz_151_;
    _zz_152_[24] = _zz_151_;
    _zz_152_[23] = _zz_151_;
    _zz_152_[22] = _zz_151_;
    _zz_152_[21] = _zz_151_;
    _zz_152_[20] = _zz_151_;
    _zz_152_[19] = _zz_151_;
    _zz_152_[18] = _zz_151_;
    _zz_152_[17] = _zz_151_;
    _zz_152_[16] = _zz_151_;
    _zz_152_[15 : 0] = writeBack_DBusCachedPlugin_rspShifted[15 : 0];
  end

  always @ (*) begin
    case(_zz_319_)
      2'b00 : begin
        writeBack_DBusCachedPlugin_rspFormated = _zz_150_;
      end
      2'b01 : begin
        writeBack_DBusCachedPlugin_rspFormated = _zz_152_;
      end
      default : begin
        writeBack_DBusCachedPlugin_rspFormated = writeBack_DBusCachedPlugin_rspShifted;
      end
    endcase
  end

  always @ (*) begin
    MmuPlugin_dBusAccess_cmd_ready = 1'b0;
    if(MmuPlugin_dBusAccess_cmd_valid)begin
      if(_zz_288_)begin
        if(_zz_289_)begin
          MmuPlugin_dBusAccess_cmd_ready = (! execute_arbitration_isStuck);
        end
      end
    end
  end

  always @ (*) begin
    DBusCachedPlugin_forceDatapath = 1'b0;
    if(MmuPlugin_dBusAccess_cmd_valid)begin
      if(_zz_288_)begin
        DBusCachedPlugin_forceDatapath = 1'b1;
      end
    end
  end

  assign _zz_94_ = (MmuPlugin_dBusAccess_cmd_valid && MmuPlugin_dBusAccess_cmd_ready);
  assign MmuPlugin_dBusAccess_rsp_valid = ((writeBack_IS_DBUS_SHARING && (! dataCache_1__io_cpu_writeBack_isWrite)) && (dataCache_1__io_cpu_redo || (! dataCache_1__io_cpu_writeBack_haltIt)));
  assign MmuPlugin_dBusAccess_rsp_payload_data = dataCache_1__io_cpu_writeBack_data;
  assign MmuPlugin_dBusAccess_rsp_payload_error = (dataCache_1__io_cpu_writeBack_unalignedAccess || dataCache_1__io_cpu_writeBack_accessError);
  assign MmuPlugin_dBusAccess_rsp_payload_redo = dataCache_1__io_cpu_redo;
  assign MmuPlugin_ports_0_cacheHits_0 = ((MmuPlugin_ports_0_cache_0_valid && (MmuPlugin_ports_0_cache_0_virtualAddress_1 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_0_cache_0_superPage || (MmuPlugin_ports_0_cache_0_virtualAddress_0 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_0_cacheHits_1 = ((MmuPlugin_ports_0_cache_1_valid && (MmuPlugin_ports_0_cache_1_virtualAddress_1 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_0_cache_1_superPage || (MmuPlugin_ports_0_cache_1_virtualAddress_0 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_0_cacheHits_2 = ((MmuPlugin_ports_0_cache_2_valid && (MmuPlugin_ports_0_cache_2_virtualAddress_1 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_0_cache_2_superPage || (MmuPlugin_ports_0_cache_2_virtualAddress_0 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_0_cacheHits_3 = ((MmuPlugin_ports_0_cache_3_valid && (MmuPlugin_ports_0_cache_3_virtualAddress_1 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_0_cache_3_superPage || (MmuPlugin_ports_0_cache_3_virtualAddress_0 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_0_cacheHits_4 = ((MmuPlugin_ports_0_cache_4_valid && (MmuPlugin_ports_0_cache_4_virtualAddress_1 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_0_cache_4_superPage || (MmuPlugin_ports_0_cache_4_virtualAddress_0 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_0_cacheHits_5 = ((MmuPlugin_ports_0_cache_5_valid && (MmuPlugin_ports_0_cache_5_virtualAddress_1 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_0_cache_5_superPage || (MmuPlugin_ports_0_cache_5_virtualAddress_0 == DBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_0_cacheHit = ({MmuPlugin_ports_0_cacheHits_5,{MmuPlugin_ports_0_cacheHits_4,{MmuPlugin_ports_0_cacheHits_3,{MmuPlugin_ports_0_cacheHits_2,{MmuPlugin_ports_0_cacheHits_1,MmuPlugin_ports_0_cacheHits_0}}}}} != (6'b000000));
  assign _zz_153_ = ((MmuPlugin_ports_0_cacheHits_1 || MmuPlugin_ports_0_cacheHits_3) || MmuPlugin_ports_0_cacheHits_5);
  assign _zz_154_ = (MmuPlugin_ports_0_cacheHits_2 || MmuPlugin_ports_0_cacheHits_3);
  assign _zz_155_ = (MmuPlugin_ports_0_cacheHits_4 || MmuPlugin_ports_0_cacheHits_5);
  assign _zz_156_ = {_zz_155_,{_zz_154_,_zz_153_}};
  assign MmuPlugin_ports_0_cacheLine_valid = _zz_247_;
  assign MmuPlugin_ports_0_cacheLine_exception = _zz_248_;
  assign MmuPlugin_ports_0_cacheLine_superPage = _zz_249_;
  assign MmuPlugin_ports_0_cacheLine_virtualAddress_0 = _zz_250_;
  assign MmuPlugin_ports_0_cacheLine_virtualAddress_1 = _zz_251_;
  assign MmuPlugin_ports_0_cacheLine_physicalAddress_0 = _zz_252_;
  assign MmuPlugin_ports_0_cacheLine_physicalAddress_1 = _zz_253_;
  assign MmuPlugin_ports_0_cacheLine_allowRead = _zz_254_;
  assign MmuPlugin_ports_0_cacheLine_allowWrite = _zz_255_;
  assign MmuPlugin_ports_0_cacheLine_allowExecute = _zz_256_;
  assign MmuPlugin_ports_0_cacheLine_allowUser = _zz_257_;
  always @ (*) begin
    MmuPlugin_ports_0_entryToReplace_willIncrement = 1'b0;
    if(_zz_291_)begin
      if(_zz_292_)begin
        MmuPlugin_ports_0_entryToReplace_willIncrement = 1'b1;
      end
    end
  end

  assign MmuPlugin_ports_0_entryToReplace_willClear = 1'b0;
  assign MmuPlugin_ports_0_entryToReplace_willOverflowIfInc = (MmuPlugin_ports_0_entryToReplace_value == (3'b101));
  assign MmuPlugin_ports_0_entryToReplace_willOverflow = (MmuPlugin_ports_0_entryToReplace_willOverflowIfInc && MmuPlugin_ports_0_entryToReplace_willIncrement);
  always @ (*) begin
    if(MmuPlugin_ports_0_entryToReplace_willOverflow)begin
      MmuPlugin_ports_0_entryToReplace_valueNext = (3'b000);
    end else begin
      MmuPlugin_ports_0_entryToReplace_valueNext = (MmuPlugin_ports_0_entryToReplace_value + _zz_344_);
    end
    if(MmuPlugin_ports_0_entryToReplace_willClear)begin
      MmuPlugin_ports_0_entryToReplace_valueNext = (3'b000);
    end
  end

  always @ (*) begin
    MmuPlugin_ports_0_requireMmuLockup = (((DBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 28] == (4'b1100)) && (! DBusCachedPlugin_mmuBus_cmd_bypassTranslation)) && MmuPlugin_satp_mode);
    if(((! MmuPlugin_status_mprv) && (CsrPlugin_privilege == (2'b11))))begin
      MmuPlugin_ports_0_requireMmuLockup = 1'b0;
    end
    if((CsrPlugin_privilege == (2'b11)))begin
      if(((! MmuPlugin_status_mprv) || (CsrPlugin_mstatus_MPP == (2'b11))))begin
        MmuPlugin_ports_0_requireMmuLockup = 1'b0;
      end
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_0_requireMmuLockup)begin
      DBusCachedPlugin_mmuBus_rsp_physicalAddress = {{MmuPlugin_ports_0_cacheLine_physicalAddress_1,(MmuPlugin_ports_0_cacheLine_superPage ? DBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12] : MmuPlugin_ports_0_cacheLine_physicalAddress_0)},DBusCachedPlugin_mmuBus_cmd_virtualAddress[11 : 0]};
    end else begin
      DBusCachedPlugin_mmuBus_rsp_physicalAddress = DBusCachedPlugin_mmuBus_cmd_virtualAddress;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_0_requireMmuLockup)begin
      DBusCachedPlugin_mmuBus_rsp_allowRead = (MmuPlugin_ports_0_cacheLine_allowRead || (MmuPlugin_status_mxr && MmuPlugin_ports_0_cacheLine_allowExecute));
    end else begin
      DBusCachedPlugin_mmuBus_rsp_allowRead = 1'b1;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_0_requireMmuLockup)begin
      DBusCachedPlugin_mmuBus_rsp_allowWrite = MmuPlugin_ports_0_cacheLine_allowWrite;
    end else begin
      DBusCachedPlugin_mmuBus_rsp_allowWrite = 1'b1;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_0_requireMmuLockup)begin
      DBusCachedPlugin_mmuBus_rsp_allowExecute = MmuPlugin_ports_0_cacheLine_allowExecute;
    end else begin
      DBusCachedPlugin_mmuBus_rsp_allowExecute = 1'b1;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_0_requireMmuLockup)begin
      DBusCachedPlugin_mmuBus_rsp_exception = (MmuPlugin_ports_0_cacheHit && ((MmuPlugin_ports_0_cacheLine_exception || ((MmuPlugin_ports_0_cacheLine_allowUser && (CsrPlugin_privilege == (2'b01))) && (! MmuPlugin_status_sum))) || ((! MmuPlugin_ports_0_cacheLine_allowUser) && (CsrPlugin_privilege == (2'b00)))));
    end else begin
      DBusCachedPlugin_mmuBus_rsp_exception = 1'b0;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_0_requireMmuLockup)begin
      DBusCachedPlugin_mmuBus_rsp_refilling = (! MmuPlugin_ports_0_cacheHit);
    end else begin
      DBusCachedPlugin_mmuBus_rsp_refilling = 1'b0;
    end
  end

  assign DBusCachedPlugin_mmuBus_rsp_isIoAccess = (DBusCachedPlugin_mmuBus_rsp_physicalAddress[31 : 28] == (4'b1111));
  assign MmuPlugin_ports_1_cacheHits_0 = ((MmuPlugin_ports_1_cache_0_valid && (MmuPlugin_ports_1_cache_0_virtualAddress_1 == IBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_1_cache_0_superPage || (MmuPlugin_ports_1_cache_0_virtualAddress_0 == IBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_1_cacheHits_1 = ((MmuPlugin_ports_1_cache_1_valid && (MmuPlugin_ports_1_cache_1_virtualAddress_1 == IBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_1_cache_1_superPage || (MmuPlugin_ports_1_cache_1_virtualAddress_0 == IBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_1_cacheHits_2 = ((MmuPlugin_ports_1_cache_2_valid && (MmuPlugin_ports_1_cache_2_virtualAddress_1 == IBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_1_cache_2_superPage || (MmuPlugin_ports_1_cache_2_virtualAddress_0 == IBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_1_cacheHits_3 = ((MmuPlugin_ports_1_cache_3_valid && (MmuPlugin_ports_1_cache_3_virtualAddress_1 == IBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22])) && (MmuPlugin_ports_1_cache_3_superPage || (MmuPlugin_ports_1_cache_3_virtualAddress_0 == IBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12])));
  assign MmuPlugin_ports_1_cacheHit = ({MmuPlugin_ports_1_cacheHits_3,{MmuPlugin_ports_1_cacheHits_2,{MmuPlugin_ports_1_cacheHits_1,MmuPlugin_ports_1_cacheHits_0}}} != (4'b0000));
  assign _zz_157_ = (MmuPlugin_ports_1_cacheHits_1 || MmuPlugin_ports_1_cacheHits_3);
  assign _zz_158_ = (MmuPlugin_ports_1_cacheHits_2 || MmuPlugin_ports_1_cacheHits_3);
  assign _zz_159_ = {_zz_158_,_zz_157_};
  assign MmuPlugin_ports_1_cacheLine_valid = _zz_258_;
  assign MmuPlugin_ports_1_cacheLine_exception = _zz_259_;
  assign MmuPlugin_ports_1_cacheLine_superPage = _zz_260_;
  assign MmuPlugin_ports_1_cacheLine_virtualAddress_0 = _zz_261_;
  assign MmuPlugin_ports_1_cacheLine_virtualAddress_1 = _zz_262_;
  assign MmuPlugin_ports_1_cacheLine_physicalAddress_0 = _zz_263_;
  assign MmuPlugin_ports_1_cacheLine_physicalAddress_1 = _zz_264_;
  assign MmuPlugin_ports_1_cacheLine_allowRead = _zz_265_;
  assign MmuPlugin_ports_1_cacheLine_allowWrite = _zz_266_;
  assign MmuPlugin_ports_1_cacheLine_allowExecute = _zz_267_;
  assign MmuPlugin_ports_1_cacheLine_allowUser = _zz_268_;
  always @ (*) begin
    MmuPlugin_ports_1_entryToReplace_willIncrement = 1'b0;
    if(_zz_291_)begin
      if(_zz_293_)begin
        MmuPlugin_ports_1_entryToReplace_willIncrement = 1'b1;
      end
    end
  end

  assign MmuPlugin_ports_1_entryToReplace_willClear = 1'b0;
  assign MmuPlugin_ports_1_entryToReplace_willOverflowIfInc = (MmuPlugin_ports_1_entryToReplace_value == (2'b11));
  assign MmuPlugin_ports_1_entryToReplace_willOverflow = (MmuPlugin_ports_1_entryToReplace_willOverflowIfInc && MmuPlugin_ports_1_entryToReplace_willIncrement);
  always @ (*) begin
    MmuPlugin_ports_1_entryToReplace_valueNext = (MmuPlugin_ports_1_entryToReplace_value + _zz_346_);
    if(MmuPlugin_ports_1_entryToReplace_willClear)begin
      MmuPlugin_ports_1_entryToReplace_valueNext = (2'b00);
    end
  end

  always @ (*) begin
    MmuPlugin_ports_1_requireMmuLockup = (((IBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 28] == (4'b1100)) && (! IBusCachedPlugin_mmuBus_cmd_bypassTranslation)) && MmuPlugin_satp_mode);
    if(((! MmuPlugin_status_mprv) && (CsrPlugin_privilege == (2'b11))))begin
      MmuPlugin_ports_1_requireMmuLockup = 1'b0;
    end
    if((CsrPlugin_privilege == (2'b11)))begin
      MmuPlugin_ports_1_requireMmuLockup = 1'b0;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_1_requireMmuLockup)begin
      IBusCachedPlugin_mmuBus_rsp_physicalAddress = {{MmuPlugin_ports_1_cacheLine_physicalAddress_1,(MmuPlugin_ports_1_cacheLine_superPage ? IBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12] : MmuPlugin_ports_1_cacheLine_physicalAddress_0)},IBusCachedPlugin_mmuBus_cmd_virtualAddress[11 : 0]};
    end else begin
      IBusCachedPlugin_mmuBus_rsp_physicalAddress = IBusCachedPlugin_mmuBus_cmd_virtualAddress;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_1_requireMmuLockup)begin
      IBusCachedPlugin_mmuBus_rsp_allowRead = (MmuPlugin_ports_1_cacheLine_allowRead || (MmuPlugin_status_mxr && MmuPlugin_ports_1_cacheLine_allowExecute));
    end else begin
      IBusCachedPlugin_mmuBus_rsp_allowRead = 1'b1;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_1_requireMmuLockup)begin
      IBusCachedPlugin_mmuBus_rsp_allowWrite = MmuPlugin_ports_1_cacheLine_allowWrite;
    end else begin
      IBusCachedPlugin_mmuBus_rsp_allowWrite = 1'b1;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_1_requireMmuLockup)begin
      IBusCachedPlugin_mmuBus_rsp_allowExecute = MmuPlugin_ports_1_cacheLine_allowExecute;
    end else begin
      IBusCachedPlugin_mmuBus_rsp_allowExecute = 1'b1;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_1_requireMmuLockup)begin
      IBusCachedPlugin_mmuBus_rsp_exception = (MmuPlugin_ports_1_cacheHit && ((MmuPlugin_ports_1_cacheLine_exception || ((MmuPlugin_ports_1_cacheLine_allowUser && (CsrPlugin_privilege == (2'b01))) && (! MmuPlugin_status_sum))) || ((! MmuPlugin_ports_1_cacheLine_allowUser) && (CsrPlugin_privilege == (2'b00)))));
    end else begin
      IBusCachedPlugin_mmuBus_rsp_exception = 1'b0;
    end
  end

  always @ (*) begin
    if(MmuPlugin_ports_1_requireMmuLockup)begin
      IBusCachedPlugin_mmuBus_rsp_refilling = (! MmuPlugin_ports_1_cacheHit);
    end else begin
      IBusCachedPlugin_mmuBus_rsp_refilling = 1'b0;
    end
  end

  assign IBusCachedPlugin_mmuBus_rsp_isIoAccess = (IBusCachedPlugin_mmuBus_rsp_physicalAddress[31 : 28] == (4'b1111));
  assign MmuPlugin_shared_dBusRsp_pte_V = _zz_347_[0];
  assign MmuPlugin_shared_dBusRsp_pte_R = _zz_348_[0];
  assign MmuPlugin_shared_dBusRsp_pte_W = _zz_349_[0];
  assign MmuPlugin_shared_dBusRsp_pte_X = _zz_350_[0];
  assign MmuPlugin_shared_dBusRsp_pte_U = _zz_351_[0];
  assign MmuPlugin_shared_dBusRsp_pte_G = _zz_352_[0];
  assign MmuPlugin_shared_dBusRsp_pte_A = _zz_353_[0];
  assign MmuPlugin_shared_dBusRsp_pte_D = _zz_354_[0];
  assign MmuPlugin_shared_dBusRsp_pte_RSW = MmuPlugin_dBusAccess_rsp_payload_data[9 : 8];
  assign MmuPlugin_shared_dBusRsp_pte_PPN0 = MmuPlugin_dBusAccess_rsp_payload_data[19 : 10];
  assign MmuPlugin_shared_dBusRsp_pte_PPN1 = MmuPlugin_dBusAccess_rsp_payload_data[31 : 20];
  assign MmuPlugin_shared_dBusRsp_exception = (((! MmuPlugin_shared_dBusRsp_pte_V) || ((! MmuPlugin_shared_dBusRsp_pte_R) && MmuPlugin_shared_dBusRsp_pte_W)) || MmuPlugin_dBusAccess_rsp_payload_error);
  assign MmuPlugin_shared_dBusRsp_leaf = (MmuPlugin_shared_dBusRsp_pte_R || MmuPlugin_shared_dBusRsp_pte_X);
  always @ (*) begin
    MmuPlugin_dBusAccess_cmd_valid = 1'b0;
    case(MmuPlugin_shared_state_1_)
      `MmuPlugin_shared_State_defaultEncoding_IDLE : begin
      end
      `MmuPlugin_shared_State_defaultEncoding_L1_CMD : begin
        MmuPlugin_dBusAccess_cmd_valid = 1'b1;
      end
      `MmuPlugin_shared_State_defaultEncoding_L1_RSP : begin
      end
      `MmuPlugin_shared_State_defaultEncoding_L0_CMD : begin
        MmuPlugin_dBusAccess_cmd_valid = 1'b1;
      end
      default : begin
      end
    endcase
  end

  assign MmuPlugin_dBusAccess_cmd_payload_write = 1'b0;
  assign MmuPlugin_dBusAccess_cmd_payload_size = (2'b10);
  always @ (*) begin
    MmuPlugin_dBusAccess_cmd_payload_address = (32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx);
    case(MmuPlugin_shared_state_1_)
      `MmuPlugin_shared_State_defaultEncoding_IDLE : begin
      end
      `MmuPlugin_shared_State_defaultEncoding_L1_CMD : begin
        MmuPlugin_dBusAccess_cmd_payload_address = {{MmuPlugin_satp_ppn,MmuPlugin_shared_vpn_1},(2'b00)};
      end
      `MmuPlugin_shared_State_defaultEncoding_L1_RSP : begin
      end
      `MmuPlugin_shared_State_defaultEncoding_L0_CMD : begin
        MmuPlugin_dBusAccess_cmd_payload_address = {{{MmuPlugin_shared_pteBuffer_PPN1[9 : 0],MmuPlugin_shared_pteBuffer_PPN0},MmuPlugin_shared_vpn_0},(2'b00)};
      end
      default : begin
      end
    endcase
  end

  assign MmuPlugin_dBusAccess_cmd_payload_data = (32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx);
  assign MmuPlugin_dBusAccess_cmd_payload_writeMask = (4'bxxxx);
  assign DBusCachedPlugin_mmuBus_busy = ((MmuPlugin_shared_state_1_ != `MmuPlugin_shared_State_defaultEncoding_IDLE) && (MmuPlugin_shared_portId == (1'b1)));
  assign IBusCachedPlugin_mmuBus_busy = ((MmuPlugin_shared_state_1_ != `MmuPlugin_shared_State_defaultEncoding_IDLE) && (MmuPlugin_shared_portId == (1'b0)));
  assign _zz_161_ = ((decode_INSTRUCTION & (32'b00000000000000000000000000000100)) == (32'b00000000000000000000000000000100));
  assign _zz_162_ = ((decode_INSTRUCTION & (32'b00000000000000000001000000000000)) == (32'b00000000000000000000000000000000));
  assign _zz_163_ = ((decode_INSTRUCTION & (32'b00000000000000000000000001001000)) == (32'b00000000000000000000000001001000));
  assign _zz_164_ = ((decode_INSTRUCTION & (32'b00000000000000000100000001010000)) == (32'b00000000000000000100000001010000));
  assign _zz_160_ = {(((decode_INSTRUCTION & _zz_449_) == (32'b00000000000000000000000000100000)) != (1'b0)),{({_zz_450_,_zz_164_} != (2'b00)),{({_zz_451_,_zz_452_} != (2'b00)),{(_zz_453_ != _zz_454_),{_zz_455_,{_zz_456_,_zz_457_}}}}}};
  assign _zz_93_ = ({((decode_INSTRUCTION & (32'b00000000000000000000000001011111)) == (32'b00000000000000000000000000010111)),{((decode_INSTRUCTION & (32'b00000000000000000000000001111111)) == (32'b00000000000000000000000001101111)),{((decode_INSTRUCTION & (32'b00000000000000000001000001101111)) == (32'b00000000000000000000000000000011)),{((decode_INSTRUCTION & _zz_612_) == (32'b00000000000000000001000001110011)),{(_zz_613_ == _zz_614_),{_zz_615_,{_zz_616_,_zz_617_}}}}}}} != (21'b000000000000000000000));
  assign _zz_92_ = _zz_355_[0];
  assign _zz_165_ = _zz_160_[2 : 1];
  assign _zz_91_ = _zz_165_;
  assign _zz_166_ = _zz_160_[3 : 3];
  assign _zz_90_ = _zz_166_;
  assign _zz_89_ = _zz_356_[0];
  assign _zz_88_ = _zz_357_[0];
  assign _zz_167_ = _zz_160_[7 : 6];
  assign _zz_87_ = _zz_167_;
  assign _zz_86_ = _zz_358_[0];
  assign _zz_85_ = _zz_359_[0];
  assign _zz_168_ = _zz_160_[12 : 11];
  assign _zz_84_ = _zz_168_;
  assign _zz_83_ = _zz_360_[0];
  assign _zz_82_ = _zz_361_[0];
  assign _zz_81_ = _zz_362_[0];
  assign _zz_80_ = _zz_363_[0];
  assign _zz_79_ = _zz_364_[0];
  assign _zz_169_ = _zz_160_[19 : 18];
  assign _zz_78_ = _zz_169_;
  assign _zz_77_ = _zz_365_[0];
  assign _zz_76_ = _zz_366_[0];
  assign _zz_170_ = _zz_160_[23 : 22];
  assign _zz_75_ = _zz_170_;
  assign _zz_74_ = _zz_367_[0];
  assign _zz_73_ = _zz_368_[0];
  assign _zz_72_ = _zz_369_[0];
  assign _zz_71_ = _zz_370_[0];
  assign _zz_70_ = _zz_371_[0];
  assign _zz_69_ = _zz_372_[0];
  assign _zz_171_ = _zz_160_[31 : 30];
  assign _zz_68_ = _zz_171_;
  assign _zz_67_ = _zz_373_[0];
  assign decodeExceptionPort_valid = ((decode_arbitration_isValid && decode_INSTRUCTION_READY) && (! decode_LEGAL_INSTRUCTION));
  assign decodeExceptionPort_payload_code = (4'b0010);
  assign decodeExceptionPort_payload_badAddr = decode_INSTRUCTION;
  assign decode_RegFilePlugin_regFileReadAddress1 = decode_INSTRUCTION_ANTICIPATED[19 : 15];
  assign decode_RegFilePlugin_regFileReadAddress2 = decode_INSTRUCTION_ANTICIPATED[24 : 20];
  assign decode_RegFilePlugin_rs1Data = _zz_244_;
  assign decode_RegFilePlugin_rs2Data = _zz_245_;
  assign _zz_66_ = decode_RegFilePlugin_rs1Data;
  assign _zz_65_ = decode_RegFilePlugin_rs2Data;
  always @ (*) begin
    lastStageRegFileWrite_valid = (_zz_63_ && writeBack_arbitration_isFiring);
    if(_zz_172_)begin
      lastStageRegFileWrite_valid = 1'b1;
    end
  end

  assign lastStageRegFileWrite_payload_address = _zz_62_[11 : 7];
  assign lastStageRegFileWrite_payload_data = _zz_95_;
  always @ (*) begin
    case(execute_ALU_BITWISE_CTRL)
      `AluBitwiseCtrlEnum_defaultEncoding_AND_1 : begin
        execute_IntAluPlugin_bitwise = (execute_SRC1 & execute_SRC2);
      end
      `AluBitwiseCtrlEnum_defaultEncoding_OR_1 : begin
        execute_IntAluPlugin_bitwise = (execute_SRC1 | execute_SRC2);
      end
      default : begin
        execute_IntAluPlugin_bitwise = (execute_SRC1 ^ execute_SRC2);
      end
    endcase
  end

  always @ (*) begin
    case(execute_ALU_CTRL)
      `AluCtrlEnum_defaultEncoding_BITWISE : begin
        _zz_173_ = execute_IntAluPlugin_bitwise;
      end
      `AluCtrlEnum_defaultEncoding_SLT_SLTU : begin
        _zz_173_ = {31'd0, _zz_374_};
      end
      default : begin
        _zz_173_ = execute_SRC_ADD_SUB;
      end
    endcase
  end

  assign _zz_60_ = _zz_173_;
  assign _zz_58_ = (decode_SRC_ADD_ZERO && (! decode_SRC_USE_SUB_LESS));
  always @ (*) begin
    case(execute_SRC1_CTRL)
      `Src1CtrlEnum_defaultEncoding_RS : begin
        _zz_174_ = execute_RS1;
      end
      `Src1CtrlEnum_defaultEncoding_PC_INCREMENT : begin
        _zz_174_ = {29'd0, _zz_375_};
      end
      `Src1CtrlEnum_defaultEncoding_IMU : begin
        _zz_174_ = {execute_INSTRUCTION[31 : 12],(12'b000000000000)};
      end
      default : begin
        _zz_174_ = {27'd0, _zz_376_};
      end
    endcase
  end

  assign _zz_57_ = _zz_174_;
  assign _zz_175_ = _zz_377_[11];
  always @ (*) begin
    _zz_176_[19] = _zz_175_;
    _zz_176_[18] = _zz_175_;
    _zz_176_[17] = _zz_175_;
    _zz_176_[16] = _zz_175_;
    _zz_176_[15] = _zz_175_;
    _zz_176_[14] = _zz_175_;
    _zz_176_[13] = _zz_175_;
    _zz_176_[12] = _zz_175_;
    _zz_176_[11] = _zz_175_;
    _zz_176_[10] = _zz_175_;
    _zz_176_[9] = _zz_175_;
    _zz_176_[8] = _zz_175_;
    _zz_176_[7] = _zz_175_;
    _zz_176_[6] = _zz_175_;
    _zz_176_[5] = _zz_175_;
    _zz_176_[4] = _zz_175_;
    _zz_176_[3] = _zz_175_;
    _zz_176_[2] = _zz_175_;
    _zz_176_[1] = _zz_175_;
    _zz_176_[0] = _zz_175_;
  end

  assign _zz_177_ = _zz_378_[11];
  always @ (*) begin
    _zz_178_[19] = _zz_177_;
    _zz_178_[18] = _zz_177_;
    _zz_178_[17] = _zz_177_;
    _zz_178_[16] = _zz_177_;
    _zz_178_[15] = _zz_177_;
    _zz_178_[14] = _zz_177_;
    _zz_178_[13] = _zz_177_;
    _zz_178_[12] = _zz_177_;
    _zz_178_[11] = _zz_177_;
    _zz_178_[10] = _zz_177_;
    _zz_178_[9] = _zz_177_;
    _zz_178_[8] = _zz_177_;
    _zz_178_[7] = _zz_177_;
    _zz_178_[6] = _zz_177_;
    _zz_178_[5] = _zz_177_;
    _zz_178_[4] = _zz_177_;
    _zz_178_[3] = _zz_177_;
    _zz_178_[2] = _zz_177_;
    _zz_178_[1] = _zz_177_;
    _zz_178_[0] = _zz_177_;
  end

  always @ (*) begin
    case(execute_SRC2_CTRL)
      `Src2CtrlEnum_defaultEncoding_RS : begin
        _zz_179_ = execute_RS2;
      end
      `Src2CtrlEnum_defaultEncoding_IMI : begin
        _zz_179_ = {_zz_176_,execute_INSTRUCTION[31 : 20]};
      end
      `Src2CtrlEnum_defaultEncoding_IMS : begin
        _zz_179_ = {_zz_178_,{execute_INSTRUCTION[31 : 25],execute_INSTRUCTION[11 : 7]}};
      end
      default : begin
        _zz_179_ = _zz_53_;
      end
    endcase
  end

  assign _zz_55_ = _zz_179_;
  always @ (*) begin
    execute_SrcPlugin_addSub = _zz_379_;
    if(execute_SRC2_FORCE_ZERO)begin
      execute_SrcPlugin_addSub = execute_SRC1;
    end
  end

  assign execute_SrcPlugin_less = ((execute_SRC1[31] == execute_SRC2[31]) ? execute_SrcPlugin_addSub[31] : (execute_SRC_LESS_UNSIGNED ? execute_SRC2[31] : execute_SRC1[31]));
  assign _zz_52_ = execute_SrcPlugin_addSub;
  assign _zz_51_ = execute_SrcPlugin_addSub;
  assign _zz_50_ = execute_SrcPlugin_less;
  assign execute_FullBarrelShifterPlugin_amplitude = execute_SRC2[4 : 0];
  always @ (*) begin
    _zz_180_[0] = execute_SRC1[31];
    _zz_180_[1] = execute_SRC1[30];
    _zz_180_[2] = execute_SRC1[29];
    _zz_180_[3] = execute_SRC1[28];
    _zz_180_[4] = execute_SRC1[27];
    _zz_180_[5] = execute_SRC1[26];
    _zz_180_[6] = execute_SRC1[25];
    _zz_180_[7] = execute_SRC1[24];
    _zz_180_[8] = execute_SRC1[23];
    _zz_180_[9] = execute_SRC1[22];
    _zz_180_[10] = execute_SRC1[21];
    _zz_180_[11] = execute_SRC1[20];
    _zz_180_[12] = execute_SRC1[19];
    _zz_180_[13] = execute_SRC1[18];
    _zz_180_[14] = execute_SRC1[17];
    _zz_180_[15] = execute_SRC1[16];
    _zz_180_[16] = execute_SRC1[15];
    _zz_180_[17] = execute_SRC1[14];
    _zz_180_[18] = execute_SRC1[13];
    _zz_180_[19] = execute_SRC1[12];
    _zz_180_[20] = execute_SRC1[11];
    _zz_180_[21] = execute_SRC1[10];
    _zz_180_[22] = execute_SRC1[9];
    _zz_180_[23] = execute_SRC1[8];
    _zz_180_[24] = execute_SRC1[7];
    _zz_180_[25] = execute_SRC1[6];
    _zz_180_[26] = execute_SRC1[5];
    _zz_180_[27] = execute_SRC1[4];
    _zz_180_[28] = execute_SRC1[3];
    _zz_180_[29] = execute_SRC1[2];
    _zz_180_[30] = execute_SRC1[1];
    _zz_180_[31] = execute_SRC1[0];
  end

  assign execute_FullBarrelShifterPlugin_reversed = ((execute_SHIFT_CTRL == `ShiftCtrlEnum_defaultEncoding_SLL_1) ? _zz_180_ : execute_SRC1);
  assign _zz_48_ = _zz_387_;
  always @ (*) begin
    _zz_181_[0] = memory_SHIFT_RIGHT[31];
    _zz_181_[1] = memory_SHIFT_RIGHT[30];
    _zz_181_[2] = memory_SHIFT_RIGHT[29];
    _zz_181_[3] = memory_SHIFT_RIGHT[28];
    _zz_181_[4] = memory_SHIFT_RIGHT[27];
    _zz_181_[5] = memory_SHIFT_RIGHT[26];
    _zz_181_[6] = memory_SHIFT_RIGHT[25];
    _zz_181_[7] = memory_SHIFT_RIGHT[24];
    _zz_181_[8] = memory_SHIFT_RIGHT[23];
    _zz_181_[9] = memory_SHIFT_RIGHT[22];
    _zz_181_[10] = memory_SHIFT_RIGHT[21];
    _zz_181_[11] = memory_SHIFT_RIGHT[20];
    _zz_181_[12] = memory_SHIFT_RIGHT[19];
    _zz_181_[13] = memory_SHIFT_RIGHT[18];
    _zz_181_[14] = memory_SHIFT_RIGHT[17];
    _zz_181_[15] = memory_SHIFT_RIGHT[16];
    _zz_181_[16] = memory_SHIFT_RIGHT[15];
    _zz_181_[17] = memory_SHIFT_RIGHT[14];
    _zz_181_[18] = memory_SHIFT_RIGHT[13];
    _zz_181_[19] = memory_SHIFT_RIGHT[12];
    _zz_181_[20] = memory_SHIFT_RIGHT[11];
    _zz_181_[21] = memory_SHIFT_RIGHT[10];
    _zz_181_[22] = memory_SHIFT_RIGHT[9];
    _zz_181_[23] = memory_SHIFT_RIGHT[8];
    _zz_181_[24] = memory_SHIFT_RIGHT[7];
    _zz_181_[25] = memory_SHIFT_RIGHT[6];
    _zz_181_[26] = memory_SHIFT_RIGHT[5];
    _zz_181_[27] = memory_SHIFT_RIGHT[4];
    _zz_181_[28] = memory_SHIFT_RIGHT[3];
    _zz_181_[29] = memory_SHIFT_RIGHT[2];
    _zz_181_[30] = memory_SHIFT_RIGHT[1];
    _zz_181_[31] = memory_SHIFT_RIGHT[0];
  end

  always @ (*) begin
    _zz_182_ = 1'b0;
    if(_zz_294_)begin
      if(_zz_295_)begin
        if(_zz_188_)begin
          _zz_182_ = 1'b1;
        end
      end
    end
    if(_zz_296_)begin
      if(_zz_297_)begin
        if(_zz_190_)begin
          _zz_182_ = 1'b1;
        end
      end
    end
    if(_zz_298_)begin
      if(_zz_299_)begin
        if(_zz_192_)begin
          _zz_182_ = 1'b1;
        end
      end
    end
    if((! decode_RS1_USE))begin
      _zz_182_ = 1'b0;
    end
  end

  always @ (*) begin
    _zz_183_ = 1'b0;
    if(_zz_294_)begin
      if(_zz_295_)begin
        if(_zz_189_)begin
          _zz_183_ = 1'b1;
        end
      end
    end
    if(_zz_296_)begin
      if(_zz_297_)begin
        if(_zz_191_)begin
          _zz_183_ = 1'b1;
        end
      end
    end
    if(_zz_298_)begin
      if(_zz_299_)begin
        if(_zz_193_)begin
          _zz_183_ = 1'b1;
        end
      end
    end
    if((! decode_RS2_USE))begin
      _zz_183_ = 1'b0;
    end
  end

  assign _zz_184_ = (_zz_63_ && writeBack_arbitration_isFiring);
  assign _zz_188_ = (writeBack_INSTRUCTION[11 : 7] == decode_INSTRUCTION[19 : 15]);
  assign _zz_189_ = (writeBack_INSTRUCTION[11 : 7] == decode_INSTRUCTION[24 : 20]);
  assign _zz_190_ = (memory_INSTRUCTION[11 : 7] == decode_INSTRUCTION[19 : 15]);
  assign _zz_191_ = (memory_INSTRUCTION[11 : 7] == decode_INSTRUCTION[24 : 20]);
  assign _zz_192_ = (execute_INSTRUCTION[11 : 7] == decode_INSTRUCTION[19 : 15]);
  assign _zz_193_ = (execute_INSTRUCTION[11 : 7] == decode_INSTRUCTION[24 : 20]);
  assign execute_MulPlugin_a = execute_SRC1;
  assign execute_MulPlugin_b = execute_SRC2;
  always @ (*) begin
    case(_zz_300_)
      2'b01 : begin
        execute_MulPlugin_aSigned = 1'b1;
      end
      2'b10 : begin
        execute_MulPlugin_aSigned = 1'b1;
      end
      default : begin
        execute_MulPlugin_aSigned = 1'b0;
      end
    endcase
  end

  always @ (*) begin
    case(_zz_300_)
      2'b01 : begin
        execute_MulPlugin_bSigned = 1'b1;
      end
      2'b10 : begin
        execute_MulPlugin_bSigned = 1'b0;
      end
      default : begin
        execute_MulPlugin_bSigned = 1'b0;
      end
    endcase
  end

  assign execute_MulPlugin_aULow = execute_MulPlugin_a[15 : 0];
  assign execute_MulPlugin_bULow = execute_MulPlugin_b[15 : 0];
  assign execute_MulPlugin_aSLow = {1'b0,execute_MulPlugin_a[15 : 0]};
  assign execute_MulPlugin_bSLow = {1'b0,execute_MulPlugin_b[15 : 0]};
  assign execute_MulPlugin_aHigh = {(execute_MulPlugin_aSigned && execute_MulPlugin_a[31]),execute_MulPlugin_a[31 : 16]};
  assign execute_MulPlugin_bHigh = {(execute_MulPlugin_bSigned && execute_MulPlugin_b[31]),execute_MulPlugin_b[31 : 16]};
  assign _zz_44_ = (execute_MulPlugin_aULow * execute_MulPlugin_bULow);
  assign _zz_43_ = ($signed(execute_MulPlugin_aSLow) * $signed(execute_MulPlugin_bHigh));
  assign _zz_42_ = ($signed(execute_MulPlugin_aHigh) * $signed(execute_MulPlugin_bSLow));
  assign _zz_41_ = ($signed(execute_MulPlugin_aHigh) * $signed(execute_MulPlugin_bHigh));
  assign _zz_40_ = ($signed(_zz_389_) + $signed(_zz_397_));
  assign writeBack_MulPlugin_result = ($signed(_zz_398_) + $signed(_zz_399_));
  always @ (*) begin
    memory_DivPlugin_div_counter_willIncrement = 1'b0;
    if(_zz_274_)begin
      if(_zz_282_)begin
        memory_DivPlugin_div_counter_willIncrement = 1'b1;
      end
    end
  end

  always @ (*) begin
    memory_DivPlugin_div_counter_willClear = 1'b0;
    if(_zz_301_)begin
      memory_DivPlugin_div_counter_willClear = 1'b1;
    end
  end

  assign memory_DivPlugin_div_counter_willOverflowIfInc = (memory_DivPlugin_div_counter_value == (6'b100001));
  assign memory_DivPlugin_div_counter_willOverflow = (memory_DivPlugin_div_counter_willOverflowIfInc && memory_DivPlugin_div_counter_willIncrement);
  always @ (*) begin
    if(memory_DivPlugin_div_counter_willOverflow)begin
      memory_DivPlugin_div_counter_valueNext = (6'b000000);
    end else begin
      memory_DivPlugin_div_counter_valueNext = (memory_DivPlugin_div_counter_value + _zz_403_);
    end
    if(memory_DivPlugin_div_counter_willClear)begin
      memory_DivPlugin_div_counter_valueNext = (6'b000000);
    end
  end

  assign _zz_194_ = memory_DivPlugin_rs1[31 : 0];
  assign _zz_195_ = {memory_DivPlugin_accumulator[31 : 0],_zz_194_[31]};
  assign _zz_196_ = (_zz_195_ - _zz_404_);
  assign _zz_197_ = (memory_INSTRUCTION[13] ? memory_DivPlugin_accumulator[31 : 0] : memory_DivPlugin_rs1[31 : 0]);
  assign _zz_198_ = (execute_RS2[31] && execute_IS_RS2_SIGNED);
  assign _zz_199_ = (1'b0 || ((execute_IS_DIV && execute_RS1[31]) && execute_IS_RS1_SIGNED));
  always @ (*) begin
    _zz_200_[32] = (execute_IS_RS1_SIGNED && execute_RS1[31]);
    _zz_200_[31 : 0] = execute_RS1;
  end

  always @ (*) begin
    CsrPlugin_privilege = (2'b11);
    if(CsrPlugin_forceMachineWire)begin
      CsrPlugin_privilege = (2'b11);
    end
  end

  assign CsrPlugin_misa_base = (2'b01);
  assign CsrPlugin_misa_extensions = (26'b00000000000000000001000010);
  assign CsrPlugin_mtvec_mode = (2'b00);
  assign CsrPlugin_mtvec_base = (30'b100000000000000000000000001000);
  assign CsrPlugin_exceptionPortCtrl_exceptionTargetPrivilegeUncapped = (2'b11);
  assign CsrPlugin_exceptionPortCtrl_exceptionTargetPrivilege = ((CsrPlugin_privilege < CsrPlugin_exceptionPortCtrl_exceptionTargetPrivilegeUncapped) ? CsrPlugin_exceptionPortCtrl_exceptionTargetPrivilegeUncapped : CsrPlugin_privilege);
  assign _zz_201_ = {decodeExceptionPort_valid,IBusCachedPlugin_decodeExceptionPort_valid};
  assign _zz_202_ = _zz_417_[0];
  always @ (*) begin
    CsrPlugin_exceptionPortCtrl_exceptionValids_decode = CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_decode;
    if(_zz_279_)begin
      CsrPlugin_exceptionPortCtrl_exceptionValids_decode = 1'b1;
    end
    if(decode_arbitration_isFlushed)begin
      CsrPlugin_exceptionPortCtrl_exceptionValids_decode = 1'b0;
    end
  end

  always @ (*) begin
    CsrPlugin_exceptionPortCtrl_exceptionValids_execute = CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_execute;
    if(execute_arbitration_isFlushed)begin
      CsrPlugin_exceptionPortCtrl_exceptionValids_execute = 1'b0;
    end
  end

  always @ (*) begin
    CsrPlugin_exceptionPortCtrl_exceptionValids_memory = CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_memory;
    if(BranchPlugin_branchExceptionPort_valid)begin
      CsrPlugin_exceptionPortCtrl_exceptionValids_memory = 1'b1;
    end
    if(memory_arbitration_isFlushed)begin
      CsrPlugin_exceptionPortCtrl_exceptionValids_memory = 1'b0;
    end
  end

  always @ (*) begin
    CsrPlugin_exceptionPortCtrl_exceptionValids_writeBack = CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_writeBack;
    if(DBusCachedPlugin_exceptionBus_valid)begin
      CsrPlugin_exceptionPortCtrl_exceptionValids_writeBack = 1'b1;
    end
    if(writeBack_arbitration_isFlushed)begin
      CsrPlugin_exceptionPortCtrl_exceptionValids_writeBack = 1'b0;
    end
  end

  assign CsrPlugin_exceptionPendings_0 = CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_decode;
  assign CsrPlugin_exceptionPendings_1 = CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_execute;
  assign CsrPlugin_exceptionPendings_2 = CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_memory;
  assign CsrPlugin_exceptionPendings_3 = CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_writeBack;
  always @ (*) begin
    CsrPlugin_interrupt = 1'b0;
    if(_zz_302_)begin
      if(_zz_303_)begin
        CsrPlugin_interrupt = 1'b1;
      end
      if(_zz_304_)begin
        CsrPlugin_interrupt = 1'b1;
      end
      if(_zz_305_)begin
        CsrPlugin_interrupt = 1'b1;
      end
    end
    if((! CsrPlugin_allowInterrupts))begin
      CsrPlugin_interrupt = 1'b0;
    end
  end

  always @ (*) begin
    CsrPlugin_interruptCode = (4'bxxxx);
    if(_zz_302_)begin
      if(_zz_303_)begin
        CsrPlugin_interruptCode = (4'b0111);
      end
      if(_zz_304_)begin
        CsrPlugin_interruptCode = (4'b0011);
      end
      if(_zz_305_)begin
        CsrPlugin_interruptCode = (4'b1011);
      end
    end
  end

  always @ (*) begin
    CsrPlugin_interruptTargetPrivilege = (2'bxx);
    if(_zz_302_)begin
      if(_zz_303_)begin
        CsrPlugin_interruptTargetPrivilege = (2'b11);
      end
      if(_zz_304_)begin
        CsrPlugin_interruptTargetPrivilege = (2'b11);
      end
      if(_zz_305_)begin
        CsrPlugin_interruptTargetPrivilege = (2'b11);
      end
    end
  end

  assign CsrPlugin_exception = (CsrPlugin_exceptionPortCtrl_exceptionValids_writeBack && CsrPlugin_allowException);
  assign CsrPlugin_lastStageWasWfi = 1'b0;
  always @ (*) begin
    CsrPlugin_pipelineLiberator_done = ((! ({writeBack_arbitration_isValid,{memory_arbitration_isValid,execute_arbitration_isValid}} != (3'b000))) && IBusCachedPlugin_pcValids_3);
    if(({CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_writeBack,{CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_memory,CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_execute}} != (3'b000)))begin
      CsrPlugin_pipelineLiberator_done = 1'b0;
    end
    if(CsrPlugin_hadException)begin
      CsrPlugin_pipelineLiberator_done = 1'b0;
    end
  end

  assign CsrPlugin_interruptJump = (CsrPlugin_interrupt && CsrPlugin_pipelineLiberator_done);
  always @ (*) begin
    CsrPlugin_targetPrivilege = CsrPlugin_interruptTargetPrivilege;
    if(CsrPlugin_hadException)begin
      CsrPlugin_targetPrivilege = CsrPlugin_exceptionPortCtrl_exceptionTargetPrivilege;
    end
  end

  always @ (*) begin
    CsrPlugin_trapCause = CsrPlugin_interruptCode;
    if(CsrPlugin_hadException)begin
      CsrPlugin_trapCause = CsrPlugin_exceptionPortCtrl_exceptionContext_code;
    end
  end

  always @ (*) begin
    CsrPlugin_xtvec_mode = (2'bxx);
    case(CsrPlugin_targetPrivilege)
      2'b11 : begin
        CsrPlugin_xtvec_mode = CsrPlugin_mtvec_mode;
      end
      default : begin
      end
    endcase
  end

  always @ (*) begin
    CsrPlugin_xtvec_base = (30'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx);
    case(CsrPlugin_targetPrivilege)
      2'b11 : begin
        CsrPlugin_xtvec_base = CsrPlugin_mtvec_base;
      end
      default : begin
      end
    endcase
  end

  assign contextSwitching = CsrPlugin_jumpInterface_valid;
  assign _zz_38_ = (! (((decode_INSTRUCTION[14 : 13] == (2'b01)) && (decode_INSTRUCTION[19 : 15] == (5'b00000))) || ((decode_INSTRUCTION[14 : 13] == (2'b11)) && (decode_INSTRUCTION[19 : 15] == (5'b00000)))));
  assign _zz_37_ = (decode_INSTRUCTION[13 : 7] != (7'b0100000));
  assign execute_CsrPlugin_inWfi = 1'b0;
  assign execute_CsrPlugin_blockedBySideEffects = ({writeBack_arbitration_isValid,memory_arbitration_isValid} != (2'b00));
  always @ (*) begin
    execute_CsrPlugin_illegalAccess = 1'b1;
    case(execute_CsrPlugin_csrAddress)
      12'b001100000000 : begin
        execute_CsrPlugin_illegalAccess = 1'b0;
      end
      12'b000100000000 : begin
        execute_CsrPlugin_illegalAccess = 1'b0;
      end
      12'b001101000001 : begin
        execute_CsrPlugin_illegalAccess = 1'b0;
      end
      12'b001101000100 : begin
        execute_CsrPlugin_illegalAccess = 1'b0;
      end
      12'b000110000000 : begin
        execute_CsrPlugin_illegalAccess = 1'b0;
      end
      12'b001101000011 : begin
        if(execute_CSR_READ_OPCODE)begin
          execute_CsrPlugin_illegalAccess = 1'b0;
        end
      end
      12'b001100000100 : begin
        execute_CsrPlugin_illegalAccess = 1'b0;
      end
      12'b001101000010 : begin
        if(execute_CSR_READ_OPCODE)begin
          execute_CsrPlugin_illegalAccess = 1'b0;
        end
      end
      default : begin
      end
    endcase
    if((CsrPlugin_privilege < execute_CsrPlugin_csrAddress[9 : 8]))begin
      execute_CsrPlugin_illegalAccess = 1'b1;
    end
    if(((! execute_arbitration_isValid) || (! execute_IS_CSR)))begin
      execute_CsrPlugin_illegalAccess = 1'b0;
    end
  end

  always @ (*) begin
    execute_CsrPlugin_illegalInstruction = 1'b0;
    if((execute_arbitration_isValid && (execute_ENV_CTRL == `EnvCtrlEnum_defaultEncoding_XRET)))begin
      if((CsrPlugin_privilege < execute_INSTRUCTION[29 : 28]))begin
        execute_CsrPlugin_illegalInstruction = 1'b1;
      end
    end
  end

  always @ (*) begin
    execute_CsrPlugin_readData = (32'b00000000000000000000000000000000);
    case(execute_CsrPlugin_csrAddress)
      12'b001100000000 : begin
        execute_CsrPlugin_readData[19 : 19] = MmuPlugin_status_mxr;
        execute_CsrPlugin_readData[18 : 18] = MmuPlugin_status_sum;
        execute_CsrPlugin_readData[17 : 17] = MmuPlugin_status_mprv;
        execute_CsrPlugin_readData[12 : 11] = CsrPlugin_mstatus_MPP;
        execute_CsrPlugin_readData[7 : 7] = CsrPlugin_mstatus_MPIE;
        execute_CsrPlugin_readData[3 : 3] = CsrPlugin_mstatus_MIE;
      end
      12'b000100000000 : begin
        execute_CsrPlugin_readData[19 : 19] = MmuPlugin_status_mxr;
        execute_CsrPlugin_readData[18 : 18] = MmuPlugin_status_sum;
        execute_CsrPlugin_readData[17 : 17] = MmuPlugin_status_mprv;
      end
      12'b001101000001 : begin
        execute_CsrPlugin_readData[31 : 0] = CsrPlugin_mepc;
      end
      12'b001101000100 : begin
        execute_CsrPlugin_readData[11 : 11] = CsrPlugin_mip_MEIP;
        execute_CsrPlugin_readData[7 : 7] = CsrPlugin_mip_MTIP;
        execute_CsrPlugin_readData[3 : 3] = CsrPlugin_mip_MSIP;
      end
      12'b000110000000 : begin
        execute_CsrPlugin_readData[31 : 31] = MmuPlugin_satp_mode;
        execute_CsrPlugin_readData[19 : 0] = MmuPlugin_satp_ppn;
      end
      12'b001101000011 : begin
        execute_CsrPlugin_readData[31 : 0] = CsrPlugin_mtval;
      end
      12'b001100000100 : begin
        execute_CsrPlugin_readData[11 : 11] = CsrPlugin_mie_MEIE;
        execute_CsrPlugin_readData[7 : 7] = CsrPlugin_mie_MTIE;
        execute_CsrPlugin_readData[3 : 3] = CsrPlugin_mie_MSIE;
      end
      12'b001101000010 : begin
        execute_CsrPlugin_readData[31 : 31] = CsrPlugin_mcause_interrupt;
        execute_CsrPlugin_readData[3 : 0] = CsrPlugin_mcause_exceptionCode;
      end
      default : begin
      end
    endcase
  end

  assign execute_CsrPlugin_writeInstruction = ((execute_arbitration_isValid && execute_IS_CSR) && execute_CSR_WRITE_OPCODE);
  assign execute_CsrPlugin_readInstruction = ((execute_arbitration_isValid && execute_IS_CSR) && execute_CSR_READ_OPCODE);
  assign execute_CsrPlugin_writeEnable = ((execute_CsrPlugin_writeInstruction && (! execute_CsrPlugin_blockedBySideEffects)) && (! execute_arbitration_isStuckByOthers));
  assign execute_CsrPlugin_readEnable = ((execute_CsrPlugin_readInstruction && (! execute_CsrPlugin_blockedBySideEffects)) && (! execute_arbitration_isStuckByOthers));
  assign execute_CsrPlugin_readToWriteData = execute_CsrPlugin_readData;
  always @ (*) begin
    case(_zz_321_)
      1'b0 : begin
        execute_CsrPlugin_writeData = execute_SRC1;
      end
      default : begin
        execute_CsrPlugin_writeData = (execute_INSTRUCTION[12] ? (execute_CsrPlugin_readToWriteData & (~ execute_SRC1)) : (execute_CsrPlugin_readToWriteData | execute_SRC1));
      end
    endcase
  end

  assign execute_CsrPlugin_csrAddress = execute_INSTRUCTION[31 : 20];
  always @ (*) begin
    debug_bus_cmd_ready = 1'b1;
    if(debug_bus_cmd_valid)begin
      case(_zz_306_)
        6'b000000 : begin
        end
        6'b000001 : begin
          if(debug_bus_cmd_payload_wr)begin
            debug_bus_cmd_ready = IBusCachedPlugin_injectionPort_ready;
          end
        end
        default : begin
        end
      endcase
    end
  end

  always @ (*) begin
    debug_bus_rsp_data = DebugPlugin_busReadDataReg;
    if((! _zz_203_))begin
      debug_bus_rsp_data[0] = DebugPlugin_resetIt;
      debug_bus_rsp_data[1] = DebugPlugin_haltIt;
      debug_bus_rsp_data[2] = DebugPlugin_isPipBusy;
      debug_bus_rsp_data[3] = DebugPlugin_haltedByBreak;
      debug_bus_rsp_data[4] = DebugPlugin_stepIt;
    end
  end

  always @ (*) begin
    IBusCachedPlugin_injectionPort_valid = 1'b0;
    if(debug_bus_cmd_valid)begin
      case(_zz_306_)
        6'b000000 : begin
        end
        6'b000001 : begin
          if(debug_bus_cmd_payload_wr)begin
            IBusCachedPlugin_injectionPort_valid = 1'b1;
          end
        end
        default : begin
        end
      endcase
    end
  end

  assign IBusCachedPlugin_injectionPort_payload = debug_bus_cmd_payload_data;
  assign _zz_34_ = ((! DebugPlugin_haltIt) && (decode_IS_EBREAK || 1'b0));
  assign debug_resetOut = DebugPlugin_resetIt_regNext;
  assign _zz_33_ = IBusCachedPlugin_decodePrediction_cmd_hadBranch;
  assign execute_BranchPlugin_eq = (execute_SRC1 == execute_SRC2);
  assign _zz_204_ = execute_INSTRUCTION[14 : 12];
  always @ (*) begin
    if((_zz_204_ == (3'b000))) begin
        _zz_205_ = execute_BranchPlugin_eq;
    end else if((_zz_204_ == (3'b001))) begin
        _zz_205_ = (! execute_BranchPlugin_eq);
    end else if((((_zz_204_ & (3'b101)) == (3'b101)))) begin
        _zz_205_ = (! execute_SRC_LESS);
    end else begin
        _zz_205_ = execute_SRC_LESS;
    end
  end

  always @ (*) begin
    case(execute_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_INC : begin
        _zz_206_ = 1'b0;
      end
      `BranchCtrlEnum_defaultEncoding_JAL : begin
        _zz_206_ = 1'b1;
      end
      `BranchCtrlEnum_defaultEncoding_JALR : begin
        _zz_206_ = 1'b1;
      end
      default : begin
        _zz_206_ = _zz_205_;
      end
    endcase
  end

  assign _zz_32_ = _zz_206_;
  assign _zz_207_ = _zz_419_[11];
  always @ (*) begin
    _zz_208_[19] = _zz_207_;
    _zz_208_[18] = _zz_207_;
    _zz_208_[17] = _zz_207_;
    _zz_208_[16] = _zz_207_;
    _zz_208_[15] = _zz_207_;
    _zz_208_[14] = _zz_207_;
    _zz_208_[13] = _zz_207_;
    _zz_208_[12] = _zz_207_;
    _zz_208_[11] = _zz_207_;
    _zz_208_[10] = _zz_207_;
    _zz_208_[9] = _zz_207_;
    _zz_208_[8] = _zz_207_;
    _zz_208_[7] = _zz_207_;
    _zz_208_[6] = _zz_207_;
    _zz_208_[5] = _zz_207_;
    _zz_208_[4] = _zz_207_;
    _zz_208_[3] = _zz_207_;
    _zz_208_[2] = _zz_207_;
    _zz_208_[1] = _zz_207_;
    _zz_208_[0] = _zz_207_;
  end

  assign _zz_209_ = _zz_420_[19];
  always @ (*) begin
    _zz_210_[10] = _zz_209_;
    _zz_210_[9] = _zz_209_;
    _zz_210_[8] = _zz_209_;
    _zz_210_[7] = _zz_209_;
    _zz_210_[6] = _zz_209_;
    _zz_210_[5] = _zz_209_;
    _zz_210_[4] = _zz_209_;
    _zz_210_[3] = _zz_209_;
    _zz_210_[2] = _zz_209_;
    _zz_210_[1] = _zz_209_;
    _zz_210_[0] = _zz_209_;
  end

  assign _zz_211_ = _zz_421_[11];
  always @ (*) begin
    _zz_212_[18] = _zz_211_;
    _zz_212_[17] = _zz_211_;
    _zz_212_[16] = _zz_211_;
    _zz_212_[15] = _zz_211_;
    _zz_212_[14] = _zz_211_;
    _zz_212_[13] = _zz_211_;
    _zz_212_[12] = _zz_211_;
    _zz_212_[11] = _zz_211_;
    _zz_212_[10] = _zz_211_;
    _zz_212_[9] = _zz_211_;
    _zz_212_[8] = _zz_211_;
    _zz_212_[7] = _zz_211_;
    _zz_212_[6] = _zz_211_;
    _zz_212_[5] = _zz_211_;
    _zz_212_[4] = _zz_211_;
    _zz_212_[3] = _zz_211_;
    _zz_212_[2] = _zz_211_;
    _zz_212_[1] = _zz_211_;
    _zz_212_[0] = _zz_211_;
  end

  always @ (*) begin
    case(execute_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_JALR : begin
        _zz_213_ = (_zz_422_[1] ^ execute_RS1[1]);
      end
      `BranchCtrlEnum_defaultEncoding_JAL : begin
        _zz_213_ = _zz_423_[1];
      end
      default : begin
        _zz_213_ = _zz_424_[1];
      end
    endcase
  end

  assign execute_BranchPlugin_missAlignedTarget = (execute_BRANCH_COND_RESULT && _zz_213_);
  assign _zz_30_ = ((execute_PREDICTION_HAD_BRANCHED2 != execute_BRANCH_COND_RESULT) || execute_BranchPlugin_missAlignedTarget);
  always @ (*) begin
    case(execute_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_JALR : begin
        execute_BranchPlugin_branch_src1 = execute_RS1;
      end
      default : begin
        execute_BranchPlugin_branch_src1 = execute_PC;
      end
    endcase
  end

  assign _zz_214_ = _zz_425_[11];
  always @ (*) begin
    _zz_215_[19] = _zz_214_;
    _zz_215_[18] = _zz_214_;
    _zz_215_[17] = _zz_214_;
    _zz_215_[16] = _zz_214_;
    _zz_215_[15] = _zz_214_;
    _zz_215_[14] = _zz_214_;
    _zz_215_[13] = _zz_214_;
    _zz_215_[12] = _zz_214_;
    _zz_215_[11] = _zz_214_;
    _zz_215_[10] = _zz_214_;
    _zz_215_[9] = _zz_214_;
    _zz_215_[8] = _zz_214_;
    _zz_215_[7] = _zz_214_;
    _zz_215_[6] = _zz_214_;
    _zz_215_[5] = _zz_214_;
    _zz_215_[4] = _zz_214_;
    _zz_215_[3] = _zz_214_;
    _zz_215_[2] = _zz_214_;
    _zz_215_[1] = _zz_214_;
    _zz_215_[0] = _zz_214_;
  end

  always @ (*) begin
    case(execute_BRANCH_CTRL)
      `BranchCtrlEnum_defaultEncoding_JALR : begin
        execute_BranchPlugin_branch_src2 = {_zz_215_,execute_INSTRUCTION[31 : 20]};
      end
      default : begin
        execute_BranchPlugin_branch_src2 = ((execute_BRANCH_CTRL == `BranchCtrlEnum_defaultEncoding_JAL) ? {{_zz_217_,{{{_zz_630_,execute_INSTRUCTION[19 : 12]},execute_INSTRUCTION[20]},execute_INSTRUCTION[30 : 21]}},1'b0} : {{_zz_219_,{{{_zz_631_,_zz_632_},execute_INSTRUCTION[30 : 25]},execute_INSTRUCTION[11 : 8]}},1'b0});
        if(execute_PREDICTION_HAD_BRANCHED2)begin
          execute_BranchPlugin_branch_src2 = {29'd0, _zz_428_};
        end
      end
    endcase
  end

  assign _zz_216_ = _zz_426_[19];
  always @ (*) begin
    _zz_217_[10] = _zz_216_;
    _zz_217_[9] = _zz_216_;
    _zz_217_[8] = _zz_216_;
    _zz_217_[7] = _zz_216_;
    _zz_217_[6] = _zz_216_;
    _zz_217_[5] = _zz_216_;
    _zz_217_[4] = _zz_216_;
    _zz_217_[3] = _zz_216_;
    _zz_217_[2] = _zz_216_;
    _zz_217_[1] = _zz_216_;
    _zz_217_[0] = _zz_216_;
  end

  assign _zz_218_ = _zz_427_[11];
  always @ (*) begin
    _zz_219_[18] = _zz_218_;
    _zz_219_[17] = _zz_218_;
    _zz_219_[16] = _zz_218_;
    _zz_219_[15] = _zz_218_;
    _zz_219_[14] = _zz_218_;
    _zz_219_[13] = _zz_218_;
    _zz_219_[12] = _zz_218_;
    _zz_219_[11] = _zz_218_;
    _zz_219_[10] = _zz_218_;
    _zz_219_[9] = _zz_218_;
    _zz_219_[8] = _zz_218_;
    _zz_219_[7] = _zz_218_;
    _zz_219_[6] = _zz_218_;
    _zz_219_[5] = _zz_218_;
    _zz_219_[4] = _zz_218_;
    _zz_219_[3] = _zz_218_;
    _zz_219_[2] = _zz_218_;
    _zz_219_[1] = _zz_218_;
    _zz_219_[0] = _zz_218_;
  end

  assign execute_BranchPlugin_branchAdder = (execute_BranchPlugin_branch_src1 + execute_BranchPlugin_branch_src2);
  assign _zz_29_ = {execute_BranchPlugin_branchAdder[31 : 1],(1'b0)};
  assign BranchPlugin_jumpInterface_valid = ((memory_arbitration_isValid && (! memory_arbitration_isStuckByOthers)) && memory_BRANCH_DO);
  assign BranchPlugin_jumpInterface_payload = memory_BRANCH_CALC;
  assign BranchPlugin_branchExceptionPort_valid = (memory_arbitration_isValid && (memory_BRANCH_DO && memory_BRANCH_CALC[1]));
  assign BranchPlugin_branchExceptionPort_payload_code = (4'b0000);
  assign BranchPlugin_branchExceptionPort_payload_badAddr = memory_BRANCH_CALC;
  assign IBusCachedPlugin_decodePrediction_rsp_wasWrong = BranchPlugin_jumpInterface_valid;
  assign _zz_28_ = decode_BRANCH_CTRL;
  assign _zz_26_ = execute_BRANCH_CTRL;
  assign _zz_101_ = _zz_75_;
  assign _zz_31_ = decode_to_execute_BRANCH_CTRL;
  assign _zz_102_ = execute_to_memory_BRANCH_CTRL;
  assign _zz_24_ = decode_ENV_CTRL;
  assign _zz_21_ = execute_ENV_CTRL;
  assign _zz_19_ = memory_ENV_CTRL;
  assign _zz_22_ = _zz_90_;
  assign _zz_36_ = decode_to_execute_ENV_CTRL;
  assign _zz_35_ = execute_to_memory_ENV_CTRL;
  assign _zz_39_ = memory_to_writeBack_ENV_CTRL;
  assign _zz_17_ = decode_ALU_CTRL;
  assign _zz_15_ = _zz_84_;
  assign _zz_59_ = decode_to_execute_ALU_CTRL;
  assign _zz_14_ = decode_SRC2_CTRL;
  assign _zz_12_ = _zz_91_;
  assign _zz_54_ = decode_to_execute_SRC2_CTRL;
  assign _zz_11_ = decode_SRC1_CTRL;
  assign _zz_9_ = _zz_68_;
  assign _zz_56_ = decode_to_execute_SRC1_CTRL;
  assign _zz_8_ = decode_ALU_BITWISE_CTRL;
  assign _zz_6_ = _zz_87_;
  assign _zz_61_ = decode_to_execute_ALU_BITWISE_CTRL;
  assign _zz_5_ = decode_SHIFT_CTRL;
  assign _zz_2_ = execute_SHIFT_CTRL;
  assign _zz_3_ = _zz_78_;
  assign _zz_49_ = decode_to_execute_SHIFT_CTRL;
  assign _zz_47_ = execute_to_memory_SHIFT_CTRL;
  assign decode_arbitration_isFlushed = ({writeBack_arbitration_flushAll,{memory_arbitration_flushAll,{execute_arbitration_flushAll,decode_arbitration_flushAll}}} != (4'b0000));
  assign execute_arbitration_isFlushed = ({writeBack_arbitration_flushAll,{memory_arbitration_flushAll,execute_arbitration_flushAll}} != (3'b000));
  assign memory_arbitration_isFlushed = ({writeBack_arbitration_flushAll,memory_arbitration_flushAll} != (2'b00));
  assign writeBack_arbitration_isFlushed = (writeBack_arbitration_flushAll != (1'b0));
  assign decode_arbitration_isStuckByOthers = (decode_arbitration_haltByOther || (((1'b0 || execute_arbitration_isStuck) || memory_arbitration_isStuck) || writeBack_arbitration_isStuck));
  assign decode_arbitration_isStuck = (decode_arbitration_haltItself || decode_arbitration_isStuckByOthers);
  assign decode_arbitration_isMoving = ((! decode_arbitration_isStuck) && (! decode_arbitration_removeIt));
  assign decode_arbitration_isFiring = ((decode_arbitration_isValid && (! decode_arbitration_isStuck)) && (! decode_arbitration_removeIt));
  assign execute_arbitration_isStuckByOthers = (execute_arbitration_haltByOther || ((1'b0 || memory_arbitration_isStuck) || writeBack_arbitration_isStuck));
  assign execute_arbitration_isStuck = (execute_arbitration_haltItself || execute_arbitration_isStuckByOthers);
  assign execute_arbitration_isMoving = ((! execute_arbitration_isStuck) && (! execute_arbitration_removeIt));
  assign execute_arbitration_isFiring = ((execute_arbitration_isValid && (! execute_arbitration_isStuck)) && (! execute_arbitration_removeIt));
  assign memory_arbitration_isStuckByOthers = (memory_arbitration_haltByOther || (1'b0 || writeBack_arbitration_isStuck));
  assign memory_arbitration_isStuck = (memory_arbitration_haltItself || memory_arbitration_isStuckByOthers);
  assign memory_arbitration_isMoving = ((! memory_arbitration_isStuck) && (! memory_arbitration_removeIt));
  assign memory_arbitration_isFiring = ((memory_arbitration_isValid && (! memory_arbitration_isStuck)) && (! memory_arbitration_removeIt));
  assign writeBack_arbitration_isStuckByOthers = (writeBack_arbitration_haltByOther || 1'b0);
  assign writeBack_arbitration_isStuck = (writeBack_arbitration_haltItself || writeBack_arbitration_isStuckByOthers);
  assign writeBack_arbitration_isMoving = ((! writeBack_arbitration_isStuck) && (! writeBack_arbitration_removeIt));
  assign writeBack_arbitration_isFiring = ((writeBack_arbitration_isValid && (! writeBack_arbitration_isStuck)) && (! writeBack_arbitration_removeIt));
  always @ (*) begin
    IBusCachedPlugin_injectionPort_ready = 1'b0;
    case(_zz_220_)
      3'b000 : begin
      end
      3'b001 : begin
      end
      3'b010 : begin
      end
      3'b011 : begin
      end
      3'b100 : begin
        IBusCachedPlugin_injectionPort_ready = 1'b1;
      end
      default : begin
      end
    endcase
  end

  always @ (posedge clk or posedge reset) begin
    if (reset) begin
      IBusCachedPlugin_fetchPc_pcReg <= (32'b10000000000000000000000000000000);
      IBusCachedPlugin_fetchPc_inc <= 1'b0;
      _zz_119_ <= 1'b0;
      _zz_125_ <= 1'b0;
      _zz_127_ <= 1'b0;
      IBusCachedPlugin_injector_nextPcCalc_valids_0 <= 1'b0;
      IBusCachedPlugin_injector_nextPcCalc_valids_1 <= 1'b0;
      IBusCachedPlugin_injector_nextPcCalc_valids_2 <= 1'b0;
      IBusCachedPlugin_injector_nextPcCalc_valids_3 <= 1'b0;
      IBusCachedPlugin_injector_nextPcCalc_valids_4 <= 1'b0;
      IBusCachedPlugin_injector_decodeRemoved <= 1'b0;
      MmuPlugin_status_sum <= 1'b0;
      MmuPlugin_status_mxr <= 1'b0;
      MmuPlugin_status_mprv <= 1'b0;
      MmuPlugin_satp_mode <= 1'b0;
      MmuPlugin_ports_0_cache_0_valid <= 1'b0;
      MmuPlugin_ports_0_cache_1_valid <= 1'b0;
      MmuPlugin_ports_0_cache_2_valid <= 1'b0;
      MmuPlugin_ports_0_cache_3_valid <= 1'b0;
      MmuPlugin_ports_0_cache_4_valid <= 1'b0;
      MmuPlugin_ports_0_cache_5_valid <= 1'b0;
      MmuPlugin_ports_0_entryToReplace_value <= (3'b000);
      MmuPlugin_ports_1_cache_0_valid <= 1'b0;
      MmuPlugin_ports_1_cache_1_valid <= 1'b0;
      MmuPlugin_ports_1_cache_2_valid <= 1'b0;
      MmuPlugin_ports_1_cache_3_valid <= 1'b0;
      MmuPlugin_ports_1_entryToReplace_value <= (2'b00);
      MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_IDLE;
      _zz_172_ <= 1'b1;
      _zz_185_ <= 1'b0;
      memory_DivPlugin_div_counter_value <= (6'b000000);
      CsrPlugin_mstatus_MIE <= 1'b0;
      CsrPlugin_mstatus_MPIE <= 1'b0;
      CsrPlugin_mstatus_MPP <= (2'b11);
      CsrPlugin_mie_MEIE <= 1'b0;
      CsrPlugin_mie_MTIE <= 1'b0;
      CsrPlugin_mie_MSIE <= 1'b0;
      CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_decode <= 1'b0;
      CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_execute <= 1'b0;
      CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_memory <= 1'b0;
      CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_writeBack <= 1'b0;
      CsrPlugin_hadException <= 1'b0;
      execute_arbitration_isValid <= 1'b0;
      memory_arbitration_isValid <= 1'b0;
      writeBack_arbitration_isValid <= 1'b0;
      _zz_220_ <= (3'b000);
      execute_to_memory_IS_DBUS_SHARING <= 1'b0;
      memory_to_writeBack_IS_DBUS_SHARING <= 1'b0;
      memory_to_writeBack_REGFILE_WRITE_DATA <= (32'b00000000000000000000000000000000);
      memory_to_writeBack_INSTRUCTION <= (32'b00000000000000000000000000000000);
    end else begin
      if(IBusCachedPlugin_fetchPc_propagatePc)begin
        IBusCachedPlugin_fetchPc_inc <= 1'b0;
      end
      if(IBusCachedPlugin_jump_pcLoad_valid)begin
        IBusCachedPlugin_fetchPc_inc <= 1'b0;
      end
      if(_zz_287_)begin
        IBusCachedPlugin_fetchPc_inc <= 1'b1;
      end
      if(IBusCachedPlugin_fetchPc_samplePcNext)begin
        IBusCachedPlugin_fetchPc_pcReg <= IBusCachedPlugin_fetchPc_pc;
      end
      _zz_119_ <= 1'b1;
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        _zz_125_ <= 1'b0;
      end
      if(_zz_123_)begin
        _zz_125_ <= IBusCachedPlugin_iBusRsp_stages_0_output_valid;
      end
      if(IBusCachedPlugin_iBusRsp_stages_1_output_ready)begin
        _zz_127_ <= IBusCachedPlugin_iBusRsp_stages_1_output_valid;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        _zz_127_ <= 1'b0;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_0 <= 1'b0;
      end
      if((! (! IBusCachedPlugin_iBusRsp_stages_1_input_ready)))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_0 <= 1'b1;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_1 <= 1'b0;
      end
      if((! (! IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_ready)))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_1 <= IBusCachedPlugin_injector_nextPcCalc_valids_0;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_1 <= 1'b0;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_2 <= 1'b0;
      end
      if((! execute_arbitration_isStuck))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_2 <= IBusCachedPlugin_injector_nextPcCalc_valids_1;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_2 <= 1'b0;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_3 <= 1'b0;
      end
      if((! memory_arbitration_isStuck))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_3 <= IBusCachedPlugin_injector_nextPcCalc_valids_2;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_3 <= 1'b0;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_4 <= 1'b0;
      end
      if((! writeBack_arbitration_isStuck))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_4 <= IBusCachedPlugin_injector_nextPcCalc_valids_3;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_nextPcCalc_valids_4 <= 1'b0;
      end
      if(decode_arbitration_removeIt)begin
        IBusCachedPlugin_injector_decodeRemoved <= 1'b1;
      end
      if((IBusCachedPlugin_jump_pcLoad_valid || IBusCachedPlugin_fetcherflushIt))begin
        IBusCachedPlugin_injector_decodeRemoved <= 1'b0;
      end
      MmuPlugin_ports_0_entryToReplace_value <= MmuPlugin_ports_0_entryToReplace_valueNext;
      if(contextSwitching)begin
        if(MmuPlugin_ports_0_cache_0_exception)begin
          MmuPlugin_ports_0_cache_0_valid <= 1'b0;
        end
        if(MmuPlugin_ports_0_cache_1_exception)begin
          MmuPlugin_ports_0_cache_1_valid <= 1'b0;
        end
        if(MmuPlugin_ports_0_cache_2_exception)begin
          MmuPlugin_ports_0_cache_2_valid <= 1'b0;
        end
        if(MmuPlugin_ports_0_cache_3_exception)begin
          MmuPlugin_ports_0_cache_3_valid <= 1'b0;
        end
        if(MmuPlugin_ports_0_cache_4_exception)begin
          MmuPlugin_ports_0_cache_4_valid <= 1'b0;
        end
        if(MmuPlugin_ports_0_cache_5_exception)begin
          MmuPlugin_ports_0_cache_5_valid <= 1'b0;
        end
      end
      MmuPlugin_ports_1_entryToReplace_value <= MmuPlugin_ports_1_entryToReplace_valueNext;
      if(contextSwitching)begin
        if(MmuPlugin_ports_1_cache_0_exception)begin
          MmuPlugin_ports_1_cache_0_valid <= 1'b0;
        end
        if(MmuPlugin_ports_1_cache_1_exception)begin
          MmuPlugin_ports_1_cache_1_valid <= 1'b0;
        end
        if(MmuPlugin_ports_1_cache_2_exception)begin
          MmuPlugin_ports_1_cache_2_valid <= 1'b0;
        end
        if(MmuPlugin_ports_1_cache_3_exception)begin
          MmuPlugin_ports_1_cache_3_valid <= 1'b0;
        end
      end
      case(MmuPlugin_shared_state_1_)
        `MmuPlugin_shared_State_defaultEncoding_IDLE : begin
          if(_zz_307_)begin
            MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_L1_CMD;
          end
          if(_zz_308_)begin
            MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_L1_CMD;
          end
        end
        `MmuPlugin_shared_State_defaultEncoding_L1_CMD : begin
          if(MmuPlugin_dBusAccess_cmd_ready)begin
            MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_L1_RSP;
          end
        end
        `MmuPlugin_shared_State_defaultEncoding_L1_RSP : begin
          if(MmuPlugin_dBusAccess_rsp_valid)begin
            MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_L0_CMD;
            if((MmuPlugin_shared_dBusRsp_leaf || MmuPlugin_shared_dBusRsp_exception))begin
              MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_IDLE;
            end
            if(MmuPlugin_dBusAccess_rsp_payload_redo)begin
              MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_L1_CMD;
            end
          end
        end
        `MmuPlugin_shared_State_defaultEncoding_L0_CMD : begin
          if(MmuPlugin_dBusAccess_cmd_ready)begin
            MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_L0_RSP;
          end
        end
        default : begin
          if(MmuPlugin_dBusAccess_rsp_valid)begin
            MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_IDLE;
            if(MmuPlugin_dBusAccess_rsp_payload_redo)begin
              MmuPlugin_shared_state_1_ <= `MmuPlugin_shared_State_defaultEncoding_L0_CMD;
            end
          end
        end
      endcase
      if(_zz_291_)begin
        if(_zz_292_)begin
          if(_zz_309_)begin
            MmuPlugin_ports_0_cache_0_valid <= 1'b1;
          end
          if(_zz_310_)begin
            MmuPlugin_ports_0_cache_1_valid <= 1'b1;
          end
          if(_zz_311_)begin
            MmuPlugin_ports_0_cache_2_valid <= 1'b1;
          end
          if(_zz_312_)begin
            MmuPlugin_ports_0_cache_3_valid <= 1'b1;
          end
          if(_zz_313_)begin
            MmuPlugin_ports_0_cache_4_valid <= 1'b1;
          end
          if(_zz_314_)begin
            MmuPlugin_ports_0_cache_5_valid <= 1'b1;
          end
        end
        if(_zz_293_)begin
          if(_zz_315_)begin
            MmuPlugin_ports_1_cache_0_valid <= 1'b1;
          end
          if(_zz_316_)begin
            MmuPlugin_ports_1_cache_1_valid <= 1'b1;
          end
          if(_zz_317_)begin
            MmuPlugin_ports_1_cache_2_valid <= 1'b1;
          end
          if(_zz_318_)begin
            MmuPlugin_ports_1_cache_3_valid <= 1'b1;
          end
        end
      end
      if((writeBack_arbitration_isValid && writeBack_IS_SFENCE_VMA))begin
        MmuPlugin_ports_0_cache_0_valid <= 1'b0;
        MmuPlugin_ports_0_cache_1_valid <= 1'b0;
        MmuPlugin_ports_0_cache_2_valid <= 1'b0;
        MmuPlugin_ports_0_cache_3_valid <= 1'b0;
        MmuPlugin_ports_0_cache_4_valid <= 1'b0;
        MmuPlugin_ports_0_cache_5_valid <= 1'b0;
        MmuPlugin_ports_1_cache_0_valid <= 1'b0;
        MmuPlugin_ports_1_cache_1_valid <= 1'b0;
        MmuPlugin_ports_1_cache_2_valid <= 1'b0;
        MmuPlugin_ports_1_cache_3_valid <= 1'b0;
      end
      _zz_172_ <= 1'b0;
      _zz_185_ <= _zz_184_;
      memory_DivPlugin_div_counter_value <= memory_DivPlugin_div_counter_valueNext;
      if((! decode_arbitration_isStuck))begin
        CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_decode <= 1'b0;
      end else begin
        CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_decode <= CsrPlugin_exceptionPortCtrl_exceptionValids_decode;
      end
      if((! execute_arbitration_isStuck))begin
        CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_execute <= (CsrPlugin_exceptionPortCtrl_exceptionValids_decode && (! decode_arbitration_isStuck));
      end else begin
        CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_execute <= CsrPlugin_exceptionPortCtrl_exceptionValids_execute;
      end
      if((! memory_arbitration_isStuck))begin
        CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_memory <= (CsrPlugin_exceptionPortCtrl_exceptionValids_execute && (! execute_arbitration_isStuck));
      end else begin
        CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_memory <= CsrPlugin_exceptionPortCtrl_exceptionValids_memory;
      end
      if((! writeBack_arbitration_isStuck))begin
        CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_writeBack <= (CsrPlugin_exceptionPortCtrl_exceptionValids_memory && (! memory_arbitration_isStuck));
      end else begin
        CsrPlugin_exceptionPortCtrl_exceptionValidsRegs_writeBack <= 1'b0;
      end
      CsrPlugin_hadException <= CsrPlugin_exception;
      if(_zz_283_)begin
        case(CsrPlugin_targetPrivilege)
          2'b11 : begin
            CsrPlugin_mstatus_MIE <= 1'b0;
            CsrPlugin_mstatus_MPIE <= CsrPlugin_mstatus_MIE;
            CsrPlugin_mstatus_MPP <= CsrPlugin_privilege;
          end
          default : begin
          end
        endcase
      end
      if(_zz_284_)begin
        case(_zz_286_)
          2'b11 : begin
            CsrPlugin_mstatus_MPP <= (2'b00);
            CsrPlugin_mstatus_MIE <= CsrPlugin_mstatus_MPIE;
            CsrPlugin_mstatus_MPIE <= 1'b1;
          end
          default : begin
          end
        endcase
      end
      if((! writeBack_arbitration_isStuck))begin
        memory_to_writeBack_INSTRUCTION <= memory_INSTRUCTION;
      end
      if((! writeBack_arbitration_isStuck))begin
        memory_to_writeBack_REGFILE_WRITE_DATA <= _zz_46_;
      end
      if((! memory_arbitration_isStuck))begin
        execute_to_memory_IS_DBUS_SHARING <= execute_IS_DBUS_SHARING;
      end
      if((! writeBack_arbitration_isStuck))begin
        memory_to_writeBack_IS_DBUS_SHARING <= memory_IS_DBUS_SHARING;
      end
      if(((! execute_arbitration_isStuck) || execute_arbitration_removeIt))begin
        execute_arbitration_isValid <= 1'b0;
      end
      if(((! decode_arbitration_isStuck) && (! decode_arbitration_removeIt)))begin
        execute_arbitration_isValid <= decode_arbitration_isValid;
      end
      if(((! memory_arbitration_isStuck) || memory_arbitration_removeIt))begin
        memory_arbitration_isValid <= 1'b0;
      end
      if(((! execute_arbitration_isStuck) && (! execute_arbitration_removeIt)))begin
        memory_arbitration_isValid <= execute_arbitration_isValid;
      end
      if(((! writeBack_arbitration_isStuck) || writeBack_arbitration_removeIt))begin
        writeBack_arbitration_isValid <= 1'b0;
      end
      if(((! memory_arbitration_isStuck) && (! memory_arbitration_removeIt)))begin
        writeBack_arbitration_isValid <= memory_arbitration_isValid;
      end
      case(_zz_220_)
        3'b000 : begin
          if(IBusCachedPlugin_injectionPort_valid)begin
            _zz_220_ <= (3'b001);
          end
        end
        3'b001 : begin
          _zz_220_ <= (3'b010);
        end
        3'b010 : begin
          _zz_220_ <= (3'b011);
        end
        3'b011 : begin
          if((! decode_arbitration_isStuck))begin
            _zz_220_ <= (3'b100);
          end
        end
        3'b100 : begin
          _zz_220_ <= (3'b000);
        end
        default : begin
        end
      endcase
      if(MmuPlugin_dBusAccess_rsp_valid)begin
        memory_to_writeBack_IS_DBUS_SHARING <= 1'b0;
      end
      case(execute_CsrPlugin_csrAddress)
        12'b001100000000 : begin
          if(execute_CsrPlugin_writeEnable)begin
            MmuPlugin_status_mxr <= _zz_429_[0];
            MmuPlugin_status_sum <= _zz_430_[0];
            MmuPlugin_status_mprv <= _zz_431_[0];
            CsrPlugin_mstatus_MPP <= execute_CsrPlugin_writeData[12 : 11];
            CsrPlugin_mstatus_MPIE <= _zz_432_[0];
            CsrPlugin_mstatus_MIE <= _zz_433_[0];
          end
        end
        12'b000100000000 : begin
          if(execute_CsrPlugin_writeEnable)begin
            MmuPlugin_status_mxr <= _zz_434_[0];
            MmuPlugin_status_sum <= _zz_435_[0];
            MmuPlugin_status_mprv <= _zz_436_[0];
          end
        end
        12'b001101000001 : begin
        end
        12'b001101000100 : begin
        end
        12'b000110000000 : begin
          if(execute_CsrPlugin_writeEnable)begin
            MmuPlugin_satp_mode <= _zz_438_[0];
          end
        end
        12'b001101000011 : begin
        end
        12'b001100000100 : begin
          if(execute_CsrPlugin_writeEnable)begin
            CsrPlugin_mie_MEIE <= _zz_439_[0];
            CsrPlugin_mie_MTIE <= _zz_440_[0];
            CsrPlugin_mie_MSIE <= _zz_441_[0];
          end
        end
        12'b001101000010 : begin
        end
        default : begin
        end
      endcase
    end
  end

  always @ (posedge clk) begin
    if(IBusCachedPlugin_iBusRsp_stages_1_output_ready)begin
      _zz_128_ <= IBusCachedPlugin_iBusRsp_stages_1_output_payload;
    end
    if(IBusCachedPlugin_iBusRsp_stages_0_output_ready)begin
      _zz_132_ <= _zz_130_;
      _zz_133_ <= _zz_131_;
    end
    if(IBusCachedPlugin_iBusRsp_stages_1_output_ready)begin
      _zz_136_ <= (_zz_132_ && (_zz_133_ == _zz_331_));
      _zz_137_ <= _zz_243_[1 : 0];
    end
    if(IBusCachedPlugin_iBusRsp_stages_1_input_ready)begin
      IBusCachedPlugin_s1_tightlyCoupledHit <= IBusCachedPlugin_s0_tightlyCoupledHit;
    end
    if(IBusCachedPlugin_iBusRsp_cacheRspArbitration_input_ready)begin
      IBusCachedPlugin_s2_tightlyCoupledHit <= IBusCachedPlugin_s1_tightlyCoupledHit;
    end
    if((MmuPlugin_dBusAccess_rsp_valid && (! MmuPlugin_dBusAccess_rsp_payload_redo)))begin
      MmuPlugin_shared_pteBuffer_V <= MmuPlugin_shared_dBusRsp_pte_V;
      MmuPlugin_shared_pteBuffer_R <= MmuPlugin_shared_dBusRsp_pte_R;
      MmuPlugin_shared_pteBuffer_W <= MmuPlugin_shared_dBusRsp_pte_W;
      MmuPlugin_shared_pteBuffer_X <= MmuPlugin_shared_dBusRsp_pte_X;
      MmuPlugin_shared_pteBuffer_U <= MmuPlugin_shared_dBusRsp_pte_U;
      MmuPlugin_shared_pteBuffer_G <= MmuPlugin_shared_dBusRsp_pte_G;
      MmuPlugin_shared_pteBuffer_A <= MmuPlugin_shared_dBusRsp_pte_A;
      MmuPlugin_shared_pteBuffer_D <= MmuPlugin_shared_dBusRsp_pte_D;
      MmuPlugin_shared_pteBuffer_RSW <= MmuPlugin_shared_dBusRsp_pte_RSW;
      MmuPlugin_shared_pteBuffer_PPN0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
      MmuPlugin_shared_pteBuffer_PPN1 <= MmuPlugin_shared_dBusRsp_pte_PPN1;
    end
    case(MmuPlugin_shared_state_1_)
      `MmuPlugin_shared_State_defaultEncoding_IDLE : begin
        if(_zz_307_)begin
          MmuPlugin_shared_vpn_1 <= IBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22];
          MmuPlugin_shared_vpn_0 <= IBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12];
          MmuPlugin_shared_portId <= (1'b0);
        end
        if(_zz_308_)begin
          MmuPlugin_shared_vpn_1 <= DBusCachedPlugin_mmuBus_cmd_virtualAddress[31 : 22];
          MmuPlugin_shared_vpn_0 <= DBusCachedPlugin_mmuBus_cmd_virtualAddress[21 : 12];
          MmuPlugin_shared_portId <= (1'b1);
        end
      end
      `MmuPlugin_shared_State_defaultEncoding_L1_CMD : begin
      end
      `MmuPlugin_shared_State_defaultEncoding_L1_RSP : begin
      end
      `MmuPlugin_shared_State_defaultEncoding_L0_CMD : begin
      end
      default : begin
      end
    endcase
    if(_zz_291_)begin
      if(_zz_292_)begin
        if(_zz_309_)begin
          MmuPlugin_ports_0_cache_0_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_0_cache_0_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_0_cache_0_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_0_cache_0_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_0_cache_0_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_0_cache_0_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_0_cache_0_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_0_cache_0_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_0_cache_0_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_0_cache_0_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
        if(_zz_310_)begin
          MmuPlugin_ports_0_cache_1_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_0_cache_1_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_0_cache_1_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_0_cache_1_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_0_cache_1_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_0_cache_1_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_0_cache_1_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_0_cache_1_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_0_cache_1_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_0_cache_1_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
        if(_zz_311_)begin
          MmuPlugin_ports_0_cache_2_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_0_cache_2_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_0_cache_2_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_0_cache_2_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_0_cache_2_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_0_cache_2_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_0_cache_2_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_0_cache_2_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_0_cache_2_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_0_cache_2_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
        if(_zz_312_)begin
          MmuPlugin_ports_0_cache_3_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_0_cache_3_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_0_cache_3_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_0_cache_3_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_0_cache_3_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_0_cache_3_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_0_cache_3_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_0_cache_3_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_0_cache_3_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_0_cache_3_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
        if(_zz_313_)begin
          MmuPlugin_ports_0_cache_4_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_0_cache_4_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_0_cache_4_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_0_cache_4_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_0_cache_4_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_0_cache_4_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_0_cache_4_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_0_cache_4_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_0_cache_4_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_0_cache_4_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
        if(_zz_314_)begin
          MmuPlugin_ports_0_cache_5_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_0_cache_5_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_0_cache_5_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_0_cache_5_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_0_cache_5_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_0_cache_5_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_0_cache_5_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_0_cache_5_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_0_cache_5_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_0_cache_5_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
      end
      if(_zz_293_)begin
        if(_zz_315_)begin
          MmuPlugin_ports_1_cache_0_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_1_cache_0_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_1_cache_0_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_1_cache_0_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_1_cache_0_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_1_cache_0_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_1_cache_0_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_1_cache_0_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_1_cache_0_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_1_cache_0_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
        if(_zz_316_)begin
          MmuPlugin_ports_1_cache_1_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_1_cache_1_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_1_cache_1_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_1_cache_1_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_1_cache_1_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_1_cache_1_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_1_cache_1_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_1_cache_1_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_1_cache_1_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_1_cache_1_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
        if(_zz_317_)begin
          MmuPlugin_ports_1_cache_2_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_1_cache_2_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_1_cache_2_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_1_cache_2_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_1_cache_2_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_1_cache_2_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_1_cache_2_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_1_cache_2_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_1_cache_2_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_1_cache_2_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
        if(_zz_318_)begin
          MmuPlugin_ports_1_cache_3_exception <= (MmuPlugin_shared_dBusRsp_exception || ((MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP) && (MmuPlugin_shared_dBusRsp_pte_PPN0 != (10'b0000000000))));
          MmuPlugin_ports_1_cache_3_virtualAddress_0 <= MmuPlugin_shared_vpn_0;
          MmuPlugin_ports_1_cache_3_virtualAddress_1 <= MmuPlugin_shared_vpn_1;
          MmuPlugin_ports_1_cache_3_physicalAddress_0 <= MmuPlugin_shared_dBusRsp_pte_PPN0;
          MmuPlugin_ports_1_cache_3_physicalAddress_1 <= MmuPlugin_shared_dBusRsp_pte_PPN1[9 : 0];
          MmuPlugin_ports_1_cache_3_allowRead <= MmuPlugin_shared_dBusRsp_pte_R;
          MmuPlugin_ports_1_cache_3_allowWrite <= MmuPlugin_shared_dBusRsp_pte_W;
          MmuPlugin_ports_1_cache_3_allowExecute <= MmuPlugin_shared_dBusRsp_pte_X;
          MmuPlugin_ports_1_cache_3_allowUser <= MmuPlugin_shared_dBusRsp_pte_U;
          MmuPlugin_ports_1_cache_3_superPage <= (MmuPlugin_shared_state_1_ == `MmuPlugin_shared_State_defaultEncoding_L1_RSP);
        end
      end
    end
    if(_zz_184_)begin
      _zz_186_ <= _zz_62_[11 : 7];
      _zz_187_ <= _zz_95_;
    end
    if((memory_DivPlugin_div_counter_value == (6'b100000)))begin
      memory_DivPlugin_div_done <= 1'b1;
    end
    if((! memory_arbitration_isStuck))begin
      memory_DivPlugin_div_done <= 1'b0;
    end
    if(_zz_274_)begin
      if(_zz_282_)begin
        memory_DivPlugin_rs1[31 : 0] <= _zz_405_[31:0];
        memory_DivPlugin_accumulator[31 : 0] <= ((! _zz_196_[32]) ? _zz_406_ : _zz_407_);
        if((memory_DivPlugin_div_counter_value == (6'b100000)))begin
          memory_DivPlugin_div_result <= _zz_408_[31:0];
        end
      end
    end
    if(_zz_301_)begin
      memory_DivPlugin_accumulator <= (65'b00000000000000000000000000000000000000000000000000000000000000000);
      memory_DivPlugin_rs1 <= ((_zz_199_ ? (~ _zz_200_) : _zz_200_) + _zz_414_);
      memory_DivPlugin_rs2 <= ((_zz_198_ ? (~ execute_RS2) : execute_RS2) + _zz_416_);
      memory_DivPlugin_div_needRevert <= ((_zz_199_ ^ (_zz_198_ && (! execute_INSTRUCTION[13]))) && (! (((execute_RS2 == (32'b00000000000000000000000000000000)) && execute_IS_RS2_SIGNED) && (! execute_INSTRUCTION[13]))));
    end
    CsrPlugin_mip_MEIP <= externalInterrupt;
    CsrPlugin_mip_MTIP <= timerInterrupt;
    CsrPlugin_mip_MSIP <= softwareInterrupt;
    CsrPlugin_mcycle <= (CsrPlugin_mcycle + (64'b0000000000000000000000000000000000000000000000000000000000000001));
    if(writeBack_arbitration_isFiring)begin
      CsrPlugin_minstret <= (CsrPlugin_minstret + (64'b0000000000000000000000000000000000000000000000000000000000000001));
    end
    if(_zz_279_)begin
      CsrPlugin_exceptionPortCtrl_exceptionContext_code <= (_zz_202_ ? IBusCachedPlugin_decodeExceptionPort_payload_code : decodeExceptionPort_payload_code);
      CsrPlugin_exceptionPortCtrl_exceptionContext_badAddr <= (_zz_202_ ? IBusCachedPlugin_decodeExceptionPort_payload_badAddr : decodeExceptionPort_payload_badAddr);
    end
    if(BranchPlugin_branchExceptionPort_valid)begin
      CsrPlugin_exceptionPortCtrl_exceptionContext_code <= BranchPlugin_branchExceptionPort_payload_code;
      CsrPlugin_exceptionPortCtrl_exceptionContext_badAddr <= BranchPlugin_branchExceptionPort_payload_badAddr;
    end
    if(DBusCachedPlugin_exceptionBus_valid)begin
      CsrPlugin_exceptionPortCtrl_exceptionContext_code <= DBusCachedPlugin_exceptionBus_payload_code;
      CsrPlugin_exceptionPortCtrl_exceptionContext_badAddr <= DBusCachedPlugin_exceptionBus_payload_badAddr;
    end
    if(_zz_283_)begin
      case(CsrPlugin_targetPrivilege)
        2'b11 : begin
          CsrPlugin_mcause_interrupt <= (! CsrPlugin_hadException);
          CsrPlugin_mcause_exceptionCode <= CsrPlugin_trapCause;
          CsrPlugin_mepc <= writeBack_PC;
          if(CsrPlugin_hadException)begin
            CsrPlugin_mtval <= CsrPlugin_exceptionPortCtrl_exceptionContext_badAddr;
          end
        end
        default : begin
        end
      endcase
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_IS_SFENCE_VMA <= decode_IS_SFENCE_VMA;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_IS_SFENCE_VMA <= execute_IS_SFENCE_VMA;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_IS_SFENCE_VMA <= memory_IS_SFENCE_VMA;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_MEMORY_MANAGMENT <= decode_MEMORY_MANAGMENT;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_MUL_HL <= execute_MUL_HL;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_MUL_LH <= execute_MUL_LH;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_SHIFT_RIGHT <= execute_SHIFT_RIGHT;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_IS_MUL <= decode_IS_MUL;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_IS_MUL <= execute_IS_MUL;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_IS_MUL <= memory_IS_MUL;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_BYPASSABLE_MEMORY_STAGE <= decode_BYPASSABLE_MEMORY_STAGE;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_BYPASSABLE_MEMORY_STAGE <= execute_BYPASSABLE_MEMORY_STAGE;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_INSTRUCTION <= decode_INSTRUCTION;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_INSTRUCTION <= execute_INSTRUCTION;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_BRANCH_CTRL <= _zz_27_;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_BRANCH_CTRL <= _zz_25_;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_MUL_LOW <= memory_MUL_LOW;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_BRANCH_DO <= execute_BRANCH_DO;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_ENV_CTRL <= _zz_23_;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_ENV_CTRL <= _zz_20_;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_ENV_CTRL <= _zz_18_;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_CSR_WRITE_OPCODE <= decode_CSR_WRITE_OPCODE;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_REGFILE_WRITE_VALID <= decode_REGFILE_WRITE_VALID;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_REGFILE_WRITE_VALID <= execute_REGFILE_WRITE_VALID;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_REGFILE_WRITE_VALID <= memory_REGFILE_WRITE_VALID;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_PREDICTION_CONTEXT_hazard <= decode_PREDICTION_CONTEXT_hazard;
      decode_to_execute_PREDICTION_CONTEXT_line_history <= decode_PREDICTION_CONTEXT_line_history;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_PREDICTION_CONTEXT_hazard <= execute_PREDICTION_CONTEXT_hazard;
      execute_to_memory_PREDICTION_CONTEXT_line_history <= execute_PREDICTION_CONTEXT_line_history;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_DO_EBREAK <= decode_DO_EBREAK;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_MUL_LL <= execute_MUL_LL;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_BRANCH_CALC <= execute_BRANCH_CALC;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_PREDICTION_HAD_BRANCHED2 <= decode_PREDICTION_HAD_BRANCHED2;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_MEMORY_ADDRESS_LOW <= execute_MEMORY_ADDRESS_LOW;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_MEMORY_ADDRESS_LOW <= memory_MEMORY_ADDRESS_LOW;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_REGFILE_WRITE_DATA <= _zz_45_;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_SRC_USE_SUB_LESS <= decode_SRC_USE_SUB_LESS;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_MEMORY_ENABLE <= decode_MEMORY_ENABLE;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_MEMORY_ENABLE <= execute_MEMORY_ENABLE;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_MEMORY_ENABLE <= memory_MEMORY_ENABLE;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_ALU_CTRL <= _zz_16_;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_RS2 <= decode_RS2;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_CSR_READ_OPCODE <= decode_CSR_READ_OPCODE;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_RS1 <= decode_RS1;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_FORMAL_PC_NEXT <= _zz_107_;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_FORMAL_PC_NEXT <= execute_FORMAL_PC_NEXT;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_FORMAL_PC_NEXT <= _zz_106_;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_IS_DIV <= decode_IS_DIV;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_IS_DIV <= execute_IS_DIV;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_SRC2_CTRL <= _zz_13_;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_PC <= decode_PC;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_PC <= _zz_53_;
    end
    if(((! writeBack_arbitration_isStuck) && (! CsrPlugin_exceptionPortCtrl_exceptionValids_writeBack)))begin
      memory_to_writeBack_PC <= memory_PC;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_IS_RS1_SIGNED <= decode_IS_RS1_SIGNED;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_MUL_HH <= execute_MUL_HH;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_MUL_HH <= memory_MUL_HH;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_SRC1_CTRL <= _zz_10_;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_IS_RS2_SIGNED <= decode_IS_RS2_SIGNED;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_ALU_BITWISE_CTRL <= _zz_7_;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_MEMORY_WR <= decode_MEMORY_WR;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_MEMORY_WR <= execute_MEMORY_WR;
    end
    if((! writeBack_arbitration_isStuck))begin
      memory_to_writeBack_MEMORY_WR <= memory_MEMORY_WR;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_SRC2_FORCE_ZERO <= decode_SRC2_FORCE_ZERO;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_BYPASSABLE_EXECUTE_STAGE <= decode_BYPASSABLE_EXECUTE_STAGE;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_IS_CSR <= decode_IS_CSR;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_SRC_LESS_UNSIGNED <= decode_SRC_LESS_UNSIGNED;
    end
    if((! execute_arbitration_isStuck))begin
      decode_to_execute_SHIFT_CTRL <= _zz_4_;
    end
    if((! memory_arbitration_isStuck))begin
      execute_to_memory_SHIFT_CTRL <= _zz_1_;
    end
    case(execute_CsrPlugin_csrAddress)
      12'b001100000000 : begin
      end
      12'b000100000000 : begin
      end
      12'b001101000001 : begin
        if(execute_CsrPlugin_writeEnable)begin
          CsrPlugin_mepc <= execute_CsrPlugin_writeData[31 : 0];
        end
      end
      12'b001101000100 : begin
        if(execute_CsrPlugin_writeEnable)begin
          CsrPlugin_mip_MSIP <= _zz_437_[0];
        end
      end
      12'b000110000000 : begin
        if(execute_CsrPlugin_writeEnable)begin
          MmuPlugin_satp_ppn <= execute_CsrPlugin_writeData[19 : 0];
        end
      end
      12'b001101000011 : begin
      end
      12'b001100000100 : begin
      end
      12'b001101000010 : begin
      end
      default : begin
      end
    endcase
  end

  always @ (posedge clk) begin
    DebugPlugin_firstCycle <= 1'b0;
    if(debug_bus_cmd_ready)begin
      DebugPlugin_firstCycle <= 1'b1;
    end
    DebugPlugin_secondCycle <= DebugPlugin_firstCycle;
    DebugPlugin_isPipBusy <= (({writeBack_arbitration_isValid,{memory_arbitration_isValid,{execute_arbitration_isValid,decode_arbitration_isValid}}} != (4'b0000)) || IBusCachedPlugin_incomingInstruction);
    if(writeBack_arbitration_isValid)begin
      DebugPlugin_busReadDataReg <= _zz_95_;
    end
    _zz_203_ <= debug_bus_cmd_payload_address[2];
    if(_zz_280_)begin
      DebugPlugin_busReadDataReg <= execute_PC;
    end
    DebugPlugin_resetIt_regNext <= DebugPlugin_resetIt;
  end

  always @ (posedge clk or posedge debugReset) begin
    if (debugReset) begin
      DebugPlugin_resetIt <= 1'b0;
      DebugPlugin_haltIt <= 1'b0;
      DebugPlugin_stepIt <= 1'b0;
      DebugPlugin_godmode <= 1'b0;
      DebugPlugin_haltedByBreak <= 1'b0;
    end else begin
      if((DebugPlugin_haltIt && (! DebugPlugin_isPipBusy)))begin
        DebugPlugin_godmode <= 1'b1;
      end
      if(debug_bus_cmd_valid)begin
        case(_zz_306_)
          6'b000000 : begin
            if(debug_bus_cmd_payload_wr)begin
              DebugPlugin_stepIt <= debug_bus_cmd_payload_data[4];
              if(debug_bus_cmd_payload_data[16])begin
                DebugPlugin_resetIt <= 1'b1;
              end
              if(debug_bus_cmd_payload_data[24])begin
                DebugPlugin_resetIt <= 1'b0;
              end
              if(debug_bus_cmd_payload_data[17])begin
                DebugPlugin_haltIt <= 1'b1;
              end
              if(debug_bus_cmd_payload_data[25])begin
                DebugPlugin_haltIt <= 1'b0;
              end
              if(debug_bus_cmd_payload_data[25])begin
                DebugPlugin_haltedByBreak <= 1'b0;
              end
              if(debug_bus_cmd_payload_data[25])begin
                DebugPlugin_godmode <= 1'b0;
              end
            end
          end
          6'b000001 : begin
          end
          default : begin
          end
        endcase
      end
      if(_zz_280_)begin
        if(_zz_281_)begin
          DebugPlugin_haltIt <= 1'b1;
          DebugPlugin_haltedByBreak <= 1'b1;
        end
      end
      if(_zz_285_)begin
        if(decode_arbitration_isValid)begin
          DebugPlugin_haltIt <= 1'b1;
        end
      end
    end
  end

  always @ (posedge clk) begin
    IBusCachedPlugin_injectionPort_payload_regNext <= IBusCachedPlugin_injectionPort_payload;
  end

endmodule

