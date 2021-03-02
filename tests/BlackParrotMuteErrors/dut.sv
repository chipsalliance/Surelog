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


package otp_ctrl_reg_pkg;

  // Param list
  parameter int NumSramKeyReqSlots = 2;
  parameter int OtpByteAddrWidth = 11;
  parameter int NumErrorEntries = 9;
  parameter int NumDaiWords = 2;
  parameter int NumDigestWords = 2;
  parameter int NumSwCfgWindowWords = 512;
  parameter int NumDebugWindowWords = 16;
  parameter int NumPart = 7;
  parameter int CreatorSwCfgOffset = 0;
  parameter int CreatorSwCfgSize = 768;
  parameter int CreatorSwCfgContentOffset = 0;
  parameter int CreatorSwCfgContentSize = 760;
  parameter int CreatorSwCfgDigestOffset = 760;
  parameter int CreatorSwCfgDigestSize = 8;
  parameter int OwnerSwCfgOffset = 768;
  parameter int OwnerSwCfgSize = 768;
  parameter int OwnerSwCfgContentOffset = 768;
  parameter int OwnerSwCfgContentSize = 760;
  parameter int OwnerSwCfgDigestOffset = 1528;
  parameter int OwnerSwCfgDigestSize = 8;
  parameter int HwCfgOffset = 1536;
  parameter int HwCfgSize = 208;
  parameter int DeviceIdOffset = 1536;
  parameter int DeviceIdSize = 32;
  parameter int HwCfgContentOffset = 1568;
  parameter int HwCfgContentSize = 168;
  parameter int HwCfgDigestOffset = 1736;
  parameter int HwCfgDigestSize = 8;
  parameter int Secret0Offset = 1744;
  parameter int Secret0Size = 40;
  parameter int TestUnlockTokenOffset = 1744;
  parameter int TestUnlockTokenSize = 16;
  parameter int TestExitTokenOffset = 1760;
  parameter int TestExitTokenSize = 16;
  parameter int Secret0DigestOffset = 1776;
  parameter int Secret0DigestSize = 8;
  parameter int Secret1Offset = 1784;
  parameter int Secret1Size = 88;
  parameter int FlashAddrKeySeedOffset = 1784;
  parameter int FlashAddrKeySeedSize = 32;
  parameter int FlashDataKeySeedOffset = 1816;
  parameter int FlashDataKeySeedSize = 32;
  parameter int SramDataKeySeedOffset = 1848;
  parameter int SramDataKeySeedSize = 16;
  parameter int Secret1DigestOffset = 1864;
  parameter int Secret1DigestSize = 8;
  parameter int Secret2Offset = 1872;
  parameter int Secret2Size = 120;
  parameter int RmaTokenOffset = 1872;
  parameter int RmaTokenSize = 16;
  parameter int CreatorRootKeyShare0Offset = 1888;
  parameter int CreatorRootKeyShare0Size = 32;
  parameter int CreatorRootKeyShare1Offset = 1920;
  parameter int CreatorRootKeyShare1Size = 32;
  parameter int Secret2DigestOffset = 1984;
  parameter int Secret2DigestSize = 8;
  parameter int LifeCycleOffset = 1992;
  parameter int LifeCycleSize = 56;
  parameter int LcStateOffset = 1992;
  parameter int LcStateSize = 24;
  parameter int LcTransitionCntOffset = 2016;
  parameter int LcTransitionCntSize = 32;
  parameter int NumAlerts = 2;

  ////////////////////////////
  // Typedefs for registers //
  ////////////////////////////
  typedef struct packed {
    struct packed {
      logic        q;
    } otp_operation_done;
    struct packed {
      logic        q;
    } otp_error;
  } otp_ctrl_reg2hw_intr_state_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
    } otp_operation_done;
    struct packed {
      logic        q;
    } otp_error;
  } otp_ctrl_reg2hw_intr_enable_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } otp_operation_done;
    struct packed {
      logic        q;
      logic        qe;
    } otp_error;
  } otp_ctrl_reg2hw_intr_test_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } otp_macro_failure;
    struct packed {
      logic        q;
      logic        qe;
    } otp_check_failure;
  } otp_ctrl_reg2hw_alert_test_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } rd;
    struct packed {
      logic        q;
      logic        qe;
    } wr;
    struct packed {
      logic        q;
      logic        qe;
    } digest;
  } otp_ctrl_reg2hw_direct_access_cmd_reg_t;

  typedef struct packed {
    logic [10:0] q;
  } otp_ctrl_reg2hw_direct_access_address_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_direct_access_wdata_mreg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } integrity;
    struct packed {
      logic        q;
      logic        qe;
    } consistency;
  } otp_ctrl_reg2hw_check_trigger_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_check_timeout_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_integrity_check_period_reg_t;

  typedef struct packed {
    logic [31:0] q;
  } otp_ctrl_reg2hw_consistency_check_period_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_creator_sw_cfg_read_lock_reg_t;

  typedef struct packed {
    logic        q;
  } otp_ctrl_reg2hw_owner_sw_cfg_read_lock_reg_t;


  typedef struct packed {
    struct packed {
      logic        d;
      logic        de;
    } otp_operation_done;
    struct packed {
      logic        d;
      logic        de;
    } otp_error;
  } otp_ctrl_hw2reg_intr_state_reg_t;

  typedef struct packed {
    struct packed {
      logic        d;
    } creator_sw_cfg_error;
    struct packed {
      logic        d;
    } owner_sw_cfg_error;
    struct packed {
      logic        d;
    } hw_cfg_error;
    struct packed {
      logic        d;
    } secret0_error;
    struct packed {
      logic        d;
    } secret1_error;
    struct packed {
      logic        d;
    } secret2_error;
    struct packed {
      logic        d;
    } life_cycle_error;
    struct packed {
      logic        d;
    } dai_error;
    struct packed {
      logic        d;
    } lci_error;
    struct packed {
      logic        d;
    } timeout_error;
    struct packed {
      logic        d;
    } lfsr_fsm_error;
    struct packed {
      logic        d;
    } scrambling_fsm_error;
    struct packed {
      logic        d;
    } key_deriv_fsm_error;
    struct packed {
      logic        d;
    } dai_idle;
    struct packed {
      logic        d;
    } check_pending;
  } otp_ctrl_hw2reg_status_reg_t;

  typedef struct packed {
    logic [2:0]  d;
  } otp_ctrl_hw2reg_err_code_mreg_t;

  typedef struct packed {
    logic        d;
  } otp_ctrl_hw2reg_direct_access_regwen_reg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_direct_access_rdata_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_creator_sw_cfg_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_owner_sw_cfg_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_hw_cfg_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_secret0_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_secret1_digest_mreg_t;

  typedef struct packed {
    logic [31:0] d;
  } otp_ctrl_hw2reg_secret2_digest_mreg_t;


  ///////////////////////////////////////
  // Register to internal design logic //
  ///////////////////////////////////////
  typedef struct packed {
    otp_ctrl_reg2hw_intr_state_reg_t intr_state; // [194:193]
    otp_ctrl_reg2hw_intr_enable_reg_t intr_enable; // [192:191]
    otp_ctrl_reg2hw_intr_test_reg_t intr_test; // [190:187]
    otp_ctrl_reg2hw_alert_test_reg_t alert_test; // [186:183]
    otp_ctrl_reg2hw_direct_access_cmd_reg_t direct_access_cmd; // [182:177]
    otp_ctrl_reg2hw_direct_access_address_reg_t direct_access_address; // [176:166]
    otp_ctrl_reg2hw_direct_access_wdata_mreg_t [1:0] direct_access_wdata; // [165:102]
    otp_ctrl_reg2hw_check_trigger_reg_t check_trigger; // [101:98]
    otp_ctrl_reg2hw_check_timeout_reg_t check_timeout; // [97:66]
    otp_ctrl_reg2hw_integrity_check_period_reg_t integrity_check_period; // [65:34]
    otp_ctrl_reg2hw_consistency_check_period_reg_t consistency_check_period; // [33:2]
    otp_ctrl_reg2hw_creator_sw_cfg_read_lock_reg_t creator_sw_cfg_read_lock; // [1:1]
    otp_ctrl_reg2hw_owner_sw_cfg_read_lock_reg_t owner_sw_cfg_read_lock; // [0:0]
  } otp_ctrl_reg2hw_t;

  ///////////////////////////////////////
  // Internal design logic to register //
  ///////////////////////////////////////
  typedef struct packed {
    otp_ctrl_hw2reg_intr_state_reg_t intr_state; // [494:491]
    otp_ctrl_hw2reg_status_reg_t status; // [490:476]
    otp_ctrl_hw2reg_err_code_mreg_t [8:0] err_code; // [475:449]
    otp_ctrl_hw2reg_direct_access_regwen_reg_t direct_access_regwen; // [448:448]
    otp_ctrl_hw2reg_direct_access_rdata_mreg_t [1:0] direct_access_rdata; // [447:384]
    otp_ctrl_hw2reg_creator_sw_cfg_digest_mreg_t [1:0] creator_sw_cfg_digest; // [383:320]
    otp_ctrl_hw2reg_owner_sw_cfg_digest_mreg_t [1:0] owner_sw_cfg_digest; // [319:256]
    otp_ctrl_hw2reg_hw_cfg_digest_mreg_t [1:0] hw_cfg_digest; // [255:192]
    otp_ctrl_hw2reg_secret0_digest_mreg_t [1:0] secret0_digest; // [191:128]
    otp_ctrl_hw2reg_secret1_digest_mreg_t [1:0] secret1_digest; // [127:64]
    otp_ctrl_hw2reg_secret2_digest_mreg_t [1:0] secret2_digest; // [63:0]
  } otp_ctrl_hw2reg_t;

  // Register Address
  parameter logic [13:0] OTP_CTRL_INTR_STATE_OFFSET = 14'h 0;
  parameter logic [13:0] OTP_CTRL_INTR_ENABLE_OFFSET = 14'h 4;
  parameter logic [13:0] OTP_CTRL_INTR_TEST_OFFSET = 14'h 8;
  parameter logic [13:0] OTP_CTRL_ALERT_TEST_OFFSET = 14'h c;
  parameter logic [13:0] OTP_CTRL_STATUS_OFFSET = 14'h 10;
  parameter logic [13:0] OTP_CTRL_ERR_CODE_OFFSET = 14'h 14;
  parameter logic [13:0] OTP_CTRL_DIRECT_ACCESS_REGWEN_OFFSET = 14'h 18;
  parameter logic [13:0] OTP_CTRL_DIRECT_ACCESS_CMD_OFFSET = 14'h 1c;
  parameter logic [13:0] OTP_CTRL_DIRECT_ACCESS_ADDRESS_OFFSET = 14'h 20;
  parameter logic [13:0] OTP_CTRL_DIRECT_ACCESS_WDATA_0_OFFSET = 14'h 24;
  parameter logic [13:0] OTP_CTRL_DIRECT_ACCESS_WDATA_1_OFFSET = 14'h 28;
  parameter logic [13:0] OTP_CTRL_DIRECT_ACCESS_RDATA_0_OFFSET = 14'h 2c;
  parameter logic [13:0] OTP_CTRL_DIRECT_ACCESS_RDATA_1_OFFSET = 14'h 30;
  parameter logic [13:0] OTP_CTRL_CHECK_TRIGGER_REGWEN_OFFSET = 14'h 34;
  parameter logic [13:0] OTP_CTRL_CHECK_TRIGGER_OFFSET = 14'h 38;
  parameter logic [13:0] OTP_CTRL_CHECK_REGWEN_OFFSET = 14'h 3c;
  parameter logic [13:0] OTP_CTRL_CHECK_TIMEOUT_OFFSET = 14'h 40;
  parameter logic [13:0] OTP_CTRL_INTEGRITY_CHECK_PERIOD_OFFSET = 14'h 44;
  parameter logic [13:0] OTP_CTRL_CONSISTENCY_CHECK_PERIOD_OFFSET = 14'h 48;
  parameter logic [13:0] OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_OFFSET = 14'h 4c;
  parameter logic [13:0] OTP_CTRL_OWNER_SW_CFG_READ_LOCK_OFFSET = 14'h 50;
  parameter logic [13:0] OTP_CTRL_CREATOR_SW_CFG_DIGEST_0_OFFSET = 14'h 54;
  parameter logic [13:0] OTP_CTRL_CREATOR_SW_CFG_DIGEST_1_OFFSET = 14'h 58;
  parameter logic [13:0] OTP_CTRL_OWNER_SW_CFG_DIGEST_0_OFFSET = 14'h 5c;
  parameter logic [13:0] OTP_CTRL_OWNER_SW_CFG_DIGEST_1_OFFSET = 14'h 60;
  parameter logic [13:0] OTP_CTRL_HW_CFG_DIGEST_0_OFFSET = 14'h 64;
  parameter logic [13:0] OTP_CTRL_HW_CFG_DIGEST_1_OFFSET = 14'h 68;
  parameter logic [13:0] OTP_CTRL_SECRET0_DIGEST_0_OFFSET = 14'h 6c;
  parameter logic [13:0] OTP_CTRL_SECRET0_DIGEST_1_OFFSET = 14'h 70;
  parameter logic [13:0] OTP_CTRL_SECRET1_DIGEST_0_OFFSET = 14'h 74;
  parameter logic [13:0] OTP_CTRL_SECRET1_DIGEST_1_OFFSET = 14'h 78;
  parameter logic [13:0] OTP_CTRL_SECRET2_DIGEST_0_OFFSET = 14'h 7c;
  parameter logic [13:0] OTP_CTRL_SECRET2_DIGEST_1_OFFSET = 14'h 80;

  // Window parameter
  parameter logic [13:0] OTP_CTRL_SW_CFG_WINDOW_OFFSET = 14'h 1000;
  parameter logic [13:0] OTP_CTRL_SW_CFG_WINDOW_SIZE   = 14'h 800;
  parameter logic [13:0] OTP_CTRL_TEST_ACCESS_OFFSET = 14'h 2000;
  parameter logic [13:0] OTP_CTRL_TEST_ACCESS_SIZE   = 14'h 40;

  // Register Index
  typedef enum int {
    OTP_CTRL_INTR_STATE,
    OTP_CTRL_INTR_ENABLE,
    OTP_CTRL_INTR_TEST,
    OTP_CTRL_ALERT_TEST,
    OTP_CTRL_STATUS,
    OTP_CTRL_ERR_CODE,
    OTP_CTRL_DIRECT_ACCESS_REGWEN,
    OTP_CTRL_DIRECT_ACCESS_CMD,
    OTP_CTRL_DIRECT_ACCESS_ADDRESS,
    OTP_CTRL_DIRECT_ACCESS_WDATA_0,
    OTP_CTRL_DIRECT_ACCESS_WDATA_1,
    OTP_CTRL_DIRECT_ACCESS_RDATA_0,
    OTP_CTRL_DIRECT_ACCESS_RDATA_1,
    OTP_CTRL_CHECK_TRIGGER_REGWEN,
    OTP_CTRL_CHECK_TRIGGER,
    OTP_CTRL_CHECK_REGWEN,
    OTP_CTRL_CHECK_TIMEOUT,
    OTP_CTRL_INTEGRITY_CHECK_PERIOD,
    OTP_CTRL_CONSISTENCY_CHECK_PERIOD,
    OTP_CTRL_CREATOR_SW_CFG_READ_LOCK,
    OTP_CTRL_OWNER_SW_CFG_READ_LOCK,
    OTP_CTRL_CREATOR_SW_CFG_DIGEST_0,
    OTP_CTRL_CREATOR_SW_CFG_DIGEST_1,
    OTP_CTRL_OWNER_SW_CFG_DIGEST_0,
    OTP_CTRL_OWNER_SW_CFG_DIGEST_1,
    OTP_CTRL_HW_CFG_DIGEST_0,
    OTP_CTRL_HW_CFG_DIGEST_1,
    OTP_CTRL_SECRET0_DIGEST_0,
    OTP_CTRL_SECRET0_DIGEST_1,
    OTP_CTRL_SECRET1_DIGEST_0,
    OTP_CTRL_SECRET1_DIGEST_1,
    OTP_CTRL_SECRET2_DIGEST_0,
    OTP_CTRL_SECRET2_DIGEST_1
  } otp_ctrl_id_e;

  // Register width information to check illegal writes
  parameter logic [3:0] OTP_CTRL_PERMIT [33] = '{
    4'b 0001, // index[ 0] OTP_CTRL_INTR_STATE
    4'b 0001, // index[ 1] OTP_CTRL_INTR_ENABLE
    4'b 0001, // index[ 2] OTP_CTRL_INTR_TEST
    4'b 0001, // index[ 3] OTP_CTRL_ALERT_TEST
    4'b 0011, // index[ 4] OTP_CTRL_STATUS
    4'b 1111, // index[ 5] OTP_CTRL_ERR_CODE
    4'b 0001, // index[ 6] OTP_CTRL_DIRECT_ACCESS_REGWEN
    4'b 0001, // index[ 7] OTP_CTRL_DIRECT_ACCESS_CMD
    4'b 0011, // index[ 8] OTP_CTRL_DIRECT_ACCESS_ADDRESS
    4'b 1111, // index[ 9] OTP_CTRL_DIRECT_ACCESS_WDATA_0
    4'b 1111, // index[10] OTP_CTRL_DIRECT_ACCESS_WDATA_1
    4'b 1111, // index[11] OTP_CTRL_DIRECT_ACCESS_RDATA_0
    4'b 1111, // index[12] OTP_CTRL_DIRECT_ACCESS_RDATA_1
    4'b 0001, // index[13] OTP_CTRL_CHECK_TRIGGER_REGWEN
    4'b 0001, // index[14] OTP_CTRL_CHECK_TRIGGER
    4'b 0001, // index[15] OTP_CTRL_CHECK_REGWEN
    4'b 1111, // index[16] OTP_CTRL_CHECK_TIMEOUT
    4'b 1111, // index[17] OTP_CTRL_INTEGRITY_CHECK_PERIOD
    4'b 1111, // index[18] OTP_CTRL_CONSISTENCY_CHECK_PERIOD
    4'b 0001, // index[19] OTP_CTRL_CREATOR_SW_CFG_READ_LOCK
    4'b 0001, // index[20] OTP_CTRL_OWNER_SW_CFG_READ_LOCK
    4'b 1111, // index[21] OTP_CTRL_CREATOR_SW_CFG_DIGEST_0
    4'b 1111, // index[22] OTP_CTRL_CREATOR_SW_CFG_DIGEST_1
    4'b 1111, // index[23] OTP_CTRL_OWNER_SW_CFG_DIGEST_0
    4'b 1111, // index[24] OTP_CTRL_OWNER_SW_CFG_DIGEST_1
    4'b 1111, // index[25] OTP_CTRL_HW_CFG_DIGEST_0
    4'b 1111, // index[26] OTP_CTRL_HW_CFG_DIGEST_1
    4'b 1111, // index[27] OTP_CTRL_SECRET0_DIGEST_0
    4'b 1111, // index[28] OTP_CTRL_SECRET0_DIGEST_1
    4'b 1111, // index[29] OTP_CTRL_SECRET1_DIGEST_0
    4'b 1111, // index[30] OTP_CTRL_SECRET1_DIGEST_1
    4'b 1111, // index[31] OTP_CTRL_SECRET2_DIGEST_0
    4'b 1111  // index[32] OTP_CTRL_SECRET2_DIGEST_1
  };
endpackage


package otp_ctrl_pkg;

  import prim_util_pkg::vbits;
  import otp_ctrl_reg_pkg::*;

  ////////////////////////
  // General Parameters //
  ////////////////////////

  // Width of entropy input
  parameter int EdnDataWidth = 64;

  parameter int NumPartWidth = vbits(NumPart);

  parameter int SwWindowAddrWidth = vbits(NumSwCfgWindowWords);

  // Redundantly encoded and complementary values are used to for signalling to the partition
  // controller FSMs and the DAI whether a partition is locked or not. Any other value than
  // "Unlocked" is interpreted as "Locked" in those FSMs.
  typedef enum logic [7:0] {
    Unlocked = 8'h5A,
    Locked   = 8'hA5
  } access_e;

  // Partition access type
  typedef struct packed {
    access_e read_lock;
    access_e write_lock;
  } part_access_t;

  parameter int DaiCmdWidth = 3;
  typedef enum logic [DaiCmdWidth-1:0] {
    DaiRead   = 3'b001,
    DaiWrite  = 3'b010,
    DaiDigest = 3'b100
  } dai_cmd_e;

  //////////////////////////////////////
  // Typedefs for OTP Macro Interface //
  //////////////////////////////////////

  // OTP-macro specific
  parameter int OtpWidth         = 16;
  parameter int OtpAddrWidth     = OtpByteAddrWidth - $clog2(OtpWidth/8);
  parameter int OtpDepth         = 2**OtpAddrWidth;
  parameter int OtpSizeWidth     = 2; // Allows to transfer up to 4 native OTP words at once.
  parameter int OtpErrWidth      = 3;
  parameter int OtpPwrSeqWidth   = 2;
  parameter int OtpIfWidth       = 2**OtpSizeWidth*OtpWidth;
  // Number of Byte address bits to cut off in order to get the native OTP word address.
  parameter int OtpAddrShift     = OtpByteAddrWidth - OtpAddrWidth;

  typedef enum logic [OtpErrWidth-1:0] {
    NoError              = 3'h0,
    MacroError           = 3'h1,
    MacroEccCorrError    = 3'h2,
    MacroEccUncorrError  = 3'h3,
    MacroWriteBlankError = 3'h4,
    AccessError          = 3'h5,
    CheckFailError       = 3'h6,
    FsmStateError        = 3'h7
  } otp_err_e;

  /////////////////////////////////
  // Typedefs for OTP Scrambling //
  /////////////////////////////////

  parameter int ScrmblKeyWidth   = 128;
  parameter int ScrmblBlockWidth = 64;

  parameter int NumPresentRounds = 31;
  parameter int ScrmblBlockHalfWords = ScrmblBlockWidth / OtpWidth;

  typedef enum logic [2:0] {
    Decrypt,
    Encrypt,
    LoadShadow,
    Digest,
    DigestInit,
    DigestFinalize
  } otp_scrmbl_cmd_e;

  parameter int NumScrmblKeys = 3;
  parameter int NumDigestSets = 5;
  parameter int ConstSelWidth = (NumScrmblKeys > NumDigestSets) ?
                                vbits(NumScrmblKeys) :
                                vbits(NumDigestSets);

  typedef enum logic [ConstSelWidth-1:0] {
    Secret0Key,
    Secret1Key,
    Secret2Key
  } key_sel_e;

  typedef enum logic [ConstSelWidth-1:0] {
    CnstyDigest,
    LcRawDigest,
    FlashDataKey,
    FlashAddrKey,
    SramDataKey
  } digest_sel_e;

  typedef enum logic [ConstSelWidth-1:0] {
    StandardMode,
    ChainedMode
  } digest_mode_e;

  /////////////////////////////////////
  // Typedefs for Partition Metadata //
  /////////////////////////////////////

  typedef enum logic [1:0] {
    Unbuffered,
    Buffered,
    LifeCycle
  } part_variant_e;

  typedef struct packed {
    part_variant_e variant;
    // Offset and size within the OTP array, in Bytes.
    logic [OtpByteAddrWidth-1:0] offset;
    logic [OtpByteAddrWidth-1:0] size;
    // Key index to use for scrambling.
    key_sel_e key_sel;
    // Attributes
    logic secret;     // Whether the partition is secret (and hence scrambled)
    logic hw_digest;  // Whether the partition has a hardware digest
    logic write_lock; // Whether the partition is write lockable (via digest)
    logic read_lock;  // Whether the partition is read lockable (via digest)
  } part_info_t;

  ///////////////////////////////
  // Typedefs for LC Interface //
  ///////////////////////////////

  typedef struct packed {
    logic                      valid;
    lc_ctrl_pkg::lc_state_e    state;
    lc_ctrl_pkg::lc_cnt_e      count;
    // These are all hash post-images
    lc_ctrl_pkg::lc_token_t    all_zero_token;
    lc_ctrl_pkg::lc_token_t    raw_unlock_token;
    lc_ctrl_pkg::lc_token_t    test_unlock_token;
    lc_ctrl_pkg::lc_token_t    test_exit_token;
    lc_ctrl_pkg::lc_token_t    rma_token;
    lc_ctrl_pkg::lc_id_state_e id_state;
  } otp_lc_data_t;

  // Default for dangling connection
  parameter otp_lc_data_t OTP_LC_DATA_DEFAULT = '{
    valid: 1'b1,
    state: '0,
    count: '0,
    all_zero_token: '0,
    raw_unlock_token: '0,
    test_unlock_token: '0,
    test_exit_token: '0,
    rma_token: '0,
    id_state: '0
  };

  typedef struct packed {
    logic req;
    lc_ctrl_pkg::lc_state_e state;
    lc_ctrl_pkg::lc_cnt_e   count;
  } lc_otp_program_req_t;

  typedef struct packed {
    logic err;
    logic ack;
  } lc_otp_program_rsp_t;

  // RAW unlock token hashing request.
  typedef struct packed {
    logic req;
    lc_ctrl_pkg::lc_token_t token_input;
  } lc_otp_token_req_t;

  typedef struct packed {
    logic ack;
    lc_ctrl_pkg::lc_token_t hashed_token;
  } lc_otp_token_rsp_t;

  ////////////////////////////////
  // Typedefs for Key Broadcast //
  ////////////////////////////////

  parameter int FlashKeySeedWidth = 256;
  parameter int SramKeySeedWidth  = 128;
  parameter int KeyMgrKeyWidth   = 256;
  parameter int FlashKeyWidth    = 128;
  parameter int SramKeyWidth     = 128;
  parameter int SramNonceWidth   = 64;
  parameter int OtbnKeyWidth     = 128;
  parameter int OtbnNonceWidth   = 256;

  typedef logic [SramKeyWidth-1:0]   sram_key_t;
  typedef logic [SramNonceWidth-1:0] sram_nonce_t;
  typedef logic [OtbnKeyWidth-1:0]   otbn_key_t;
  typedef logic [OtbnNonceWidth-1:0] otbn_nonce_t;

  typedef struct packed {
    logic valid;
    logic [KeyMgrKeyWidth-1:0] key_share0;
    logic [KeyMgrKeyWidth-1:0] key_share1;
  } otp_keymgr_key_t;

  parameter otp_keymgr_key_t OTP_KEYMGR_KEY_DEFAULT = '{
    valid: 1'b1,
    key_share0: 256'hefb7ea7ee90093cf4affd9aaa2d6c0ec446cfdf5f2d5a0bfd7e2d93edc63a102,
    key_share1: 256'h56d24a00181de99e0f690b447a8dde2a1ffb8bc306707107aa6e2410f15cfc37
  };

  typedef struct packed {
    logic data_req; // Requests static key for data scrambling.
    logic addr_req; // Requests static key for address scrambling.
  } flash_otp_key_req_t;

  typedef struct packed {
    logic req; // Requests ephemeral scrambling key and nonce.
  } sram_otp_key_req_t;

  typedef struct packed {
    logic req; // Requests ephemeral scrambling key and nonce.
  } otbn_otp_key_req_t;

  typedef struct packed {
    logic data_ack;                // Ack for data key.
    logic addr_ack;                // Ack for address key.
    logic [FlashKeyWidth-1:0] key; // 128bit static scrambling key.
    logic seed_valid;              // Set to 1 if the key seed has been provisioned and is valid.
  } flash_otp_key_rsp_t;

  // Default for dangling connection
  parameter flash_otp_key_rsp_t FLASH_OTP_KEY_RSP_DEFAULT = '{
    data_ack: 1'b1,
    addr_ack: 1'b1,
    key: '0,
    seed_valid: 1'b1
  };

  typedef struct packed {
    logic        ack;         // Ack for key.
    sram_key_t   key;        // 128bit ephemeral scrambling key.
    sram_nonce_t nonce;      // 64bit nonce.
    logic        seed_valid; // Set to 1 if the key seed has been provisioned and is valid.
  } sram_otp_key_rsp_t;

  typedef struct packed {
    logic        ack;        // Ack for key.
    otbn_key_t   key;        // 128bit ephemeral scrambling key.
    otbn_nonce_t nonce;      // 256bit nonce.
    logic        seed_valid; // Set to 1 if the key seed has been provisioned and is valid.
  } otbn_otp_key_rsp_t;

  ////////////////////////////////
  // Power/Reset Ctrl Interface //
  ////////////////////////////////

  typedef struct packed {
    logic init;
  } pwr_otp_init_req_t;

  typedef struct packed {
    logic done;
  } pwr_otp_init_rsp_t;

  typedef struct packed {
    logic idle;
  } otp_pwr_state_t;


  ///////////////////
  // AST Interface //
  ///////////////////

  typedef struct packed {
    logic [OtpPwrSeqWidth-1:0] pwr_seq;
  } otp_ast_req_t;

  typedef struct packed {
    logic [OtpPwrSeqWidth-1:0] pwr_seq_h;
  } otp_ast_rsp_t;

  ///////////////////////////////////////////
  // Defaults for random netlist constants //
  ///////////////////////////////////////////

  // These LFSR parameters have been generated with
  // $ hw/ip/prim/util/gen-lfsr-seed.py --width 40 --seed 4247488366
  localparam int LfsrWidth = 40;
  typedef logic [LfsrWidth-1:0]                        lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  localparam lfsr_seed_t RndCnstLfsrSeedDefault = 40'h453d28ea98;
  localparam lfsr_perm_t RndCnstLfsrPermDefault =
      240'h4235171482c225f79289b32181a0163a760355d3447063d16661e44c12a5;


  typedef logic [NumScrmblKeys-1:0][ScrmblKeyWidth-1:0] key_array_t;
  parameter key_array_t RndCnstKeyDefault = {
    128'h047288e1a65c839dae610bbbdf8c4525,
    128'h38fe59a71a91a65636573a6513784e3b,
    128'h4f48dcc45ace0770e9135bda73e56344
  };

  // Note: digest set 0 is used for computing the partition digests. Constants at
  // higher indices are used to compute the scrambling keys.
  typedef logic [NumDigestSets-1:0][ScrmblKeyWidth-1:0] digest_const_array_t;
  parameter digest_const_array_t RndCnstDigestConstDefault = {
    128'h9d40106e2dc2346ec96d61f0cc5295c7,
    128'hafed2aa5c3284c01d71103edab1d8953,
    128'h8a14fe0c08f8a3a190dd32c05f208474,
    128'h9e6fac4ba15a3bce29d05a3e9e2d0846,
    128'h3a0c6051392e00ef24073627319555b8
  };

  typedef logic [NumDigestSets-1:0][ScrmblBlockWidth-1:0] digest_iv_array_t;
  parameter digest_iv_array_t RndCnstDigestIVDefault = {
    64'ha5af72c1b813aec4,
    64'h5d7aacd1db316407,
    64'hd0ec83b7fe6ae2ae,
    64'hc2993a0ea64e312d,
    64'h899aac2ab7d91479
  };

  parameter lc_ctrl_pkg::lc_token_t RndCnstRawUnlockTokenDefault =
    128'hcbbd013ff15eba2f3065461eeb88463e;

endpackage : otp_ctrl_pkg

 
module otp_ctrl_part_buf
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
#(
  // Partition information.
  parameter part_info_t             Info = part_info_t'(0)
) (
  
  
);

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  import prim_util_pkg::vbits;

  localparam int DigestOffset = Info.offset + Info.size - ScrmblBlockWidth/8;

endmodule

package otp_ctrl_part_pkg;

  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_pkg::*;

  localparam part_info_t PartInfo [NumPart] = '{
    // CREATOR_SW_CFG
    '{
      variant:    Unbuffered,
      offset:     11'd0,
      size:       768,
      key_sel:    key_sel_e'('0),
      secret:     1'b0,
      hw_digest:  1'b0,
      write_lock: 1'b1,
      read_lock:  1'b0
    },
    // OWNER_SW_CFG
    '{
      variant:    Unbuffered,
      offset:     11'd768,
      size:       768,
      key_sel:    key_sel_e'('0),
      secret:     1'b0,
      hw_digest:  1'b0,
      write_lock: 1'b1,
      read_lock:  1'b0
    },
    // HW_CFG
    '{
      variant:    Buffered,
      offset:     11'd1536,
      size:       208,
      key_sel:    key_sel_e'('0),
      secret:     1'b0,
      hw_digest:  1'b1,
      write_lock: 1'b1,
      read_lock:  1'b0
    },
    // SECRET0
    '{
      variant:    Buffered,
      offset:     11'd1744,
      size:       40,
      key_sel:    Secret0Key,
      secret:     1'b1,
      hw_digest:  1'b1,
      write_lock: 1'b1,
      read_lock:  1'b1
    },
    // SECRET1
    '{
      variant:    Buffered,
      offset:     11'd1784,
      size:       88,
      key_sel:    Secret1Key,
      secret:     1'b1,
      hw_digest:  1'b1,
      write_lock: 1'b1,
      read_lock:  1'b1
    },
    // SECRET2
    '{
      variant:    Buffered,
      offset:     11'd1872,
      size:       120,
      key_sel:    Secret2Key,
      secret:     1'b1,
      hw_digest:  1'b1,
      write_lock: 1'b1,
      read_lock:  1'b1
    },
    // LIFE_CYCLE
    '{
      variant:    LifeCycle,
      offset:     11'd1992,
      size:       56,
      key_sel:    key_sel_e'('0),
      secret:     1'b0,
      hw_digest:  1'b0,
      write_lock: 1'b0,
      read_lock:  1'b0
    }
  };

endpackage

module otp_ctrl
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*; ();

for (genvar k = 0; k < NumPart; k ++) begin : gen_partitions

if (PartInfo[k].variant == Buffered) begin : gen_buffered
      otp_ctrl_part_buf #(
        .Info(PartInfo[k]),
        .DataDefault(PartInvDefault[PartInfo[k].offset*8 +: PartInfo[k].size*8])
      ) u_part_buf ();
end

end

endmodule


