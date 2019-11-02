module pcm_slv_top(clk, rst, ssel, pcm_clk_i, pcm_sync_i, pcm_din_i, pcm_dout_o, din_i, dout_o, re_i, we_i);
  wire _000_;
  wire _001_;
  wire [7:0] _002_;
  wire _003_;
  wire [15:0] _004_;
  wire [15:0] _005_;
  wire _006_;
  wire [3:0] _007_;
  wire _008_;
  wire _009_;
  wire [7:0] _010_;
  wire [7:0] _011_;
  wire [15:0] _012_;
  wire _013_;
  wire _014_;
  wire _015_;
  wire _016_;
  wire _017_;
  wire _018_;
  wire _019_;
  wire _020_;
  wire _021_;
  wire _022_;
  wire _023_;
  wire _024_;
  wire _025_;
  wire _026_;
  wire _027_;
  wire _028_;
  wire _029_;
  wire _030_;
  wire _031_;
  wire _032_;
  wire _033_;
  wire _034_;
  wire _035_;
  wire _036_;
  wire _037_;
  wire _038_;
  wire _039_;
  wire _040_;
  wire _041_;
  wire _042_;
  wire _043_;
  wire _044_;
  wire _045_;
  wire _046_;
  wire _047_;
  wire _048_;
  wire _049_;
  wire _050_;
  wire _051_;
  wire _052_;
  wire _053_;
  wire _054_;
  wire _055_;
  wire _056_;
  wire _057_;
  wire _058_;
  wire _059_;
  wire _060_;
  wire _061_;
  wire _062_;
  wire _063_;
  wire _064_;
  wire _065_;
  wire _066_;
  wire _067_;
  wire _068_;
  wire _069_;
  wire _070_;
  wire _071_;
  wire _072_;
  wire _073_;
  wire _074_;
  wire _075_;
  wire _076_;
  wire _077_;
  wire _078_;
  wire _079_;
  wire _080_;
  wire _081_;
  wire _082_;
  wire _083_;
  wire _084_;
  wire _085_;
  wire _086_;
  wire _087_;
  wire _088_;
  wire _089_;
  wire _090_;
  wire _091_;
  wire _092_;
  wire _093_;
  wire _094_;
  wire _095_;
  wire _096_;
  wire _097_;
  wire _098_;
  wire _099_;
  wire _100_;
  wire _101_;
  wire _102_;
  wire _103_;
  wire _104_;
  wire _105_;
  wire _106_;
  wire _107_;
  wire _108_;
  wire _109_;
  wire _110_;
  wire _111_;
  wire _112_;
  wire _113_;
  wire _114_;
  input clk;
  input [7:0] din_i;
  output [7:0] dout_o;
  reg pclk_r;
  reg pclk_s;
  reg pclk_t;
  input pcm_clk_i;
  input pcm_din_i;
  output pcm_dout_o;
  reg pcm_dout_o;
  input pcm_sync_i;
  reg pcm_sync_r1;
  reg pcm_sync_r2;
  reg pcm_sync_r3;
  reg [7:0] psa;
  reg psync;
  input re_i;
  input rst;
  reg [15:0] rx_hold_reg;
  reg [15:0] rx_reg;
  reg rxd;
  reg rxd_t;
  input [2:0] ssel;
  reg [3:0] tx_cnt;
  reg tx_go;
  reg tx_go_r1;
  reg [7:0] tx_hold_byte_h;
  reg [7:0] tx_hold_byte_l;
  wire [15:0] tx_hold_reg;
  input [1:0] we_i;
  assign _013_ = ~pcm_sync_r3;
  assign _003_ = _013_ & pcm_sync_r2;
  assign _014_ = ~pclk_s;
  assign _015_ = pclk_r & _014_;
  assign _000_ = _015_ ? pcm_sync_i : pcm_sync_r1;
  assign _016_ = pclk_r | _014_;
  assign _002_[0] = _016_ ? psa[0] : pcm_sync_r1;
  assign _002_[1] = _016_ ? psa[1] : psa[0];
  assign _002_[2] = _016_ ? psa[2] : psa[1];
  assign _002_[3] = _016_ ? psa[3] : psa[2];
  assign _002_[4] = _016_ ? psa[4] : psa[3];
  assign _002_[5] = _016_ ? psa[5] : psa[4];
  assign _002_[6] = _016_ ? psa[6] : psa[5];
  assign _002_[7] = _016_ ? psa[7] : psa[6];
  assign _010_[0] = we_i[1] ? din_i[0] : tx_hold_byte_h[0];
  assign _010_[1] = we_i[1] ? din_i[1] : tx_hold_byte_h[1];
  assign _010_[2] = we_i[1] ? din_i[2] : tx_hold_byte_h[2];
  assign _010_[3] = we_i[1] ? din_i[3] : tx_hold_byte_h[3];
  assign _010_[4] = we_i[1] ? din_i[4] : tx_hold_byte_h[4];
  assign _010_[5] = we_i[1] ? din_i[5] : tx_hold_byte_h[5];
  assign _010_[6] = we_i[1] ? din_i[6] : tx_hold_byte_h[6];
  assign _010_[7] = we_i[1] ? din_i[7] : tx_hold_byte_h[7];
  assign _011_[0] = we_i[0] ? din_i[0] : tx_hold_byte_l[0];
  assign _011_[1] = we_i[0] ? din_i[1] : tx_hold_byte_l[1];
  assign _011_[2] = we_i[0] ? din_i[2] : tx_hold_byte_l[2];
  assign _011_[3] = we_i[0] ? din_i[3] : tx_hold_byte_l[3];
  assign _011_[4] = we_i[0] ? din_i[4] : tx_hold_byte_l[4];
  assign _011_[5] = we_i[0] ? din_i[5] : tx_hold_byte_l[5];
  assign _011_[6] = we_i[0] ? din_i[6] : tx_hold_byte_l[6];
  assign _011_[7] = we_i[0] ? din_i[7] : tx_hold_byte_l[7];
  assign _017_ = ~tx_go;
  assign _018_ = _016_ | _017_;
  assign _019_ = ~tx_cnt[3];
  assign _020_ = ~tx_cnt[2];
  assign _021_ = ~tx_cnt[0];
  assign _022_ = ~tx_cnt[1];
  assign _023_ = _022_ | _021_;
  assign _024_ = _023_ | _020_;
  assign _025_ = _024_ | _019_;
  assign _026_ = _025_ | _018_;
  assign _027_ = ~psync;
  assign _028_ = _027_ & tx_go;
  assign _029_ = _028_ & _026_;
  assign _030_ = _029_ | psync;
  assign _008_ = _030_ & rst;
  assign _031_ = psync & tx_hold_byte_l[0];
  assign _032_ = tx_hold_reg[0] & _027_;
  assign _033_ = _032_ & _018_;
  assign _034_ = _033_ | _031_;
  assign _012_[0] = _034_ & rst;
  assign _035_ = _018_ ? tx_hold_reg[10] : tx_hold_reg[9];
  assign _036_ = psync ? tx_hold_byte_h[2] : _035_;
  assign _012_[10] = _036_ & rst;
  assign _037_ = _018_ ? tx_hold_reg[11] : tx_hold_reg[10];
  assign _038_ = psync ? tx_hold_byte_h[3] : _037_;
  assign _012_[11] = _038_ & rst;
  assign _039_ = _018_ ? tx_hold_reg[12] : tx_hold_reg[11];
  assign _040_ = psync ? tx_hold_byte_h[4] : _039_;
  assign _012_[12] = _040_ & rst;
  assign _041_ = _018_ ? tx_hold_reg[13] : tx_hold_reg[12];
  assign _042_ = psync ? tx_hold_byte_h[5] : _041_;
  assign _012_[13] = _042_ & rst;
  assign _043_ = _018_ ? tx_hold_reg[14] : tx_hold_reg[13];
  assign _044_ = psync ? tx_hold_byte_h[6] : _043_;
  assign _012_[14] = _044_ & rst;
  assign _045_ = _018_ ? pcm_dout_o : tx_hold_reg[14];
  assign _046_ = psync ? tx_hold_byte_h[7] : _045_;
  assign _012_[15] = _046_ & rst;
  assign _047_ = _018_ ? tx_hold_reg[1] : tx_hold_reg[0];
  assign _048_ = psync ? tx_hold_byte_l[1] : _047_;
  assign _012_[1] = _048_ & rst;
  assign _049_ = _018_ ? tx_hold_reg[2] : tx_hold_reg[1];
  assign _050_ = psync ? tx_hold_byte_l[2] : _049_;
  assign _012_[2] = _050_ & rst;
  assign _051_ = _018_ ? tx_hold_reg[3] : tx_hold_reg[2];
  assign _052_ = psync ? tx_hold_byte_l[3] : _051_;
  assign _012_[3] = _052_ & rst;
  assign _053_ = _018_ ? tx_hold_reg[4] : tx_hold_reg[3];
  assign _054_ = psync ? tx_hold_byte_l[4] : _053_;
  assign _012_[4] = _054_ & rst;
  assign _055_ = _018_ ? tx_hold_reg[5] : tx_hold_reg[4];
  assign _056_ = psync ? tx_hold_byte_l[5] : _055_;
  assign _012_[5] = _056_ & rst;
  assign _057_ = _018_ ? tx_hold_reg[6] : tx_hold_reg[5];
  assign _058_ = psync ? tx_hold_byte_l[6] : _057_;
  assign _012_[6] = _058_ & rst;
  assign _059_ = _018_ ? tx_hold_reg[7] : tx_hold_reg[6];
  assign _060_ = psync ? tx_hold_byte_l[7] : _059_;
  assign _012_[7] = _060_ & rst;
  assign _061_ = _018_ ? tx_hold_reg[8] : tx_hold_reg[7];
  assign _062_ = psync ? tx_hold_byte_h[0] : _061_;
  assign _012_[8] = _062_ & rst;
  assign _063_ = _018_ ? tx_hold_reg[9] : tx_hold_reg[8];
  assign _064_ = psync ? tx_hold_byte_h[1] : _063_;
  assign _012_[9] = _064_ & rst;
  assign _065_ = _018_ ^ _021_;
  assign _007_[0] = _065_ & rst;
  assign _066_ = tx_cnt[1] ^ tx_cnt[0];
  assign _067_ = _018_ ? tx_cnt[1] : _066_;
  assign _007_[1] = _067_ & rst;
  assign _068_ = _023_ ^ _020_;
  assign _069_ = _018_ ? tx_cnt[2] : _068_;
  assign _007_[2] = _069_ & rst;
  assign _070_ = _024_ ^ _019_;
  assign _071_ = _018_ ? tx_cnt[3] : _070_;
  assign _007_[3] = _071_ & rst;
  assign _009_ = _016_ ? tx_go_r1 : tx_go;
  assign _006_ = _015_ ? pcm_din_i : rxd_t;
  assign _072_ = tx_go_r1 | tx_go;
  assign _073_ = _072_ & _015_;
  assign _074_ = _073_ ? rxd : rx_hold_reg[0];
  assign _004_[0] = _074_ & rst;
  assign _075_ = _073_ ? rx_hold_reg[9] : rx_hold_reg[10];
  assign _004_[10] = _075_ & rst;
  assign _076_ = _073_ ? rx_hold_reg[10] : rx_hold_reg[11];
  assign _004_[11] = _076_ & rst;
  assign _077_ = _073_ ? rx_hold_reg[11] : rx_hold_reg[12];
  assign _004_[12] = _077_ & rst;
  assign _078_ = _073_ ? rx_hold_reg[12] : rx_hold_reg[13];
  assign _004_[13] = _078_ & rst;
  assign _079_ = _073_ ? rx_hold_reg[13] : rx_hold_reg[14];
  assign _004_[14] = _079_ & rst;
  assign _080_ = _073_ ? rx_hold_reg[14] : rx_hold_reg[15];
  assign _004_[15] = _080_ & rst;
  assign _081_ = _073_ ? rx_hold_reg[0] : rx_hold_reg[1];
  assign _004_[1] = _081_ & rst;
  assign _082_ = _073_ ? rx_hold_reg[1] : rx_hold_reg[2];
  assign _004_[2] = _082_ & rst;
  assign _083_ = _073_ ? rx_hold_reg[2] : rx_hold_reg[3];
  assign _004_[3] = _083_ & rst;
  assign _084_ = _073_ ? rx_hold_reg[3] : rx_hold_reg[4];
  assign _004_[4] = _084_ & rst;
  assign _085_ = _073_ ? rx_hold_reg[4] : rx_hold_reg[5];
  assign _004_[5] = _085_ & rst;
  assign _086_ = _073_ ? rx_hold_reg[5] : rx_hold_reg[6];
  assign _004_[6] = _086_ & rst;
  assign _087_ = _073_ ? rx_hold_reg[6] : rx_hold_reg[7];
  assign _004_[7] = _087_ & rst;
  assign _088_ = _073_ ? rx_hold_reg[7] : rx_hold_reg[8];
  assign _004_[8] = _088_ & rst;
  assign _089_ = _073_ ? rx_hold_reg[8] : rx_hold_reg[9];
  assign _004_[9] = _089_ & rst;
  assign _090_ = ~_016_;
  assign _091_ = tx_go_r1 & _017_;
  assign _092_ = _091_ & _090_;
  assign _093_ = _092_ ? rx_hold_reg[0] : rx_reg[0];
  assign _005_[0] = _093_ & rst;
  assign _094_ = _092_ ? rx_hold_reg[10] : rx_reg[10];
  assign _005_[10] = _094_ & rst;
  assign _095_ = _092_ ? rx_hold_reg[11] : rx_reg[11];
  assign _005_[11] = _095_ & rst;
  assign _096_ = _092_ ? rx_hold_reg[12] : rx_reg[12];
  assign _005_[12] = _096_ & rst;
  assign _097_ = _092_ ? rx_hold_reg[13] : rx_reg[13];
  assign _005_[13] = _097_ & rst;
  assign _098_ = _092_ ? rx_hold_reg[14] : rx_reg[14];
  assign _005_[14] = _098_ & rst;
  assign _099_ = _092_ ? rx_hold_reg[15] : rx_reg[15];
  assign _005_[15] = _099_ & rst;
  assign _100_ = _092_ ? rx_hold_reg[1] : rx_reg[1];
  assign _005_[1] = _100_ & rst;
  assign _101_ = _092_ ? rx_hold_reg[2] : rx_reg[2];
  assign _005_[2] = _101_ & rst;
  assign _102_ = _092_ ? rx_hold_reg[3] : rx_reg[3];
  assign _005_[3] = _102_ & rst;
  assign _103_ = _092_ ? rx_hold_reg[4] : rx_reg[4];
  assign _005_[4] = _103_ & rst;
  assign _104_ = _092_ ? rx_hold_reg[5] : rx_reg[5];
  assign _005_[5] = _104_ & rst;
  assign _105_ = _092_ ? rx_hold_reg[6] : rx_reg[6];
  assign _005_[6] = _105_ & rst;
  assign _106_ = _092_ ? rx_hold_reg[7] : rx_reg[7];
  assign _005_[7] = _106_ & rst;
  assign _107_ = _092_ ? rx_hold_reg[8] : rx_reg[8];
  assign _005_[8] = _107_ & rst;
  assign _108_ = _092_ ? rx_hold_reg[9] : rx_reg[9];
  assign _005_[9] = _108_ & rst;
  assign _109_ = ssel[0] ? psa[7] : psa[6];
  assign _110_ = ssel[0] ? psa[5] : psa[4];
  assign _111_ = ssel[1] ? _109_ : _110_;
  assign _112_ = ssel[0] ? psa[3] : psa[2];
  assign _113_ = ssel[0] ? psa[1] : psa[0];
  assign _114_ = ssel[1] ? _112_ : _113_;
  assign _001_ = ssel[2] ? _111_ : _114_;
  assign dout_o[0] = re_i ? rx_reg[8] : rx_reg[0];
  assign dout_o[1] = re_i ? rx_reg[9] : rx_reg[1];
  assign dout_o[2] = re_i ? rx_reg[10] : rx_reg[2];
  assign dout_o[3] = re_i ? rx_reg[11] : rx_reg[3];
  assign dout_o[4] = re_i ? rx_reg[12] : rx_reg[4];
  assign dout_o[5] = re_i ? rx_reg[13] : rx_reg[5];
  assign dout_o[6] = re_i ? rx_reg[14] : rx_reg[6];
  assign dout_o[7] = re_i ? rx_reg[15] : rx_reg[7];
  always @(posedge clk)
      pclk_s <= pclk_t;
  always @(posedge clk)
      pclk_r <= pclk_s;
  always @(posedge clk)
      pcm_sync_r1 <= _000_;
  always @(posedge clk)
      psa[0] <= _002_[0];
  always @(posedge clk)
      psa[1] <= _002_[1];
  always @(posedge clk)
      psa[2] <= _002_[2];
  always @(posedge clk)
      psa[3] <= _002_[3];
  always @(posedge clk)
      psa[4] <= _002_[4];
  always @(posedge clk)
      psa[5] <= _002_[5];
  always @(posedge clk)
      psa[6] <= _002_[6];
  always @(posedge clk)
      psa[7] <= _002_[7];
  always @(posedge clk)
      pcm_sync_r2 <= _001_;
  always @(posedge clk)
      pcm_sync_r3 <= pcm_sync_r2;
  always @(posedge clk)
      psync <= _003_;
  always @(posedge clk)
      tx_hold_byte_h[0] <= _010_[0];
  always @(posedge clk)
      tx_hold_byte_h[1] <= _010_[1];
  always @(posedge clk)
      tx_hold_byte_h[2] <= _010_[2];
  always @(posedge clk)
      tx_hold_byte_h[3] <= _010_[3];
  always @(posedge clk)
      tx_hold_byte_h[4] <= _010_[4];
  always @(posedge clk)
      tx_hold_byte_h[5] <= _010_[5];
  always @(posedge clk)
      tx_hold_byte_h[6] <= _010_[6];
  always @(posedge clk)
      tx_hold_byte_h[7] <= _010_[7];
  always @(posedge clk)
      tx_hold_byte_l[0] <= _011_[0];
  always @(posedge clk)
      tx_hold_byte_l[1] <= _011_[1];
  always @(posedge clk)
      tx_hold_byte_l[2] <= _011_[2];
  always @(posedge clk)
      tx_hold_byte_l[3] <= _011_[3];
  always @(posedge clk)
      tx_hold_byte_l[4] <= _011_[4];
  always @(posedge clk)
      tx_hold_byte_l[5] <= _011_[5];
  always @(posedge clk)
      tx_hold_byte_l[6] <= _011_[6];
  always @(posedge clk)
      tx_hold_byte_l[7] <= _011_[7];
  always @(posedge clk)
      tx_go <= _008_;
  reg \tx_hold_reg_reg[0] ;
  always @(posedge clk)
      \tx_hold_reg_reg[0]  <= _012_[0];
  assign tx_hold_reg[0] = \tx_hold_reg_reg[0] ;
  reg \tx_hold_reg_reg[10] ;
  always @(posedge clk)
      \tx_hold_reg_reg[10]  <= _012_[10];
  assign tx_hold_reg[10] = \tx_hold_reg_reg[10] ;
  reg \tx_hold_reg_reg[11] ;
  always @(posedge clk)
      \tx_hold_reg_reg[11]  <= _012_[11];
  assign tx_hold_reg[11] = \tx_hold_reg_reg[11] ;
  reg \tx_hold_reg_reg[12] ;
  always @(posedge clk)
      \tx_hold_reg_reg[12]  <= _012_[12];
  assign tx_hold_reg[12] = \tx_hold_reg_reg[12] ;
  reg \tx_hold_reg_reg[13] ;
  always @(posedge clk)
      \tx_hold_reg_reg[13]  <= _012_[13];
  assign tx_hold_reg[13] = \tx_hold_reg_reg[13] ;
  reg \tx_hold_reg_reg[14] ;
  always @(posedge clk)
      \tx_hold_reg_reg[14]  <= _012_[14];
  assign tx_hold_reg[14] = \tx_hold_reg_reg[14] ;
  always @(posedge clk)
      pcm_dout_o <= _012_[15];
  reg \tx_hold_reg_reg[1] ;
  always @(posedge clk)
      \tx_hold_reg_reg[1]  <= _012_[1];
  assign tx_hold_reg[1] = \tx_hold_reg_reg[1] ;
  reg \tx_hold_reg_reg[2] ;
  always @(posedge clk)
      \tx_hold_reg_reg[2]  <= _012_[2];
  assign tx_hold_reg[2] = \tx_hold_reg_reg[2] ;
  reg \tx_hold_reg_reg[3] ;
  always @(posedge clk)
      \tx_hold_reg_reg[3]  <= _012_[3];
  assign tx_hold_reg[3] = \tx_hold_reg_reg[3] ;
  reg \tx_hold_reg_reg[4] ;
  always @(posedge clk)
      \tx_hold_reg_reg[4]  <= _012_[4];
  assign tx_hold_reg[4] = \tx_hold_reg_reg[4] ;
  reg \tx_hold_reg_reg[5] ;
  always @(posedge clk)
      \tx_hold_reg_reg[5]  <= _012_[5];
  assign tx_hold_reg[5] = \tx_hold_reg_reg[5] ;
  reg \tx_hold_reg_reg[6] ;
  always @(posedge clk)
      \tx_hold_reg_reg[6]  <= _012_[6];
  assign tx_hold_reg[6] = \tx_hold_reg_reg[6] ;
  reg \tx_hold_reg_reg[7] ;
  always @(posedge clk)
      \tx_hold_reg_reg[7]  <= _012_[7];
  assign tx_hold_reg[7] = \tx_hold_reg_reg[7] ;
  reg \tx_hold_reg_reg[8] ;
  always @(posedge clk)
      \tx_hold_reg_reg[8]  <= _012_[8];
  assign tx_hold_reg[8] = \tx_hold_reg_reg[8] ;
  reg \tx_hold_reg_reg[9] ;
  always @(posedge clk)
      \tx_hold_reg_reg[9]  <= _012_[9];
  assign tx_hold_reg[9] = \tx_hold_reg_reg[9] ;
  always @(posedge clk)
      tx_cnt[0] <= _007_[0];
  always @(posedge clk)
      tx_cnt[1] <= _007_[1];
  always @(posedge clk)
      tx_cnt[2] <= _007_[2];
  always @(posedge clk)
      tx_cnt[3] <= _007_[3];
  always @(posedge clk)
      tx_go_r1 <= _009_;
  always @(posedge clk)
      rxd_t <= _006_;
  always @(posedge clk)
      rxd <= rxd_t;
  always @(posedge clk)
      rx_hold_reg[0] <= _004_[0];
  always @(posedge clk)
      rx_hold_reg[10] <= _004_[10];
  always @(posedge clk)
      rx_hold_reg[11] <= _004_[11];
  always @(posedge clk)
      rx_hold_reg[12] <= _004_[12];
  always @(posedge clk)
      rx_hold_reg[13] <= _004_[13];
  always @(posedge clk)
      rx_hold_reg[14] <= _004_[14];
  always @(posedge clk)
      rx_hold_reg[15] <= _004_[15];
  always @(posedge clk)
      rx_hold_reg[1] <= _004_[1];
  always @(posedge clk)
      rx_hold_reg[2] <= _004_[2];
  always @(posedge clk)
      rx_hold_reg[3] <= _004_[3];
  always @(posedge clk)
      rx_hold_reg[4] <= _004_[4];
  always @(posedge clk)
      rx_hold_reg[5] <= _004_[5];
  always @(posedge clk)
      rx_hold_reg[6] <= _004_[6];
  always @(posedge clk)
      rx_hold_reg[7] <= _004_[7];
  always @(posedge clk)
      rx_hold_reg[8] <= _004_[8];
  always @(posedge clk)
      rx_hold_reg[9] <= _004_[9];
  always @(posedge clk)
      rx_reg[0] <= _005_[0];
  always @(posedge clk)
      rx_reg[10] <= _005_[10];
  always @(posedge clk)
      rx_reg[11] <= _005_[11];
  always @(posedge clk)
      rx_reg[12] <= _005_[12];
  always @(posedge clk)
      rx_reg[13] <= _005_[13];
  always @(posedge clk)
      rx_reg[14] <= _005_[14];
  always @(posedge clk)
      rx_reg[15] <= _005_[15];
  always @(posedge clk)
      rx_reg[1] <= _005_[1];
  always @(posedge clk)
      rx_reg[2] <= _005_[2];
  always @(posedge clk)
      rx_reg[3] <= _005_[3];
  always @(posedge clk)
      rx_reg[4] <= _005_[4];
  always @(posedge clk)
      rx_reg[5] <= _005_[5];
  always @(posedge clk)
      rx_reg[6] <= _005_[6];
  always @(posedge clk)
      rx_reg[7] <= _005_[7];
  always @(posedge clk)
      rx_reg[8] <= _005_[8];
  always @(posedge clk)
      rx_reg[9] <= _005_[9];
  always @(posedge clk)
      pclk_t <= pcm_clk_i;
  assign tx_hold_reg[15] = pcm_dout_o;
endmodule
