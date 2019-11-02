module usb_phy(clk, rst, phy_tx_mode, usb_rst, txdp, txdn, txoe, rxd, rxdp, rxdn, DataOut_i, TxValid_i, TxReady_o, RxValid_o, RxActive_o, RxError_o, DataIn_o, LineState_o);
  wire [4:0] _00_;
  wire _01_;
  wire _02_;
  wire _03_;
  wire _04_;
  wire _05_;
  wire _06_;
  wire _07_;
  wire _08_;
  wire _09_;
  wire _10_;
  wire _11_;
  wire _12_;
  wire _13_;
  wire _14_;
  wire _15_;
  wire _16_;
  wire _17_;
  wire _18_;
  wire _19_;
  wire _20_;
  output [7:0] DataIn_o;
  input [7:0] DataOut_i;
  output [1:0] LineState_o;
  output RxActive_o;
  output RxError_o;
  output RxValid_o;
  output TxReady_o;
  input TxValid_i;
  input clk;
  wire fs_ce;
  input phy_tx_mode;
  input rst;
  reg [4:0] rst_cnt;
  input rxd;
  input rxdn;
  input rxdp;
  output txdn;
  output txdp;
  output txoe;
  output usb_rst;
  reg usb_rst;
  assign _02_ = ~rst_cnt[0];
  assign _03_ = ~fs_ce;
  assign _04_ = usb_rst | _03_;
  assign _05_ = _04_ ^ _02_;
  assign _06_ = ~LineState_o[0];
  assign _07_ = ~LineState_o[1];
  assign _08_ = _07_ & _06_;
  assign _09_ = _08_ & rst;
  assign _00_[0] = _09_ & _05_;
  assign _10_ = rst_cnt[1] ^ rst_cnt[0];
  assign _11_ = _04_ ? rst_cnt[1] : _10_;
  assign _00_[1] = _11_ & _09_;
  assign _12_ = rst_cnt[1] & rst_cnt[0];
  assign _13_ = _12_ ^ rst_cnt[2];
  assign _14_ = _04_ ? rst_cnt[2] : _13_;
  assign _00_[2] = _14_ & _09_;
  assign _15_ = _12_ & rst_cnt[2];
  assign _16_ = _15_ ^ rst_cnt[3];
  assign _17_ = _04_ ? rst_cnt[3] : _16_;
  assign _00_[3] = _17_ & _09_;
  assign _18_ = _15_ & rst_cnt[3];
  assign _19_ = _18_ ^ rst_cnt[4];
  assign _20_ = _04_ ? rst_cnt[4] : _19_;
  assign _00_[4] = _20_ & _09_;
  assign _01_ = _18_ & rst_cnt[4];
  always @(posedge clk)
      rst_cnt[0] <= _00_[0];
  always @(posedge clk)
      rst_cnt[1] <= _00_[1];
  always @(posedge clk)
      rst_cnt[2] <= _00_[2];
  always @(posedge clk)
      rst_cnt[3] <= _00_[3];
  always @(posedge clk)
      rst_cnt[4] <= _00_[4];
  always @(posedge clk)
      usb_rst <= _01_;
  usb_rx_phy i_rx_phy (
    .DataIn_o(DataIn_o),
    .LineState(LineState_o),
    .RxActive_o(RxActive_o),
    .RxEn_i(txoe),
    .RxError_o(RxError_o),
    .RxValid_o(RxValid_o),
    .clk(clk),
    .fs_ce(fs_ce),
    .rst(rst),
    .rxd(rxd),
    .rxdn(rxdn),
    .rxdp(rxdp)
  );
  usb_tx_phy i_tx_phy (
    .DataOut_i(DataOut_i),
    .TxReady_o(TxReady_o),
    .TxValid_i(TxValid_i),
    .clk(clk),
    .fs_ce(fs_ce),
    .phy_mode(phy_tx_mode),
    .rst(rst),
    .txdn(txdn),
    .txdp(txdp),
    .txoe(txoe)
  );
endmodule

module usb_rx_phy(clk, rst, fs_ce, rxd, rxdp, rxdn, RxValid_o, RxActive_o, RxError_o, DataIn_o, RxEn_i, LineState);
  wire [2:0] _000_;
  wire _001_;
  wire _002_;
  wire [1:0] _003_;
  wire [2:0] _004_;
  wire [7:0] _005_;
  wire [2:0] _006_;
  wire _007_;
  wire _008_;
  wire _009_;
  wire _010_;
  wire _011_;
  wire _012_;
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
  wire _115_;
  wire _116_;
  wire _117_;
  wire _118_;
  wire _119_;
  wire _120_;
  wire _121_;
  wire _122_;
  wire _123_;
  wire _124_;
  wire _125_;
  wire _126_;
  wire _127_;
  wire _128_;
  wire _129_;
  wire _130_;
  wire _131_;
  wire _132_;
  wire _133_;
  wire _134_;
  wire _135_;
  wire _136_;
  wire _137_;
  wire _138_;
  wire _139_;
  wire _140_;
  wire _141_;
  wire _142_;
  wire _143_;
  wire _144_;
  wire _145_;
  wire _146_;
  wire _147_;
  wire _148_;
  wire _149_;
  wire _150_;
  wire _151_;
  wire _152_;
  wire _153_;
  wire _154_;
  wire _155_;
  wire _156_;
  wire _157_;
  wire _158_;
  wire _159_;
  wire _160_;
  wire _161_;
  wire _162_;
  wire _163_;
  wire _164_;
  wire _165_;
  wire _166_;
  wire _167_;
  wire _168_;
  wire _169_;
  wire _170_;
  wire _171_;
  wire _172_;
  wire _173_;
  wire _174_;
  wire _175_;
  wire _176_;
  wire _177_;
  wire _178_;
  wire _179_;
  wire _180_;
  wire _181_;
  output [7:0] DataIn_o;
  reg [7:0] DataIn_o;
  output [1:0] LineState;
  reg [1:0] LineState;
  output RxActive_o;
  reg RxActive_o;
  input RxEn_i;
  output RxError_o;
  output RxValid_o;
  reg RxValid_o;
  reg [2:0] bit_cnt;
  reg bit_stuff_err;
  reg byte_err;
  input clk;
  reg [1:0] dpll_state;
  output fs_ce;
  reg fs_ce;
  wire fs_ce_d;
  reg fs_ce_r1;
  reg fs_ce_r2;
  reg [2:0] fs_state;
  wire [7:0] hold_reg;
  reg lock_en;
  reg [2:0] one_cnt;
  input rst;
  wire rx_active;
  wire rx_en;
  wire rx_valid;
  reg rx_valid1;
  reg rx_valid_r;
  input rxd;
  reg rxd_r;
  reg rxd_s;
  reg rxd_s0;
  reg rxd_s1;
  input rxdn;
  reg rxdn_s;
  reg rxdn_s0;
  wire rxdn_s1;
  reg rxdn_s_r;
  input rxdp;
  reg rxdp_s;
  reg rxdp_s0;
  wire rxdp_s1;
  reg rxdp_s_r;
  reg sd_nrzi;
  reg sd_r;
  wire se0;
  reg se0_r;
  reg se0_s;
  reg shift_en;
  reg sync_err;
  assign _166_ = ~fs_state[0];
  assign _167_ = ~fs_state[1];
  assign _168_ = _167_ & _166_;
  assign _169_ = _168_ & fs_state[2];
  assign _170_ = fs_state[1] & _166_;
  assign _171_ = _170_ | _169_;
  assign _172_ = ~lock_en;
  assign _173_ = ~rxdn_s;
  assign _174_ = rxdp_s | _173_;
  assign _175_ = _174_ | _172_;
  assign _176_ = _175_ & _171_;
  assign _177_ = ~fs_state[2];
  assign _178_ = _167_ & fs_state[0];
  assign _179_ = _178_ & _177_;
  assign _180_ = fs_state[1] & fs_state[0];
  assign _181_ = _180_ & _177_;
  assign _021_ = _181_ | _179_;
  assign _022_ = ~rxdp_s;
  assign _023_ = _022_ | rxdn_s;
  assign _024_ = _023_ | _172_;
  assign _025_ = _024_ & _021_;
  assign _026_ = _178_ & fs_state[2];
  assign _027_ = _026_ & _024_;
  assign _028_ = _027_ & _175_;
  assign _029_ = _028_ | _025_;
  assign _030_ = _029_ | _176_;
  assign _031_ = _026_ | _021_;
  assign _032_ = _031_ | _171_;
  assign _033_ = ~RxActive_o;
  assign _034_ = rxdp_s | rxdn_s;
  assign _035_ = ~se0_s;
  assign _036_ = _033_ & fs_ce;
  assign _037_ = _036_ & _035_;
  assign _038_ = _037_ & _034_;
  assign _039_ = _038_ & _032_;
  assign _020_ = _039_ & _030_;
  assign _015_ = rxdp_s0 & LineState[0];
  assign _013_ = rxdn_s0 & LineState[1];
  assign se0 = ~_034_;
  assign _040_ = ~one_cnt[0];
  assign _041_ = one_cnt[1] & _040_;
  assign _042_ = _041_ & one_cnt[2];
  assign _043_ = fs_ce & sd_nrzi;
  assign _044_ = _043_ & RxActive_o;
  assign _045_ = _044_ & _034_;
  assign _001_ = _045_ & _042_;
  assign _046_ = rx_valid1 & fs_ce;
  assign _047_ = ~_046_;
  assign _048_ = _047_ | _042_;
  assign _009_ = ~_048_;
  assign _049_ = bit_cnt[2] | bit_cnt[1];
  assign _050_ = ~se0_r;
  assign _051_ = _050_ & RxActive_o;
  assign _052_ = _051_ & se0;
  assign _002_ = _052_ & _049_;
  assign _053_ = bit_stuff_err | byte_err;
  assign RxError_o = _053_ | sync_err;
  assign _014_ = _015_ | rxdp_s_r;
  assign _012_ = _013_ | rxdn_s_r;
  assign _054_ = _022_ & rxdn_s;
  assign _055_ = _168_ & _177_;
  assign _056_ = fs_state[2] ? _168_ : _170_;
  assign _057_ = _056_ | _055_;
  assign _058_ = _170_ & fs_state[2];
  assign _059_ = _026_ | _058_;
  assign _060_ = _059_ | _021_;
  assign _061_ = _060_ | _057_;
  assign _062_ = _054_ & lock_en;
  assign _063_ = _027_ & _062_;
  assign _064_ = _061_ ? _063_ : _054_;
  assign _065_ = _064_ & _038_;
  assign _066_ = _065_ & lock_en;
  assign _067_ = ~rx_valid_r;
  assign _068_ = _034_ | _067_;
  assign _069_ = _068_ & RxActive_o;
  assign _070_ = _069_ | _066_;
  assign _007_ = _070_ & rst;
  assign _071_ = ~fs_ce;
  assign _072_ = rx_valid_r & _071_;
  assign _010_ = _072_ | RxValid_o;
  assign _017_ = fs_ce ? rxd_s : sd_r;
  assign _073_ = ~rxd_s;
  assign _074_ = sd_r | _073_;
  assign _075_ = RxActive_o & fs_ce;
  assign _076_ = ~sd_r;
  assign _077_ = _076_ | rxd_s;
  assign _078_ = _077_ & _075_;
  assign _079_ = _078_ & _074_;
  assign _080_ = ~_075_;
  assign _081_ = _080_ & sd_nrzi;
  assign _082_ = _081_ | _079_;
  assign _083_ = _082_ | _033_;
  assign _016_ = _083_ & rst;
  assign _084_ = ~_042_;
  assign _085_ = _084_ & sd_nrzi;
  assign _086_ = fs_ce & _040_;
  assign _087_ = _086_ & _085_;
  assign _088_ = _071_ & one_cnt[0];
  assign _089_ = _088_ | _087_;
  assign _090_ = rst & shift_en;
  assign _006_[0] = _090_ & _089_;
  assign _091_ = one_cnt[1] ^ one_cnt[0];
  assign _092_ = _091_ & fs_ce;
  assign _093_ = _092_ & _085_;
  assign _094_ = _071_ & one_cnt[1];
  assign _095_ = _094_ | _093_;
  assign _006_[1] = _095_ & _090_;
  assign _096_ = one_cnt[1] & one_cnt[0];
  assign _097_ = _096_ ^ one_cnt[2];
  assign _098_ = _085_ & fs_ce;
  assign _099_ = _098_ & _097_;
  assign _100_ = _071_ & one_cnt[2];
  assign _101_ = _100_ | _099_;
  assign _006_[2] = _101_ & _090_;
  assign _102_ = _065_ | RxActive_o;
  assign _019_ = _071_ ? shift_en : _102_;
  assign _103_ = shift_en & fs_ce;
  assign _104_ = _103_ & _084_;
  assign _005_[0] = _104_ ? DataIn_o[1] : DataIn_o[0];
  assign _005_[1] = _104_ ? DataIn_o[2] : DataIn_o[1];
  assign _005_[2] = _104_ ? DataIn_o[3] : DataIn_o[2];
  assign _005_[3] = _104_ ? DataIn_o[4] : DataIn_o[3];
  assign _005_[4] = _104_ ? DataIn_o[5] : DataIn_o[4];
  assign _005_[5] = _104_ ? DataIn_o[6] : DataIn_o[5];
  assign _005_[6] = _104_ ? DataIn_o[7] : DataIn_o[6];
  assign _005_[7] = _104_ ? sd_nrzi : DataIn_o[7];
  assign _105_ = _084_ & fs_ce;
  assign _106_ = _105_ ^ bit_cnt[0];
  assign _000_[0] = _106_ & _090_;
  assign _107_ = bit_cnt[1] ^ bit_cnt[0];
  assign _108_ = _105_ ? _107_ : bit_cnt[1];
  assign _000_[1] = _108_ & _090_;
  assign _109_ = bit_cnt[1] & bit_cnt[0];
  assign _110_ = _109_ ^ bit_cnt[2];
  assign _111_ = _105_ ? _110_ : bit_cnt[2];
  assign _000_[2] = _111_ & _090_;
  assign _112_ = _109_ & bit_cnt[2];
  assign _113_ = _112_ & _105_;
  assign _114_ = _048_ & rx_valid1;
  assign _115_ = _114_ | _113_;
  assign _008_ = _115_ & rst;
  assign _116_ = rxd_s0 & rxd_s1;
  assign _117_ = rxd_s0 | rxd_s1;
  assign _118_ = ~_116_;
  assign _119_ = _118_ & rxd_s;
  assign _120_ = _119_ & _117_;
  assign _011_ = _120_ | _116_;
  assign _018_ = _071_ ? se0_s : se0;
  assign _121_ = ~rst;
  assign _122_ = ~dpll_state[0];
  assign _123_ = _122_ & dpll_state[1];
  assign _124_ = rxd_r ^ rxd_s;
  assign _125_ = _124_ & lock_en;
  assign _126_ = ~_125_;
  assign _127_ = _126_ & _123_;
  assign _128_ = ~dpll_state[1];
  assign _129_ = _122_ & _128_;
  assign fs_ce_d = dpll_state[0] & _128_;
  assign _130_ = _125_ ? fs_ce_d : _129_;
  assign _131_ = _130_ | _127_;
  assign _132_ = _122_ | _128_;
  assign _133_ = _132_ & rst;
  assign _134_ = _133_ & _131_;
  assign _003_[0] = _134_ | _121_;
  assign _135_ = fs_ce_d | _127_;
  assign _003_[1] = _135_ & _133_;
  assign _136_ = _062_ | fs_state[0];
  assign _137_ = _136_ & _055_;
  assign _138_ = _062_ & _058_;
  assign _139_ = _170_ & _177_;
  assign _140_ = _062_ & _139_;
  assign _141_ = _062_ & _169_;
  assign _142_ = _141_ | _140_;
  assign _143_ = _142_ | _138_;
  assign _144_ = _143_ | _137_;
  assign _145_ = _061_ & _038_;
  assign _146_ = _145_ & _144_;
  assign _147_ = ~_038_;
  assign _148_ = _147_ & fs_state[0];
  assign _149_ = _148_ | _146_;
  assign _004_[0] = _149_ & rst;
  assign _150_ = rxdp_s & _173_;
  assign _151_ = _150_ & lock_en;
  assign _152_ = _026_ & _151_;
  assign _153_ = _152_ | _138_;
  assign _154_ = _151_ & _179_;
  assign _155_ = _154_ | _140_;
  assign _156_ = _155_ | _153_;
  assign _157_ = _156_ & _145_;
  assign _158_ = _147_ & fs_state[1];
  assign _159_ = _158_ | _157_;
  assign _004_[1] = _159_ & rst;
  assign _160_ = _151_ & _181_;
  assign _161_ = _160_ | _141_;
  assign _162_ = _161_ | _153_;
  assign _163_ = _162_ & _145_;
  assign _164_ = _147_ & fs_state[2];
  assign _165_ = _164_ | _163_;
  assign _004_[2] = _165_ & rst;
  always @(posedge clk)
      lock_en <= RxEn_i;
  always @(posedge clk)
      sync_err <= _020_;
  always @(posedge clk)
      rxd_s0 <= rxd;
  always @(posedge clk)
      rxd_s1 <= rxd_s0;
  always @(posedge clk)
      rxd_s <= _011_;
  always @(posedge clk)
      rxdp_s0 <= rxdp;
  always @(posedge clk)
      LineState[0] <= rxdp_s0;
  always @(posedge clk)
      rxdp_s_r <= _015_;
  always @(posedge clk)
      rxdp_s <= _014_;
  always @(posedge clk)
      rxdn_s0 <= rxdn;
  always @(posedge clk)
      LineState[1] <= rxdn_s0;
  always @(posedge clk)
      rxdn_s_r <= _013_;
  always @(posedge clk)
      rxdn_s <= _012_;
  always @(posedge clk)
      se0_s <= _018_;
  always @(posedge clk)
      rxd_r <= rxd_s;
  always @(posedge clk)
      dpll_state[0] <= _003_[0];
  always @(posedge clk)
      dpll_state[1] <= _003_[1];
  always @(posedge clk)
      fs_ce_r1 <= fs_ce_d;
  always @(posedge clk)
      fs_ce_r2 <= fs_ce_r1;
  always @(posedge clk)
      fs_ce <= fs_ce_r2;
  always @(posedge clk)
      fs_state[0] <= _004_[0];
  always @(posedge clk)
      fs_state[1] <= _004_[1];
  always @(posedge clk)
      fs_state[2] <= _004_[2];
  always @(posedge clk)
      RxActive_o <= _007_;
  always @(posedge clk)
      rx_valid_r <= _010_;
  always @(posedge clk)
      sd_r <= _017_;
  always @(posedge clk)
      sd_nrzi <= _016_;
  always @(posedge clk)
      one_cnt[0] <= _006_[0];
  always @(posedge clk)
      one_cnt[1] <= _006_[1];
  always @(posedge clk)
      one_cnt[2] <= _006_[2];
  always @(posedge clk)
      bit_stuff_err <= _001_;
  always @(posedge clk)
      shift_en <= _019_;
  always @(posedge clk)
      DataIn_o[0] <= _005_[0];
  always @(posedge clk)
      DataIn_o[1] <= _005_[1];
  always @(posedge clk)
      DataIn_o[2] <= _005_[2];
  always @(posedge clk)
      DataIn_o[3] <= _005_[3];
  always @(posedge clk)
      DataIn_o[4] <= _005_[4];
  always @(posedge clk)
      DataIn_o[5] <= _005_[5];
  always @(posedge clk)
      DataIn_o[6] <= _005_[6];
  always @(posedge clk)
      DataIn_o[7] <= _005_[7];
  always @(posedge clk)
      bit_cnt[0] <= _000_[0];
  always @(posedge clk)
      bit_cnt[1] <= _000_[1];
  always @(posedge clk)
      bit_cnt[2] <= _000_[2];
  always @(posedge clk)
      rx_valid1 <= _008_;
  always @(posedge clk)
      RxValid_o <= _009_;
  always @(posedge clk)
      se0_r <= se0;
  always @(posedge clk)
      byte_err <= _002_;
  assign hold_reg = DataIn_o;
  assign rx_active = RxActive_o;
  assign rx_en = lock_en;
  assign rx_valid = RxValid_o;
  assign rxdn_s1 = LineState[1];
  assign rxdp_s1 = LineState[0];
endmodule

module usb_tx_phy(clk, rst, fs_ce, phy_mode, txdp, txdn, txoe, DataOut_i, TxValid_i, TxReady_o);
  wire _000_;
  wire _001_;
  wire _002_;
  wire _003_;
  wire _004_;
  wire _005_;
  wire [2:0] _006_;
  wire _007_;
  wire [7:0] _008_;
  wire [2:0] _009_;
  wire _010_;
  wire _011_;
  wire _012_;
  wire _013_;
  wire [2:0] _014_;
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
  wire _115_;
  wire _116_;
  wire _117_;
  wire _118_;
  wire _119_;
  wire _120_;
  wire _121_;
  wire _122_;
  wire _123_;
  wire _124_;
  wire _125_;
  wire _126_;
  wire _127_;
  wire _128_;
  wire _129_;
  wire _130_;
  wire _131_;
  wire _132_;
  wire _133_;
  wire _134_;
  wire _135_;
  wire _136_;
  wire _137_;
  wire _138_;
  wire _139_;
  wire _140_;
  wire _141_;
  wire _142_;
  wire _143_;
  wire _144_;
  wire _145_;
  wire _146_;
  wire _147_;
  wire _148_;
  wire _149_;
  wire _150_;
  wire _151_;
  wire _152_;
  wire _153_;
  wire _154_;
  wire _155_;
  wire _156_;
  wire _157_;
  wire _158_;
  wire _159_;
  wire _160_;
  wire _161_;
  wire _162_;
  wire _163_;
  wire _164_;
  wire _165_;
  wire _166_;
  wire _167_;
  wire _168_;
  wire _169_;
  wire _170_;
  wire _171_;
  wire _172_;
  wire _173_;
  wire _174_;
  wire _175_;
  wire _176_;
  wire _177_;
  wire _178_;
  wire _179_;
  wire _180_;
  wire _181_;
  wire _182_;
  wire _183_;
  wire _184_;
  wire _185_;
  input [7:0] DataOut_i;
  output TxReady_o;
  reg TxReady_o;
  input TxValid_i;
  reg append_eop;
  reg append_eop_sync1;
  reg append_eop_sync2;
  reg append_eop_sync3;
  reg append_eop_sync4;
  reg [2:0] bit_cnt;
  input clk;
  reg data_done;
  wire eop_done;
  input fs_ce;
  reg [7:0] hold_reg;
  reg [7:0] hold_reg_d;
  reg ld_data;
  wire ld_data_d;
  reg [2:0] one_cnt;
  input phy_mode;
  input rst;
  reg sd_bs_o;
  reg sd_nrzi_o;
  reg sd_raw_o;
  reg sft_done;
  reg sft_done_r;
  reg [2:0] state;
  reg tx_ip;
  reg tx_ip_sync;
  wire tx_ready_d;
  output txdn;
  reg txdn;
  output txdp;
  reg txdp;
  output txoe;
  reg txoe;
  reg txoe_r1;
  reg txoe_r2;
  assign _178_ = ~state[2];
  assign _179_ = ~state[1];
  assign _180_ = _179_ & state[0];
  assign _181_ = _180_ & _178_;
  assign _182_ = ~state[0];
  assign _183_ = state[1] & _182_;
  assign _184_ = _183_ & _178_;
  assign _185_ = _184_ | _181_;
  assign _022_ = ~sft_done;
  assign _023_ = sft_done_r | _022_;
  assign _024_ = ~_023_;
  assign _025_ = _024_ & _181_;
  assign _026_ = _024_ & data_done;
  assign _027_ = _026_ & _184_;
  assign _028_ = _027_ | _025_;
  assign ld_data_d = _028_ & _185_;
  assign _029_ = ~one_cnt[0];
  assign _030_ = one_cnt[1] & _029_;
  assign _031_ = _030_ & one_cnt[2];
  assign _032_ = ~_031_;
  assign _033_ = bit_cnt[1] & bit_cnt[0];
  assign _034_ = _033_ & bit_cnt[2];
  assign _013_ = _034_ & _032_;
  assign _035_ = rst & TxValid_i;
  assign _000_ = _035_ & ld_data_d;
  assign _036_ = _179_ & _182_;
  assign _037_ = _036_ & _178_;
  assign _038_ = _037_ & TxValid_i;
  assign _039_ = ~append_eop_sync3;
  assign _040_ = tx_ip & _039_;
  assign _041_ = _040_ | _038_;
  assign _015_ = _041_ & rst;
  assign _042_ = fs_ce ? tx_ip : tx_ip_sync;
  assign _016_ = _042_ & rst;
  assign _043_ = ~tx_ip;
  assign _044_ = _043_ & TxValid_i;
  assign _045_ = data_done & TxValid_i;
  assign _046_ = _045_ | _044_;
  assign _007_ = _046_ & rst;
  assign _047_ = ~bit_cnt[0];
  assign _048_ = ~fs_ce;
  assign _049_ = _031_ | _048_;
  assign _050_ = _049_ ^ _047_;
  assign _051_ = tx_ip_sync & rst;
  assign _006_[0] = _051_ & _050_;
  assign _052_ = bit_cnt[1] ^ bit_cnt[0];
  assign _053_ = _049_ ? bit_cnt[1] : _052_;
  assign _006_[1] = _053_ & _051_;
  assign _054_ = _033_ ^ bit_cnt[2];
  assign _055_ = _049_ ? bit_cnt[2] : _054_;
  assign _006_[2] = _055_ & _051_;
  assign _056_ = bit_cnt[1] & _047_;
  assign _057_ = _056_ & bit_cnt[2];
  assign _058_ = ~bit_cnt[1];
  assign _059_ = _058_ & _047_;
  assign _060_ = _059_ & bit_cnt[2];
  assign _061_ = _058_ & bit_cnt[0];
  assign _062_ = _061_ & bit_cnt[2];
  assign _063_ = _062_ | _060_;
  assign _064_ = _063_ | _057_;
  assign _065_ = ~bit_cnt[2];
  assign _066_ = _033_ & _065_;
  assign _067_ = _059_ & _065_;
  assign _068_ = _061_ & _065_;
  assign _069_ = _056_ & _065_;
  assign _070_ = _065_ | _064_;
  assign _071_ = _057_ & hold_reg_d[6];
  assign _072_ = _060_ & hold_reg_d[4];
  assign _073_ = _062_ & hold_reg_d[5];
  assign _074_ = _073_ | _072_;
  assign _075_ = _074_ | _071_;
  assign _076_ = _067_ & hold_reg_d[0];
  assign _077_ = _068_ & hold_reg_d[1];
  assign _078_ = _077_ | _076_;
  assign _079_ = _069_ & hold_reg_d[2];
  assign _080_ = _066_ & hold_reg_d[3];
  assign _081_ = _080_ | _079_;
  assign _082_ = _081_ | _078_;
  assign _083_ = _082_ | _075_;
  assign _084_ = _070_ ? _083_ : hold_reg_d[7];
  assign _012_ = _084_ & tx_ip_sync;
  assign _085_ = ~_038_;
  assign _086_ = ld_data ? DataOut_i[0] : hold_reg[0];
  assign _008_[0] = _086_ & _085_;
  assign _087_ = ld_data ? DataOut_i[1] : hold_reg[1];
  assign _008_[1] = _087_ & _085_;
  assign _088_ = ld_data ? DataOut_i[2] : hold_reg[2];
  assign _008_[2] = _088_ & _085_;
  assign _089_ = ld_data ? DataOut_i[3] : hold_reg[3];
  assign _008_[3] = _089_ & _085_;
  assign _090_ = ld_data ? DataOut_i[4] : hold_reg[4];
  assign _008_[4] = _090_ & _085_;
  assign _091_ = ld_data ? DataOut_i[5] : hold_reg[5];
  assign _008_[5] = _091_ & _085_;
  assign _092_ = ld_data ? DataOut_i[6] : hold_reg[6];
  assign _008_[6] = _092_ & _085_;
  assign _093_ = ld_data ? DataOut_i[7] : hold_reg[7];
  assign _008_[7] = _093_ | _038_;
  assign _094_ = _032_ & sd_raw_o;
  assign _095_ = fs_ce & _029_;
  assign _096_ = _095_ & _094_;
  assign _097_ = _048_ & one_cnt[0];
  assign _098_ = _097_ | _096_;
  assign _009_[0] = _098_ & _051_;
  assign _099_ = one_cnt[1] ^ one_cnt[0];
  assign _100_ = _099_ & fs_ce;
  assign _101_ = _100_ & _094_;
  assign _102_ = _048_ & one_cnt[1];
  assign _103_ = _102_ | _101_;
  assign _009_[1] = _103_ & _051_;
  assign _104_ = one_cnt[1] & one_cnt[0];
  assign _105_ = _104_ ^ one_cnt[2];
  assign _106_ = _094_ & fs_ce;
  assign _107_ = _106_ & _105_;
  assign _108_ = _048_ & one_cnt[2];
  assign _109_ = _108_ | _107_;
  assign _009_[2] = _109_ & _051_;
  assign _110_ = tx_ip_sync & fs_ce;
  assign _111_ = _110_ & _094_;
  assign _112_ = sd_bs_o & _048_;
  assign _113_ = _112_ | _111_;
  assign _010_ = _113_ & rst;
  assign _114_ = ~rst;
  assign _115_ = ~tx_ip_sync;
  assign _116_ = ~txoe_r1;
  assign _117_ = _116_ | _115_;
  assign _118_ = ~sd_nrzi_o;
  assign _119_ = sd_bs_o ^ _118_;
  assign _120_ = _048_ ? sd_nrzi_o : _119_;
  assign _121_ = _120_ | _117_;
  assign _011_ = _121_ | _114_;
  assign _122_ = _023_ | data_done;
  assign _123_ = ~_122_;
  assign _124_ = _123_ & _184_;
  assign _125_ = ~append_eop_sync2;
  assign _126_ = append_eop & _125_;
  assign _127_ = _126_ | _124_;
  assign _001_ = _127_ & rst;
  assign _128_ = fs_ce ? append_eop : append_eop_sync1;
  assign _002_ = _128_ & rst;
  assign _129_ = fs_ce ? append_eop_sync1 : append_eop_sync2;
  assign _003_ = _129_ & rst;
  assign _130_ = ~append_eop_sync4;
  assign _131_ = _130_ & append_eop_sync3;
  assign _132_ = _131_ | append_eop_sync2;
  assign _133_ = _048_ ? append_eop_sync3 : _132_;
  assign _004_ = _133_ & rst;
  assign _134_ = fs_ce ? append_eop_sync3 : append_eop_sync4;
  assign _005_ = _134_ & rst;
  assign _135_ = fs_ce ? tx_ip_sync : txoe_r1;
  assign _020_ = _135_ & rst;
  assign _136_ = fs_ce ? txoe_r1 : txoe_r2;
  assign _021_ = _136_ & rst;
  assign _137_ = ~txoe_r2;
  assign _138_ = _116_ & fs_ce;
  assign _139_ = _138_ & _137_;
  assign _140_ = txoe & _048_;
  assign _141_ = _140_ | _139_;
  assign _019_ = _141_ | _114_;
  assign _142_ = ~phy_mode;
  assign _143_ = sd_nrzi_o & _039_;
  assign _144_ = _142_ ? sd_nrzi_o : _143_;
  assign _145_ = _048_ ? txdp : _144_;
  assign _018_ = _145_ | _114_;
  assign _146_ = _118_ & _039_;
  assign _147_ = _142_ ? append_eop_sync3 : _146_;
  assign _148_ = _048_ ? txdn : _147_;
  assign _017_ = _148_ & rst;
  assign _149_ = _036_ & state[2];
  assign _150_ = state[1] & state[0];
  assign _151_ = _150_ & _178_;
  assign _152_ = _151_ | _037_;
  assign _153_ = _152_ | _149_;
  assign _154_ = _153_ | _185_;
  assign _155_ = _048_ | append_eop_sync3;
  assign _156_ = ~_155_;
  assign _157_ = _156_ | state[0];
  assign _158_ = _157_ & _149_;
  assign _159_ = state[0] & _039_;
  assign _160_ = _159_ & _151_;
  assign _161_ = _023_ & state[0];
  assign _162_ = _161_ & _181_;
  assign _163_ = _162_ | _038_;
  assign _164_ = _163_ | _160_;
  assign _165_ = _164_ | _158_;
  assign _166_ = _165_ | _124_;
  assign _167_ = state[0] & _048_;
  assign _168_ = _154_ ? _166_ : _167_;
  assign _014_[0] = _168_ & rst;
  assign _169_ = _160_ | _025_;
  assign _170_ = _169_ | _184_;
  assign _171_ = state[1] & _048_;
  assign _172_ = _154_ ? _170_ : _171_;
  assign _014_[1] = _172_ & rst;
  assign _173_ = state[2] | append_eop_sync3;
  assign _174_ = _173_ & _151_;
  assign _175_ = _149_ | _174_;
  assign _176_ = state[2] & _048_;
  assign _177_ = _154_ ? _175_ : _176_;
  assign _014_[2] = _177_ & rst;
  always @(posedge clk)
      TxReady_o <= _000_;
  always @(posedge clk)
      ld_data <= ld_data_d;
  always @(posedge clk)
      tx_ip <= _015_;
  always @(posedge clk)
      tx_ip_sync <= _016_;
  always @(posedge clk)
      data_done <= _007_;
  always @(posedge clk)
      bit_cnt[0] <= _006_[0];
  always @(posedge clk)
      bit_cnt[1] <= _006_[1];
  always @(posedge clk)
      bit_cnt[2] <= _006_[2];
  always @(posedge clk)
      sd_raw_o <= _012_;
  always @(posedge clk)
      sft_done <= _013_;
  always @(posedge clk)
      sft_done_r <= sft_done;
  always @(posedge clk)
      hold_reg[0] <= _008_[0];
  always @(posedge clk)
      hold_reg[1] <= _008_[1];
  always @(posedge clk)
      hold_reg[2] <= _008_[2];
  always @(posedge clk)
      hold_reg[3] <= _008_[3];
  always @(posedge clk)
      hold_reg[4] <= _008_[4];
  always @(posedge clk)
      hold_reg[5] <= _008_[5];
  always @(posedge clk)
      hold_reg[6] <= _008_[6];
  always @(posedge clk)
      hold_reg[7] <= _008_[7];
  always @(posedge clk)
      hold_reg_d[0] <= hold_reg[0];
  always @(posedge clk)
      hold_reg_d[1] <= hold_reg[1];
  always @(posedge clk)
      hold_reg_d[2] <= hold_reg[2];
  always @(posedge clk)
      hold_reg_d[3] <= hold_reg[3];
  always @(posedge clk)
      hold_reg_d[4] <= hold_reg[4];
  always @(posedge clk)
      hold_reg_d[5] <= hold_reg[5];
  always @(posedge clk)
      hold_reg_d[6] <= hold_reg[6];
  always @(posedge clk)
      hold_reg_d[7] <= hold_reg[7];
  always @(posedge clk)
      one_cnt[0] <= _009_[0];
  always @(posedge clk)
      one_cnt[1] <= _009_[1];
  always @(posedge clk)
      one_cnt[2] <= _009_[2];
  always @(posedge clk)
      sd_bs_o <= _010_;
  always @(posedge clk)
      sd_nrzi_o <= _011_;
  always @(posedge clk)
      append_eop <= _001_;
  always @(posedge clk)
      append_eop_sync1 <= _002_;
  always @(posedge clk)
      append_eop_sync2 <= _003_;
  always @(posedge clk)
      append_eop_sync3 <= _004_;
  always @(posedge clk)
      append_eop_sync4 <= _005_;
  always @(posedge clk)
      txoe_r1 <= _020_;
  always @(posedge clk)
      txoe_r2 <= _021_;
  always @(posedge clk)
      txoe <= _019_;
  always @(posedge clk)
      txdp <= _018_;
  always @(posedge clk)
      txdn <= _017_;
  always @(posedge clk)
      state[0] <= _014_[0];
  always @(posedge clk)
      state[1] <= _014_[1];
  always @(posedge clk)
      state[2] <= _014_[2];
  assign eop_done = append_eop_sync3;
  assign tx_ready_d = ld_data_d;
endmodule
