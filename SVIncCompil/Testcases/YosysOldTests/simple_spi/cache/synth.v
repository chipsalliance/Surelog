module \$paramod\fifo4\dw=8 (clk, rst, clr, din, we, dout, re, full, empty);
  wire _000_;
  wire [1:0] _001_;
  wire [1:0] _002_;
  wire _003_;
  wire _004_;
  wire _005_;
  wire _006_;
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
  wire [7:0] _064_;
  wire [7:0] _065_;
  wire [7:0] _066_;
  wire [7:0] _067_;
  input clk;
  input clr;
  input [8:1] din;
  output [8:1] dout;
  output empty;
  output full;
  reg gb;
  reg [8:1] \mem[0] ;
  reg [8:1] \mem[1] ;
  reg [8:1] \mem[2] ;
  reg [8:1] \mem[3] ;
  input re;
  reg [1:0] rp;
  input rst;
  input we;
  reg [1:0] wp;
  assign _060_ = ~gb;
  assign _061_ = ~rp[1];
  assign _062_ = _061_ ^ wp[1];
  assign _063_ = ~wp[0];
  assign _003_ = rp[0] ^ _063_;
  assign _004_ = _003_ & _062_;
  assign empty = _004_ & _060_;
  assign full = _004_ & gb;
  assign _005_ = rp[0] ? \mem[3] [1] : \mem[2] [1];
  assign _006_ = rp[0] ? \mem[1] [1] : \mem[0] [1];
  assign dout[1] = rp[1] ? _005_ : _006_;
  assign _007_ = rp[0] ? \mem[3] [2] : \mem[2] [2];
  assign _008_ = rp[0] ? \mem[1] [2] : \mem[0] [2];
  assign dout[2] = rp[1] ? _007_ : _008_;
  assign _009_ = rp[0] ? \mem[3] [3] : \mem[2] [3];
  assign _010_ = rp[0] ? \mem[1] [3] : \mem[0] [3];
  assign dout[3] = rp[1] ? _009_ : _010_;
  assign _011_ = rp[0] ? \mem[3] [4] : \mem[2] [4];
  assign _012_ = rp[0] ? \mem[1] [4] : \mem[0] [4];
  assign dout[4] = rp[1] ? _011_ : _012_;
  assign _013_ = rp[0] ? \mem[3] [5] : \mem[2] [5];
  assign _014_ = rp[0] ? \mem[1] [5] : \mem[0] [5];
  assign dout[5] = rp[1] ? _013_ : _014_;
  assign _015_ = rp[0] ? \mem[3] [6] : \mem[2] [6];
  assign _016_ = rp[0] ? \mem[1] [6] : \mem[0] [6];
  assign dout[6] = rp[1] ? _015_ : _016_;
  assign _017_ = rp[0] ? \mem[3] [7] : \mem[2] [7];
  assign _018_ = rp[0] ? \mem[1] [7] : \mem[0] [7];
  assign dout[7] = rp[1] ? _017_ : _018_;
  assign _019_ = rp[0] ? \mem[3] [8] : \mem[2] [8];
  assign _020_ = rp[0] ? \mem[1] [8] : \mem[0] [8];
  assign dout[8] = rp[1] ? _019_ : _020_;
  assign _021_ = we & wp[0];
  assign _022_ = ~we;
  assign _023_ = _022_ | wp[1];
  assign _024_ = _023_ | _021_;
  assign _025_ = din[1] & we;
  assign _064_[0] = _024_ ? \mem[0] [1] : _025_;
  assign _026_ = din[2] & we;
  assign _064_[1] = _024_ ? \mem[0] [2] : _026_;
  assign _027_ = din[3] & we;
  assign _064_[2] = _024_ ? \mem[0] [3] : _027_;
  assign _028_ = din[4] & we;
  assign _064_[3] = _024_ ? \mem[0] [4] : _028_;
  assign _029_ = din[5] & we;
  assign _064_[4] = _024_ ? \mem[0] [5] : _029_;
  assign _030_ = din[6] & we;
  assign _064_[5] = _024_ ? \mem[0] [6] : _030_;
  assign _031_ = din[7] & we;
  assign _064_[6] = _024_ ? \mem[0] [7] : _031_;
  assign _032_ = din[8] & we;
  assign _064_[7] = _024_ ? \mem[0] [8] : _032_;
  assign _033_ = ~_021_;
  assign _034_ = _023_ | _033_;
  assign _065_[0] = _034_ ? \mem[1] [1] : _025_;
  assign _065_[1] = _034_ ? \mem[1] [2] : _026_;
  assign _065_[2] = _034_ ? \mem[1] [3] : _027_;
  assign _065_[3] = _034_ ? \mem[1] [4] : _028_;
  assign _065_[4] = _034_ ? \mem[1] [5] : _029_;
  assign _065_[5] = _034_ ? \mem[1] [6] : _030_;
  assign _065_[6] = _034_ ? \mem[1] [7] : _031_;
  assign _065_[7] = _034_ ? \mem[1] [8] : _032_;
  assign _035_ = we & wp[1];
  assign _036_ = ~_035_;
  assign _037_ = _036_ | _021_;
  assign _066_[0] = _037_ ? \mem[2] [1] : _025_;
  assign _066_[1] = _037_ ? \mem[2] [2] : _026_;
  assign _066_[2] = _037_ ? \mem[2] [3] : _027_;
  assign _066_[3] = _037_ ? \mem[2] [4] : _028_;
  assign _066_[4] = _037_ ? \mem[2] [5] : _029_;
  assign _066_[5] = _037_ ? \mem[2] [6] : _030_;
  assign _066_[6] = _037_ ? \mem[2] [7] : _031_;
  assign _066_[7] = _037_ ? \mem[2] [8] : _032_;
  assign _038_ = _035_ & _021_;
  assign _067_[0] = _038_ ? _025_ : \mem[3] [1];
  assign _067_[1] = _038_ ? _026_ : \mem[3] [2];
  assign _067_[2] = _038_ ? _027_ : \mem[3] [3];
  assign _067_[3] = _038_ ? _028_ : \mem[3] [4];
  assign _067_[4] = _038_ ? _029_ : \mem[3] [5];
  assign _067_[5] = _038_ ? _030_ : \mem[3] [6];
  assign _067_[6] = _038_ ? _031_ : \mem[3] [7];
  assign _067_[7] = _038_ ? _032_ : \mem[3] [8];
  assign _039_ = ~clr;
  assign _040_ = re ^ rp[0];
  assign _001_[0] = _040_ & _039_;
  assign _041_ = ~re;
  assign _042_ = rp[1] ^ rp[0];
  assign _043_ = _041_ ? rp[1] : _042_;
  assign _001_[1] = _043_ & _039_;
  assign _044_ = wp[1] ^ wp[0];
  assign _045_ = ~_044_;
  assign _046_ = _045_ | rp[1];
  assign _047_ = _044_ | _061_;
  assign _048_ = rp[0] | wp[0];
  assign _049_ = ~rp[0];
  assign _050_ = _049_ | _063_;
  assign _051_ = _050_ & we;
  assign _052_ = _051_ & _048_;
  assign _053_ = _052_ & _047_;
  assign _054_ = _053_ & _046_;
  assign _055_ = _041_ & gb;
  assign _056_ = _055_ | _054_;
  assign _057_ = _039_ & rst;
  assign _000_ = _057_ & _056_;
  assign _058_ = we ^ wp[0];
  assign _002_[0] = _058_ & _039_;
  assign _059_ = _022_ ? wp[1] : _044_;
  assign _002_[1] = _059_ & _039_;
  always @(posedge clk)
      \mem[0] [1] <= _064_[0];
  always @(posedge clk)
      \mem[0] [2] <= _064_[1];
  always @(posedge clk)
      \mem[0] [3] <= _064_[2];
  always @(posedge clk)
      \mem[0] [4] <= _064_[3];
  always @(posedge clk)
      \mem[0] [5] <= _064_[4];
  always @(posedge clk)
      \mem[0] [6] <= _064_[5];
  always @(posedge clk)
      \mem[0] [7] <= _064_[6];
  always @(posedge clk)
      \mem[0] [8] <= _064_[7];
  always @(posedge clk)
      \mem[1] [1] <= _065_[0];
  always @(posedge clk)
      \mem[1] [2] <= _065_[1];
  always @(posedge clk)
      \mem[1] [3] <= _065_[2];
  always @(posedge clk)
      \mem[1] [4] <= _065_[3];
  always @(posedge clk)
      \mem[1] [5] <= _065_[4];
  always @(posedge clk)
      \mem[1] [6] <= _065_[5];
  always @(posedge clk)
      \mem[1] [7] <= _065_[6];
  always @(posedge clk)
      \mem[1] [8] <= _065_[7];
  always @(posedge clk)
      \mem[2] [1] <= _066_[0];
  always @(posedge clk)
      \mem[2] [2] <= _066_[1];
  always @(posedge clk)
      \mem[2] [3] <= _066_[2];
  always @(posedge clk)
      \mem[2] [4] <= _066_[3];
  always @(posedge clk)
      \mem[2] [5] <= _066_[4];
  always @(posedge clk)
      \mem[2] [6] <= _066_[5];
  always @(posedge clk)
      \mem[2] [7] <= _066_[6];
  always @(posedge clk)
      \mem[2] [8] <= _066_[7];
  always @(posedge clk)
      \mem[3] [1] <= _067_[0];
  always @(posedge clk)
      \mem[3] [2] <= _067_[1];
  always @(posedge clk)
      \mem[3] [3] <= _067_[2];
  always @(posedge clk)
      \mem[3] [4] <= _067_[3];
  always @(posedge clk)
      \mem[3] [5] <= _067_[4];
  always @(posedge clk)
      \mem[3] [6] <= _067_[5];
  always @(posedge clk)
      \mem[3] [7] <= _067_[6];
  always @(posedge clk)
      \mem[3] [8] <= _067_[7];
  always @(posedge clk or negedge rst)
    if (!rst)
      rp[0] <= 0;
    else
      rp[0] <= _001_[0];
  always @(posedge clk or negedge rst)
    if (!rst)
      rp[1] <= 0;
    else
      rp[1] <= _001_[1];
  always @(posedge clk)
      gb <= _000_;
  always @(posedge clk or negedge rst)
    if (!rst)
      wp[0] <= 0;
    else
      wp[0] <= _002_[0];
  always @(posedge clk or negedge rst)
    if (!rst)
      wp[1] <= 0;
    else
      wp[1] <= _002_[1];
endmodule

module simple_spi_top(clk_i, rst_i, cyc_i, stb_i, adr_i, we_i, dat_i, dat_o, ack_o, inta_o, sck_o, mosi_o, miso_i);
  wire _000_;
  wire [2:0] _001_;
  wire [11:0] _002_;
  wire [7:0] _003_;
  wire _004_;
  wire _005_;
  wire _006_;
  wire [7:0] _007_;
  wire [7:0] _008_;
  wire _009_;
  wire [1:0] _010_;
  wire [1:0] _011_;
  wire [7:0] _012_;
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
  wire _182_;
  wire _183_;
  wire _184_;
  wire _185_;
  wire _186_;
  wire _187_;
  wire _188_;
  wire _189_;
  wire _190_;
  wire _191_;
  wire _192_;
  wire _193_;
  wire _194_;
  wire _195_;
  wire _196_;
  wire _197_;
  wire _198_;
  wire _199_;
  wire _200_;
  wire _201_;
  wire _202_;
  wire _203_;
  wire _204_;
  wire _205_;
  wire _206_;
  wire _207_;
  wire _208_;
  wire _209_;
  wire _210_;
  wire _211_;
  wire _212_;
  wire _213_;
  wire _214_;
  wire _215_;
  wire _216_;
  wire _217_;
  wire _218_;
  wire _219_;
  wire _220_;
  wire _221_;
  wire _222_;
  wire _223_;
  wire _224_;
  wire _225_;
  wire _226_;
  wire _227_;
  wire _228_;
  wire _229_;
  wire _230_;
  wire _231_;
  wire _232_;
  wire _233_;
  wire _234_;
  wire _235_;
  wire _236_;
  wire _237_;
  wire _238_;
  wire _239_;
  wire _240_;
  wire _241_;
  wire _242_;
  wire _243_;
  wire _244_;
  wire _245_;
  wire _246_;
  wire _247_;
  wire _248_;
  wire _249_;
  wire _250_;
  wire _251_;
  wire _252_;
  wire _253_;
  wire _254_;
  wire _255_;
  wire _256_;
  wire _257_;
  wire _258_;
  wire _259_;
  wire _260_;
  wire _261_;
  wire _262_;
  wire _263_;
  wire _264_;
  wire _265_;
  wire _266_;
  wire _267_;
  wire _268_;
  wire _269_;
  wire _270_;
  wire _271_;
  wire _272_;
  wire _273_;
  wire _274_;
  wire _275_;
  wire _276_;
  wire _277_;
  wire _278_;
  wire _279_;
  wire _280_;
  wire _281_;
  wire _282_;
  wire _283_;
  wire _284_;
  wire _285_;
  wire _286_;
  wire _287_;
  wire _288_;
  wire _289_;
  wire _290_;
  wire _291_;
  wire _292_;
  wire _293_;
  wire _294_;
  wire _295_;
  wire _296_;
  wire _297_;
  wire _298_;
  wire _299_;
  wire _300_;
  wire _301_;
  wire _302_;
  wire _303_;
  wire _304_;
  wire _305_;
  wire _306_;
  wire _307_;
  wire _308_;
  wire _309_;
  output ack_o;
  reg ack_o;
  input [1:0] adr_i;
  reg [2:0] bcnt;
  input clk_i;
  reg [11:0] clkcnt;
  reg cpha;
  reg cpol;
  input cyc_i;
  input [7:0] dat_i;
  output [7:0] dat_o;
  reg [7:0] dat_o;
  reg dwom;
  reg [3:0] espr;
  reg [1:0] icnt;
  output inta_o;
  reg inta_o;
  input miso_i;
  output mosi_o;
  reg mosi_o;
  reg mstr;
  wire [7:0] rfdout;
  wire rfempty;
  wire rffull;
  wire rfre;
  reg rfwe;
  input rst_i;
  output sck_o;
  reg sck_o;
  wire [7:0] spcr;
  wire spe;
  wire [7:0] sper;
  wire spie;
  reg spif;
  wire [1:0] spr;
  wire [1:0] spre;
  wire [7:0] spsr;
  reg [1:0] state;
  input stb_i;
  reg [1:0] tcnt;
  wire [7:0] treg;
  wire wcol;
  input we_i;
  wire [7:0] wfdout;
  wire wfempty;
  wire wffull;
  reg wfre;
  wire wfwe;
  assign _015_ = ~adr_i[0];
  assign _016_ = adr_i[1] & _015_;
  assign _017_ = cyc_i & stb_i;
  assign _018_ = _017_ & ack_o;
  assign _019_ = _018_ & _016_;
  assign wfwe = _019_ & we_i;
  assign _020_ = ~we_i;
  assign rfre = _019_ & _020_;
  assign _021_ = ~ack_o;
  assign _000_ = _017_ & _021_;
  assign _004_ = spif & spcr[7];
  assign _309_ = ~spcr[6];
  assign _022_ = _017_ & we_i;
  assign _023_ = ~adr_i[1];
  assign _024_ = _023_ & _015_;
  assign _025_ = _024_ ? dat_i[0] : espr[0];
  assign _007_[0] = _022_ ? _025_ : espr[0];
  assign _026_ = _024_ ? dat_i[1] : espr[1];
  assign _007_[1] = _022_ ? _026_ : espr[1];
  assign _027_ = _024_ ? dat_i[2] : cpha;
  assign _007_[2] = _022_ ? _027_ : cpha;
  assign _028_ = _024_ ? dat_i[3] : cpol;
  assign _007_[3] = _022_ ? _028_ : cpol;
  assign _029_ = ~_022_;
  assign _030_ = _024_ | mstr;
  assign _007_[4] = _029_ ? mstr : _030_;
  assign _031_ = _024_ ? dat_i[5] : dwom;
  assign _007_[5] = _022_ ? _031_ : dwom;
  assign _032_ = _024_ ? dat_i[6] : spcr[6];
  assign _007_[6] = _022_ ? _032_ : spcr[6];
  assign _033_ = _024_ ? dat_i[7] : spcr[7];
  assign _007_[7] = _022_ ? _033_ : spcr[7];
  assign _034_ = adr_i[1] & adr_i[0];
  assign _035_ = _034_ ? dat_i[0] : espr[2];
  assign _008_[0] = _022_ ? _035_ : espr[2];
  assign _036_ = _034_ ? dat_i[1] : espr[3];
  assign _008_[1] = _022_ ? _036_ : espr[3];
  assign _037_ = _034_ ? dat_i[2] : sper[2];
  assign _008_[2] = _022_ ? _037_ : sper[2];
  assign _038_ = _034_ ? dat_i[3] : sper[3];
  assign _008_[3] = _022_ ? _038_ : sper[3];
  assign _039_ = _034_ ? dat_i[4] : sper[4];
  assign _008_[4] = _022_ ? _039_ : sper[4];
  assign _040_ = _034_ ? dat_i[5] : sper[5];
  assign _008_[5] = _022_ ? _040_ : sper[5];
  assign _041_ = _034_ ? dat_i[6] : icnt[0];
  assign _008_[6] = _022_ ? _041_ : icnt[0];
  assign _042_ = _034_ ? dat_i[7] : icnt[1];
  assign _008_[7] = _022_ ? _042_ : icnt[1];
  assign _043_ = ~dat_i[7];
  assign _044_ = _023_ & adr_i[0];
  assign _045_ = ~_044_;
  assign _046_ = _045_ | _029_;
  assign _047_ = _046_ | _043_;
  assign _048_ = tcnt[1] | tcnt[0];
  assign _049_ = ~_048_;
  assign _050_ = _049_ & rfwe;
  assign _051_ = _050_ | spif;
  assign _052_ = _051_ & spcr[6];
  assign _009_ = _052_ & _047_;
  assign _053_ = wfwe & spsr[3];
  assign _054_ = _053_ | spsr[6];
  assign _055_ = ~dat_i[6];
  assign _056_ = _046_ | _055_;
  assign _057_ = _056_ & spcr[6];
  assign _013_ = _057_ & _054_;
  assign _058_ = ~clkcnt[0];
  assign _059_ = clkcnt[7] | clkcnt[6];
  assign _060_ = clkcnt[9] | clkcnt[8];
  assign _061_ = _060_ | _059_;
  assign _062_ = clkcnt[3] | clkcnt[2];
  assign _063_ = clkcnt[5] | clkcnt[4];
  assign _064_ = _063_ | _062_;
  assign _065_ = clkcnt[1] | clkcnt[0];
  assign _066_ = clkcnt[11] | clkcnt[10];
  assign _067_ = _066_ | _065_;
  assign _068_ = _067_ | _064_;
  assign _069_ = _068_ | _061_;
  assign _070_ = ~_069_;
  assign _071_ = ~state[0];
  assign _072_ = ~state[1];
  assign _073_ = _072_ & _071_;
  assign _074_ = _073_ | _309_;
  assign _075_ = _074_ | _070_;
  assign _076_ = ~_075_;
  assign _077_ = espr[1] | espr[0];
  assign _078_ = _077_ | espr[2];
  assign _079_ = _078_ | espr[3];
  assign _080_ = ~espr[3];
  assign _081_ = ~espr[2];
  assign _082_ = ~espr[1];
  assign _083_ = _082_ & espr[0];
  assign _084_ = _083_ & _081_;
  assign _085_ = _084_ & _080_;
  assign _086_ = ~espr[0];
  assign _087_ = espr[1] & _086_;
  assign _088_ = _087_ & _081_;
  assign _089_ = _088_ & _080_;
  assign _090_ = _082_ | espr[0];
  assign _091_ = _080_ & espr[2];
  assign _092_ = ~_091_;
  assign _093_ = _092_ | _090_;
  assign _094_ = ~_093_;
  assign _095_ = espr[1] & espr[0];
  assign _096_ = _095_ & _091_;
  assign _097_ = _078_ | _080_;
  assign _098_ = ~_097_;
  assign _099_ = _084_ & espr[3];
  assign _100_ = _088_ & espr[3];
  assign _101_ = _100_ | _099_;
  assign _102_ = _101_ | _098_;
  assign _103_ = _102_ | _096_;
  assign _104_ = _103_ | _094_;
  assign _105_ = espr[1] | _086_;
  assign _106_ = _092_ | _105_;
  assign _107_ = espr[3] | espr[2];
  assign _108_ = ~_107_;
  assign _109_ = _108_ & _095_;
  assign _110_ = ~_109_;
  assign _111_ = _092_ | _077_;
  assign _112_ = _111_ & _110_;
  assign _113_ = _112_ & _106_;
  assign _114_ = ~_113_;
  assign _115_ = _114_ | _104_;
  assign _116_ = _115_ | _089_;
  assign _002_[0] = _076_ ? _058_ : _079_;
  assign _117_ = ~_085_;
  assign _118_ = ~_089_;
  assign _119_ = ~_096_;
  assign _120_ = _105_ | espr[2];
  assign _121_ = _120_ | _080_;
  assign _122_ = _090_ | espr[2];
  assign _123_ = _122_ | _080_;
  assign _124_ = _123_ & _121_;
  assign _125_ = _124_ & _097_;
  assign _126_ = _125_ & _119_;
  assign _127_ = _126_ & _093_;
  assign _128_ = _113_ & _127_;
  assign _129_ = _128_ & _118_;
  assign _130_ = _129_ & _117_;
  assign _131_ = _130_ & _079_;
  assign _132_ = ~clkcnt[10];
  assign _133_ = _065_ | clkcnt[2];
  assign _134_ = _133_ | clkcnt[3];
  assign _135_ = _134_ | clkcnt[4];
  assign _136_ = _135_ | clkcnt[5];
  assign _137_ = _136_ | clkcnt[6];
  assign _138_ = _137_ | clkcnt[7];
  assign _139_ = _138_ | clkcnt[8];
  assign _140_ = _139_ | clkcnt[9];
  assign _141_ = _140_ ^ _132_;
  assign _002_[10] = _075_ ? _131_ : _141_;
  assign _142_ = ~clkcnt[11];
  assign _143_ = _140_ | clkcnt[10];
  assign _144_ = _143_ ^ _142_;
  assign _002_[11] = _144_ & _076_;
  assign _145_ = clkcnt[1] ^ _058_;
  assign _146_ = _131_ | _116_;
  assign _002_[1] = _076_ ? _145_ : _146_;
  assign _147_ = ~clkcnt[2];
  assign _148_ = _065_ ^ _147_;
  assign _149_ = _131_ | _115_;
  assign _002_[2] = _076_ ? _148_ : _149_;
  assign _150_ = ~clkcnt[3];
  assign _151_ = _133_ ^ _150_;
  assign _152_ = ~_111_;
  assign _153_ = _152_ | _104_;
  assign _154_ = _153_ | _109_;
  assign _155_ = _154_ | _131_;
  assign _002_[3] = _076_ ? _151_ : _155_;
  assign _156_ = ~clkcnt[4];
  assign _157_ = _134_ ^ _156_;
  assign _158_ = _153_ | _131_;
  assign _002_[4] = _076_ ? _157_ : _158_;
  assign _159_ = ~clkcnt[5];
  assign _160_ = _135_ ^ _159_;
  assign _161_ = _131_ | _104_;
  assign _002_[5] = _076_ ? _160_ : _161_;
  assign _162_ = ~clkcnt[6];
  assign _163_ = _136_ ^ _162_;
  assign _164_ = _131_ | _103_;
  assign _002_[6] = _076_ ? _163_ : _164_;
  assign _165_ = ~clkcnt[7];
  assign _166_ = _137_ ^ _165_;
  assign _167_ = _131_ | _102_;
  assign _002_[7] = _076_ ? _166_ : _167_;
  assign _168_ = ~clkcnt[8];
  assign _169_ = _138_ ^ _168_;
  assign _170_ = _131_ | _101_;
  assign _002_[8] = _076_ ? _169_ : _170_;
  assign _171_ = ~clkcnt[9];
  assign _172_ = _139_ ^ _171_;
  assign _173_ = _131_ | _100_;
  assign _002_[9] = _076_ ? _172_ : _173_;
  assign _174_ = state[1] ^ state[0];
  assign _175_ = state[1] & state[0];
  assign _176_ = ~bcnt[0];
  assign _177_ = _069_ ^ _176_;
  assign _178_ = _177_ & _175_;
  assign _179_ = _178_ | _073_;
  assign _180_ = _174_ ? bcnt[0] : _179_;
  assign _001_[0] = _180_ & spcr[6];
  assign _181_ = bcnt[1] ^ _176_;
  assign _182_ = _069_ ? bcnt[1] : _181_;
  assign _183_ = _182_ & _175_;
  assign _184_ = _183_ | _073_;
  assign _185_ = _174_ ? bcnt[1] : _184_;
  assign _001_[1] = _185_ & spcr[6];
  assign _186_ = ~bcnt[2];
  assign _187_ = bcnt[1] | bcnt[0];
  assign _188_ = _187_ ^ _186_;
  assign _189_ = _069_ ? bcnt[2] : _188_;
  assign _190_ = _189_ & _175_;
  assign _191_ = _190_ | _073_;
  assign _192_ = _174_ ? bcnt[2] : _191_;
  assign _001_[2] = _192_ & spcr[6];
  assign _193_ = _187_ | bcnt[2];
  assign _194_ = ~_193_;
  assign _195_ = _175_ & spcr[6];
  assign _196_ = _195_ & _194_;
  assign _005_ = _196_ & _070_;
  assign _197_ = state[1] & _071_;
  assign _198_ = ~sck_o;
  assign _199_ = _193_ ? _198_ : cpol;
  assign _200_ = _069_ ? sck_o : _199_;
  assign _201_ = _200_ & _175_;
  assign _202_ = cpha ? _198_ : cpol;
  assign _203_ = spsr[2] ? cpol : _202_;
  assign _204_ = _203_ & _073_;
  assign _205_ = _072_ & state[0];
  assign _206_ = _069_ ^ _198_;
  assign _207_ = _206_ & _205_;
  assign _208_ = _207_ | _204_;
  assign _209_ = _208_ | _201_;
  assign _210_ = _197_ ? sck_o : _209_;
  assign _006_ = _210_ & spcr[6];
  assign _211_ = _069_ ? state[0] : _193_;
  assign _212_ = _211_ & _175_;
  assign _213_ = ~spsr[2];
  assign _214_ = state[0] | _213_;
  assign _215_ = _214_ & _073_;
  assign _216_ = _205_ | _215_;
  assign _217_ = _216_ | _212_;
  assign _218_ = ~_197_;
  assign _219_ = _218_ & spcr[6];
  assign _010_[0] = _219_ & _217_;
  assign _220_ = _070_ | state[1];
  assign _221_ = _220_ & _205_;
  assign _222_ = _069_ & state[1];
  assign _223_ = _222_ & _175_;
  assign _224_ = _223_ | _221_;
  assign _010_[1] = _224_ & _219_;
  assign _225_ = _073_ & wfdout[0];
  assign _226_ = _069_ ? treg[0] : miso_i;
  assign _227_ = _226_ & _175_;
  assign _228_ = _227_ | _225_;
  assign _229_ = _174_ ? treg[0] : _228_;
  assign _012_[0] = _229_ & spcr[6];
  assign _230_ = _073_ & wfdout[1];
  assign _231_ = _069_ ? treg[1] : treg[0];
  assign _232_ = _231_ & _175_;
  assign _233_ = _232_ | _230_;
  assign _234_ = _174_ ? treg[1] : _233_;
  assign _012_[1] = _234_ & spcr[6];
  assign _235_ = _073_ & wfdout[2];
  assign _236_ = _069_ ? treg[2] : treg[1];
  assign _237_ = _236_ & _175_;
  assign _238_ = _237_ | _235_;
  assign _239_ = _174_ ? treg[2] : _238_;
  assign _012_[2] = _239_ & spcr[6];
  assign _240_ = _073_ & wfdout[3];
  assign _241_ = _069_ ? treg[3] : treg[2];
  assign _242_ = _241_ & _175_;
  assign _243_ = _242_ | _240_;
  assign _244_ = _174_ ? treg[3] : _243_;
  assign _012_[3] = _244_ & spcr[6];
  assign _245_ = _073_ & wfdout[4];
  assign _246_ = _069_ ? treg[4] : treg[3];
  assign _247_ = _246_ & _175_;
  assign _248_ = _247_ | _245_;
  assign _249_ = _174_ ? treg[4] : _248_;
  assign _012_[4] = _249_ & spcr[6];
  assign _250_ = _073_ & wfdout[5];
  assign _251_ = _069_ ? treg[5] : treg[4];
  assign _252_ = _251_ & _175_;
  assign _253_ = _252_ | _250_;
  assign _254_ = _174_ ? treg[5] : _253_;
  assign _012_[5] = _254_ & spcr[6];
  assign _255_ = _073_ & wfdout[6];
  assign _256_ = _069_ ? treg[6] : treg[5];
  assign _257_ = _256_ & _175_;
  assign _258_ = _257_ | _255_;
  assign _259_ = _174_ ? treg[6] : _258_;
  assign _012_[6] = _259_ & spcr[6];
  assign _260_ = _073_ & wfdout[7];
  assign _261_ = _069_ ? mosi_o : treg[6];
  assign _262_ = _261_ & _175_;
  assign _263_ = _262_ | _260_;
  assign _264_ = _174_ ? mosi_o : _263_;
  assign _012_[7] = _264_ & spcr[6];
  assign _265_ = _213_ & spcr[6];
  assign _014_ = _265_ & _073_;
  assign _266_ = ~rfwe;
  assign _267_ = ~tcnt[0];
  assign _268_ = _048_ ? _267_ : icnt[0];
  assign _269_ = _266_ ? tcnt[0] : _268_;
  assign _011_[0] = _309_ ? icnt[0] : _269_;
  assign _270_ = tcnt[1] & tcnt[0];
  assign _271_ = _048_ ? _270_ : icnt[1];
  assign _272_ = _266_ ? tcnt[1] : _271_;
  assign _011_[1] = _309_ ? icnt[1] : _272_;
  assign _273_ = _016_ & rfdout[0];
  assign _274_ = _024_ & espr[0];
  assign _275_ = _044_ & rfempty;
  assign _276_ = _275_ | _274_;
  assign _277_ = _276_ | _273_;
  assign _003_[0] = _034_ ? espr[2] : _277_;
  assign _278_ = _016_ & rfdout[1];
  assign _279_ = _024_ & espr[1];
  assign _280_ = _044_ & rffull;
  assign _281_ = _280_ | _279_;
  assign _282_ = _281_ | _278_;
  assign _003_[1] = _034_ ? espr[3] : _282_;
  assign _283_ = _016_ & rfdout[2];
  assign _284_ = _024_ & cpha;
  assign _285_ = _044_ & spsr[2];
  assign _286_ = _285_ | _284_;
  assign _287_ = _286_ | _283_;
  assign _003_[2] = _034_ ? sper[2] : _287_;
  assign _288_ = _016_ & rfdout[3];
  assign _289_ = _024_ & cpol;
  assign _290_ = _044_ & spsr[3];
  assign _291_ = _290_ | _289_;
  assign _292_ = _291_ | _288_;
  assign _003_[3] = _034_ ? sper[3] : _292_;
  assign _293_ = _024_ & mstr;
  assign _294_ = _016_ & rfdout[4];
  assign _295_ = _294_ | _293_;
  assign _003_[4] = _034_ ? sper[4] : _295_;
  assign _296_ = _024_ & dwom;
  assign _297_ = _016_ & rfdout[5];
  assign _298_ = _297_ | _296_;
  assign _003_[5] = _034_ ? sper[5] : _298_;
  assign _299_ = _016_ & rfdout[6];
  assign _300_ = _024_ & spcr[6];
  assign _301_ = _044_ & spsr[6];
  assign _302_ = _301_ | _300_;
  assign _303_ = _302_ | _299_;
  assign _003_[6] = _034_ ? icnt[0] : _303_;
  assign _304_ = _016_ & rfdout[7];
  assign _305_ = _024_ & spcr[7];
  assign _306_ = _044_ & spif;
  assign _307_ = _306_ | _305_;
  assign _308_ = _307_ | _304_;
  assign _003_[7] = _034_ ? icnt[1] : _308_;
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      espr[0] <= 0;
    else
      espr[0] <= _007_[0];
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      espr[1] <= 0;
    else
      espr[1] <= _007_[1];
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      cpha <= 0;
    else
      cpha <= _007_[2];
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      cpol <= 0;
    else
      cpol <= _007_[3];
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      mstr <= 1;
    else
      mstr <= _007_[4];
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      dwom <= 0;
    else
      dwom <= _007_[5];
  reg \spcr_reg[6] ;
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      \spcr_reg[6]  <= 0;
    else
      \spcr_reg[6]  <= _007_[6];
  assign spcr[6] = \spcr_reg[6] ;
  reg \spcr_reg[7] ;
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      \spcr_reg[7]  <= 0;
    else
      \spcr_reg[7]  <= _007_[7];
  assign spcr[7] = \spcr_reg[7] ;
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      espr[2] <= 0;
    else
      espr[2] <= _008_[0];
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      espr[3] <= 0;
    else
      espr[3] <= _008_[1];
  reg \sper_reg[2] ;
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      \sper_reg[2]  <= 0;
    else
      \sper_reg[2]  <= _008_[2];
  assign sper[2] = \sper_reg[2] ;
  reg \sper_reg[3] ;
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      \sper_reg[3]  <= 0;
    else
      \sper_reg[3]  <= _008_[3];
  assign sper[3] = \sper_reg[3] ;
  reg \sper_reg[4] ;
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      \sper_reg[4]  <= 0;
    else
      \sper_reg[4]  <= _008_[4];
  assign sper[4] = \sper_reg[4] ;
  reg \sper_reg[5] ;
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      \sper_reg[5]  <= 0;
    else
      \sper_reg[5]  <= _008_[5];
  assign sper[5] = \sper_reg[5] ;
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      icnt[0] <= 0;
    else
      icnt[0] <= _008_[6];
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      icnt[1] <= 0;
    else
      icnt[1] <= _008_[7];
  always @(posedge clk_i)
      dat_o[0] <= _003_[0];
  always @(posedge clk_i)
      dat_o[1] <= _003_[1];
  always @(posedge clk_i)
      dat_o[2] <= _003_[2];
  always @(posedge clk_i)
      dat_o[3] <= _003_[3];
  always @(posedge clk_i)
      dat_o[4] <= _003_[4];
  always @(posedge clk_i)
      dat_o[5] <= _003_[5];
  always @(posedge clk_i)
      dat_o[6] <= _003_[6];
  always @(posedge clk_i)
      dat_o[7] <= _003_[7];
  always @(posedge clk_i or negedge rst_i)
    if (!rst_i)
      ack_o <= 0;
    else
      ack_o <= _000_;
  always @(posedge clk_i)
      spif <= _009_;
  reg \spsr_reg[6] ;
  always @(posedge clk_i)
      \spsr_reg[6]  <= _013_;
  assign spsr[6] = \spsr_reg[6] ;
  always @(posedge clk_i)
      inta_o <= _004_;
  always @(posedge clk_i)
      clkcnt[0] <= _002_[0];
  always @(posedge clk_i)
      clkcnt[10] <= _002_[10];
  always @(posedge clk_i)
      clkcnt[11] <= _002_[11];
  always @(posedge clk_i)
      clkcnt[1] <= _002_[1];
  always @(posedge clk_i)
      clkcnt[2] <= _002_[2];
  always @(posedge clk_i)
      clkcnt[3] <= _002_[3];
  always @(posedge clk_i)
      clkcnt[4] <= _002_[4];
  always @(posedge clk_i)
      clkcnt[5] <= _002_[5];
  always @(posedge clk_i)
      clkcnt[6] <= _002_[6];
  always @(posedge clk_i)
      clkcnt[7] <= _002_[7];
  always @(posedge clk_i)
      clkcnt[8] <= _002_[8];
  always @(posedge clk_i)
      clkcnt[9] <= _002_[9];
  always @(posedge clk_i)
      bcnt[0] <= _001_[0];
  always @(posedge clk_i)
      bcnt[1] <= _001_[1];
  always @(posedge clk_i)
      bcnt[2] <= _001_[2];
  always @(posedge clk_i)
      rfwe <= _005_;
  always @(posedge clk_i)
      sck_o <= _006_;
  always @(posedge clk_i)
      state[0] <= _010_[0];
  always @(posedge clk_i)
      state[1] <= _010_[1];
  reg \treg_reg[0] ;
  always @(posedge clk_i)
      \treg_reg[0]  <= _012_[0];
  assign treg[0] = \treg_reg[0] ;
  reg \treg_reg[1] ;
  always @(posedge clk_i)
      \treg_reg[1]  <= _012_[1];
  assign treg[1] = \treg_reg[1] ;
  reg \treg_reg[2] ;
  always @(posedge clk_i)
      \treg_reg[2]  <= _012_[2];
  assign treg[2] = \treg_reg[2] ;
  reg \treg_reg[3] ;
  always @(posedge clk_i)
      \treg_reg[3]  <= _012_[3];
  assign treg[3] = \treg_reg[3] ;
  reg \treg_reg[4] ;
  always @(posedge clk_i)
      \treg_reg[4]  <= _012_[4];
  assign treg[4] = \treg_reg[4] ;
  reg \treg_reg[5] ;
  always @(posedge clk_i)
      \treg_reg[5]  <= _012_[5];
  assign treg[5] = \treg_reg[5] ;
  reg \treg_reg[6] ;
  always @(posedge clk_i)
      \treg_reg[6]  <= _012_[6];
  assign treg[6] = \treg_reg[6] ;
  always @(posedge clk_i)
      mosi_o <= _012_[7];
  always @(posedge clk_i)
      wfre <= _014_;
  always @(posedge clk_i)
      tcnt[0] <= _011_[0];
  always @(posedge clk_i)
      tcnt[1] <= _011_[1];
  \$paramod\fifo4\dw=8  rfifo (
    .clk(clk_i),
    .clr(_309_),
    .din({ mosi_o, treg[6:0] }),
    .dout(rfdout),
    .empty(rfempty),
    .full(rffull),
    .re(rfre),
    .rst(rst_i),
    .we(rfwe)
  );
  \$paramod\fifo4\dw=8  wfifo (
    .clk(clk_i),
    .clr(_309_),
    .din(dat_i),
    .dout(wfdout),
    .empty(spsr[2]),
    .full(spsr[3]),
    .re(wfre),
    .rst(rst_i),
    .we(wfwe)
  );
  assign spcr[5:0] = { dwom, mstr, cpol, cpha, espr[1:0] };
  assign spe = spcr[6];
  assign { sper[7:6], sper[1:0] } = { icnt, espr[3:2] };
  assign spie = spcr[7];
  assign spr = espr[1:0];
  assign spre = espr[3:2];
  assign { spsr[7], spsr[5:4], spsr[1:0] } = { spif, 2'b00, rffull, rfempty };
  assign treg[7] = mosi_o;
  assign wcol = spsr[6];
  assign wfempty = spsr[2];
  assign wffull = spsr[3];
endmodule
