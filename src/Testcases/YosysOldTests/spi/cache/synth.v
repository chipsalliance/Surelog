module spi_clgen(clk_in, rst, go, enable, last_clk, divider, clk_out, pos_edge, neg_edge);
  wire _000_;
  wire [15:0] _001_;
  wire _002_;
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
  input clk_in;
  output clk_out;
  reg clk_out;
  reg [15:0] cnt;
  input [15:0] divider;
  input enable;
  input go;
  input last_clk;
  output neg_edge;
  reg neg_edge;
  output pos_edge;
  reg pos_edge;
  input rst;
  assign _071_ = ~divider[13];
  assign _072_ = ~divider[14];
  assign _073_ = _072_ & _071_;
  assign _074_ = ~divider[15];
  assign _075_ = ~divider[1];
  assign _076_ = _075_ & _074_;
  assign _077_ = _076_ & _073_;
  assign _078_ = ~divider[0];
  assign _079_ = ~divider[10];
  assign _080_ = _079_ & _078_;
  assign _081_ = ~divider[11];
  assign _082_ = ~divider[12];
  assign _083_ = _082_ & _081_;
  assign _084_ = _083_ & _080_;
  assign _085_ = _084_ & _077_;
  assign _086_ = ~divider[6];
  assign _087_ = ~divider[7];
  assign _088_ = _087_ & _086_;
  assign _089_ = ~divider[8];
  assign _090_ = ~divider[9];
  assign _091_ = _090_ & _089_;
  assign _092_ = _091_ & _088_;
  assign _093_ = ~divider[2];
  assign _094_ = ~divider[3];
  assign _095_ = _094_ & _093_;
  assign _096_ = ~divider[4];
  assign _097_ = ~divider[5];
  assign _098_ = _097_ & _096_;
  assign _099_ = _098_ & _095_;
  assign _100_ = _099_ & _092_;
  assign _101_ = _100_ & _085_;
  assign _102_ = ~enable;
  assign _103_ = go & _102_;
  assign _104_ = _103_ & _101_;
  assign _105_ = ~cnt[12];
  assign _106_ = ~cnt[13];
  assign _107_ = _106_ & _105_;
  assign _108_ = ~cnt[14];
  assign _109_ = ~cnt[15];
  assign _110_ = _109_ & _108_;
  assign _111_ = _110_ & _107_;
  assign _112_ = ~cnt[1];
  assign _113_ = _112_ & cnt[0];
  assign _114_ = ~cnt[10];
  assign _115_ = ~cnt[11];
  assign _004_ = _115_ & _114_;
  assign _005_ = _004_ & _113_;
  assign _006_ = _005_ & _111_;
  assign _007_ = ~cnt[6];
  assign _008_ = ~cnt[7];
  assign _009_ = _008_ & _007_;
  assign _010_ = ~cnt[8];
  assign _011_ = ~cnt[9];
  assign _012_ = _011_ & _010_;
  assign _013_ = _012_ & _009_;
  assign _014_ = ~cnt[2];
  assign _015_ = ~cnt[3];
  assign _016_ = _015_ & _014_;
  assign _017_ = ~cnt[4];
  assign _018_ = ~cnt[5];
  assign _019_ = _018_ & _017_;
  assign _020_ = _019_ & _016_;
  assign _021_ = _020_ & _013_;
  assign _022_ = _021_ & _006_;
  assign _023_ = ~clk_out;
  assign _024_ = _023_ & enable;
  assign _025_ = _024_ & _022_;
  assign _026_ = _101_ & clk_out;
  assign _027_ = _026_ | _025_;
  assign _003_ = _027_ | _104_;
  assign _028_ = clk_out & enable;
  assign _029_ = _028_ & _022_;
  assign _030_ = _024_ & _101_;
  assign _002_ = _030_ | _029_;
  assign _031_ = ~cnt[0];
  assign _032_ = _112_ & _031_;
  assign _033_ = _032_ & _004_;
  assign _034_ = _033_ & _111_;
  assign _035_ = _034_ & _021_;
  assign _036_ = ~_035_;
  assign _037_ = _036_ & enable;
  assign _001_[0] = _037_ ? _031_ : divider[0];
  assign _038_ = ~_037_;
  assign _039_ = cnt[1] | cnt[0];
  assign _040_ = _039_ | cnt[2];
  assign _041_ = _040_ | cnt[3];
  assign _042_ = _041_ | cnt[4];
  assign _043_ = _042_ | cnt[5];
  assign _044_ = _043_ | cnt[6];
  assign _045_ = _044_ | cnt[7];
  assign _046_ = _045_ | cnt[8];
  assign _047_ = _046_ | cnt[9];
  assign _048_ = _047_ ^ _114_;
  assign _001_[10] = _038_ ? divider[10] : _048_;
  assign _049_ = _047_ | cnt[10];
  assign _050_ = _049_ ^ _115_;
  assign _001_[11] = _038_ ? divider[11] : _050_;
  assign _051_ = _049_ | cnt[11];
  assign _052_ = _051_ ^ _105_;
  assign _001_[12] = _038_ ? divider[12] : _052_;
  assign _053_ = _051_ | cnt[12];
  assign _054_ = _053_ ^ _106_;
  assign _001_[13] = _038_ ? divider[13] : _054_;
  assign _055_ = _053_ | cnt[13];
  assign _056_ = _055_ ^ _108_;
  assign _001_[14] = _038_ ? divider[14] : _056_;
  assign _057_ = _055_ | cnt[14];
  assign _058_ = _057_ ^ _109_;
  assign _001_[15] = _038_ ? divider[15] : _058_;
  assign _059_ = cnt[1] ^ _031_;
  assign _001_[1] = _037_ ? _059_ : divider[1];
  assign _060_ = _039_ ^ _014_;
  assign _001_[2] = _037_ ? _060_ : divider[2];
  assign _061_ = _040_ ^ _015_;
  assign _001_[3] = _037_ ? _061_ : divider[3];
  assign _062_ = _041_ ^ _017_;
  assign _001_[4] = _037_ ? _062_ : divider[4];
  assign _063_ = _042_ ^ _018_;
  assign _001_[5] = _037_ ? _063_ : divider[5];
  assign _064_ = _043_ ^ _007_;
  assign _001_[6] = _037_ ? _064_ : divider[6];
  assign _065_ = _044_ ^ _008_;
  assign _001_[7] = _037_ ? _065_ : divider[7];
  assign _066_ = _045_ ^ _010_;
  assign _001_[8] = _038_ ? divider[8] : _066_;
  assign _067_ = _046_ ^ _011_;
  assign _001_[9] = _038_ ? divider[9] : _067_;
  assign _068_ = last_clk & _023_;
  assign _069_ = _068_ | _102_;
  assign _070_ = _069_ | _036_;
  assign _000_ = _070_ ^ _023_;
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[0] <= 1;
    else
      cnt[0] <= _001_[0];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[10] <= 1;
    else
      cnt[10] <= _001_[10];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[11] <= 1;
    else
      cnt[11] <= _001_[11];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[12] <= 1;
    else
      cnt[12] <= _001_[12];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[13] <= 1;
    else
      cnt[13] <= _001_[13];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[14] <= 1;
    else
      cnt[14] <= _001_[14];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[15] <= 1;
    else
      cnt[15] <= _001_[15];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[1] <= 1;
    else
      cnt[1] <= _001_[1];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[2] <= 1;
    else
      cnt[2] <= _001_[2];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[3] <= 1;
    else
      cnt[3] <= _001_[3];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[4] <= 1;
    else
      cnt[4] <= _001_[4];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[5] <= 1;
    else
      cnt[5] <= _001_[5];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[6] <= 1;
    else
      cnt[6] <= _001_[6];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[7] <= 1;
    else
      cnt[7] <= _001_[7];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[8] <= 1;
    else
      cnt[8] <= _001_[8];
  always @(posedge clk_in or posedge rst)
    if (rst)
      cnt[9] <= 1;
    else
      cnt[9] <= _001_[9];
  always @(posedge clk_in or posedge rst)
    if (rst)
      clk_out <= 0;
    else
      clk_out <= _000_;
  always @(posedge clk_in or posedge rst)
    if (rst)
      neg_edge <= 0;
    else
      neg_edge <= _002_;
  always @(posedge clk_in or posedge rst)
    if (rst)
      pos_edge <= 0;
    else
      pos_edge <= _003_;
endmodule

module spi_shift(clk, rst, latch, byte_sel, len, lsb, go, pos_edge, neg_edge, rx_negedge, tx_negedge, tip, last, p_in, p_out, s_clk, s_in, s_out);
  wire [7:0] _0000_;
  wire [127:0] _0001_;
  wire _0002_;
  wire _0003_;
  wire _0004_;
  wire _0005_;
  wire _0006_;
  wire _0007_;
  wire _0008_;
  wire _0009_;
  wire _0010_;
  wire _0011_;
  wire _0012_;
  wire _0013_;
  wire _0014_;
  wire _0015_;
  wire _0016_;
  wire _0017_;
  wire _0018_;
  wire _0019_;
  wire _0020_;
  wire _0021_;
  wire _0022_;
  wire _0023_;
  wire _0024_;
  wire _0025_;
  wire _0026_;
  wire _0027_;
  wire _0028_;
  wire _0029_;
  wire _0030_;
  wire _0031_;
  wire _0032_;
  wire _0033_;
  wire _0034_;
  wire _0035_;
  wire _0036_;
  wire _0037_;
  wire _0038_;
  wire _0039_;
  wire _0040_;
  wire _0041_;
  wire _0042_;
  wire _0043_;
  wire _0044_;
  wire _0045_;
  wire _0046_;
  wire _0047_;
  wire _0048_;
  wire _0049_;
  wire _0050_;
  wire _0051_;
  wire _0052_;
  wire _0053_;
  wire _0054_;
  wire _0055_;
  wire _0056_;
  wire _0057_;
  wire _0058_;
  wire _0059_;
  wire _0060_;
  wire _0061_;
  wire _0062_;
  wire _0063_;
  wire _0064_;
  wire _0065_;
  wire _0066_;
  wire _0067_;
  wire _0068_;
  wire _0069_;
  wire _0070_;
  wire _0071_;
  wire _0072_;
  wire _0073_;
  wire _0074_;
  wire _0075_;
  wire _0076_;
  wire _0077_;
  wire _0078_;
  wire _0079_;
  wire _0080_;
  wire _0081_;
  wire _0082_;
  wire _0083_;
  wire _0084_;
  wire _0085_;
  wire _0086_;
  wire _0087_;
  wire _0088_;
  wire _0089_;
  wire _0090_;
  wire _0091_;
  wire _0092_;
  wire _0093_;
  wire _0094_;
  wire _0095_;
  wire _0096_;
  wire _0097_;
  wire _0098_;
  wire _0099_;
  wire _0100_;
  wire _0101_;
  wire _0102_;
  wire _0103_;
  wire _0104_;
  wire _0105_;
  wire _0106_;
  wire _0107_;
  wire _0108_;
  wire _0109_;
  wire _0110_;
  wire _0111_;
  wire _0112_;
  wire _0113_;
  wire _0114_;
  wire _0115_;
  wire _0116_;
  wire _0117_;
  wire _0118_;
  wire _0119_;
  wire _0120_;
  wire _0121_;
  wire _0122_;
  wire _0123_;
  wire _0124_;
  wire _0125_;
  wire _0126_;
  wire _0127_;
  wire _0128_;
  wire _0129_;
  wire _0130_;
  wire _0131_;
  wire _0132_;
  wire _0133_;
  wire _0134_;
  wire _0135_;
  wire _0136_;
  wire _0137_;
  wire _0138_;
  wire _0139_;
  wire _0140_;
  wire _0141_;
  wire _0142_;
  wire _0143_;
  wire _0144_;
  wire _0145_;
  wire _0146_;
  wire _0147_;
  wire _0148_;
  wire _0149_;
  wire _0150_;
  wire _0151_;
  wire _0152_;
  wire _0153_;
  wire _0154_;
  wire _0155_;
  wire _0156_;
  wire _0157_;
  wire _0158_;
  wire _0159_;
  wire _0160_;
  wire _0161_;
  wire _0162_;
  wire _0163_;
  wire _0164_;
  wire _0165_;
  wire _0166_;
  wire _0167_;
  wire _0168_;
  wire _0169_;
  wire _0170_;
  wire _0171_;
  wire _0172_;
  wire _0173_;
  wire _0174_;
  wire _0175_;
  wire _0176_;
  wire _0177_;
  wire _0178_;
  wire _0179_;
  wire _0180_;
  wire _0181_;
  wire _0182_;
  wire _0183_;
  wire _0184_;
  wire _0185_;
  wire _0186_;
  wire _0187_;
  wire _0188_;
  wire _0189_;
  wire _0190_;
  wire _0191_;
  wire _0192_;
  wire _0193_;
  wire _0194_;
  wire _0195_;
  wire _0196_;
  wire _0197_;
  wire _0198_;
  wire _0199_;
  wire _0200_;
  wire _0201_;
  wire _0202_;
  wire _0203_;
  wire _0204_;
  wire _0205_;
  wire _0206_;
  wire _0207_;
  wire _0208_;
  wire _0209_;
  wire _0210_;
  wire _0211_;
  wire _0212_;
  wire _0213_;
  wire _0214_;
  wire _0215_;
  wire _0216_;
  wire _0217_;
  wire _0218_;
  wire _0219_;
  wire _0220_;
  wire _0221_;
  wire _0222_;
  wire _0223_;
  wire _0224_;
  wire _0225_;
  wire _0226_;
  wire _0227_;
  wire _0228_;
  wire _0229_;
  wire _0230_;
  wire _0231_;
  wire _0232_;
  wire _0233_;
  wire _0234_;
  wire _0235_;
  wire _0236_;
  wire _0237_;
  wire _0238_;
  wire _0239_;
  wire _0240_;
  wire _0241_;
  wire _0242_;
  wire _0243_;
  wire _0244_;
  wire _0245_;
  wire _0246_;
  wire _0247_;
  wire _0248_;
  wire _0249_;
  wire _0250_;
  wire _0251_;
  wire _0252_;
  wire _0253_;
  wire _0254_;
  wire _0255_;
  wire _0256_;
  wire _0257_;
  wire _0258_;
  wire _0259_;
  wire _0260_;
  wire _0261_;
  wire _0262_;
  wire _0263_;
  wire _0264_;
  wire _0265_;
  wire _0266_;
  wire _0267_;
  wire _0268_;
  wire _0269_;
  wire _0270_;
  wire _0271_;
  wire _0272_;
  wire _0273_;
  wire _0274_;
  wire _0275_;
  wire _0276_;
  wire _0277_;
  wire _0278_;
  wire _0279_;
  wire _0280_;
  wire _0281_;
  wire _0282_;
  wire _0283_;
  wire _0284_;
  wire _0285_;
  wire _0286_;
  wire _0287_;
  wire _0288_;
  wire _0289_;
  wire _0290_;
  wire _0291_;
  wire _0292_;
  wire _0293_;
  wire _0294_;
  wire _0295_;
  wire _0296_;
  wire _0297_;
  wire _0298_;
  wire _0299_;
  wire _0300_;
  wire _0301_;
  wire _0302_;
  wire _0303_;
  wire _0304_;
  wire _0305_;
  wire _0306_;
  wire _0307_;
  wire _0308_;
  wire _0309_;
  wire _0310_;
  wire _0311_;
  wire _0312_;
  wire _0313_;
  wire _0314_;
  wire _0315_;
  wire _0316_;
  wire _0317_;
  wire _0318_;
  wire _0319_;
  wire _0320_;
  wire _0321_;
  wire _0322_;
  wire _0323_;
  wire _0324_;
  wire _0325_;
  wire _0326_;
  wire _0327_;
  wire _0328_;
  wire _0329_;
  wire _0330_;
  wire _0331_;
  wire _0332_;
  wire _0333_;
  wire _0334_;
  wire _0335_;
  wire _0336_;
  wire _0337_;
  wire _0338_;
  wire _0339_;
  wire _0340_;
  wire _0341_;
  wire _0342_;
  wire _0343_;
  wire _0344_;
  wire _0345_;
  wire _0346_;
  wire _0347_;
  wire _0348_;
  wire _0349_;
  wire _0350_;
  wire _0351_;
  wire _0352_;
  wire _0353_;
  wire _0354_;
  wire _0355_;
  wire _0356_;
  wire _0357_;
  wire _0358_;
  wire _0359_;
  wire _0360_;
  wire _0361_;
  wire _0362_;
  wire _0363_;
  wire _0364_;
  wire _0365_;
  wire _0366_;
  wire _0367_;
  wire _0368_;
  wire _0369_;
  wire _0370_;
  wire _0371_;
  wire _0372_;
  wire _0373_;
  wire _0374_;
  wire _0375_;
  wire _0376_;
  wire _0377_;
  wire _0378_;
  wire _0379_;
  wire _0380_;
  wire _0381_;
  wire _0382_;
  wire _0383_;
  wire _0384_;
  wire _0385_;
  wire _0386_;
  wire _0387_;
  wire _0388_;
  wire _0389_;
  wire _0390_;
  wire _0391_;
  wire _0392_;
  wire _0393_;
  wire _0394_;
  wire _0395_;
  wire _0396_;
  wire _0397_;
  wire _0398_;
  wire _0399_;
  wire _0400_;
  wire _0401_;
  wire _0402_;
  wire _0403_;
  wire _0404_;
  wire _0405_;
  wire _0406_;
  wire _0407_;
  wire _0408_;
  wire _0409_;
  wire _0410_;
  wire _0411_;
  wire _0412_;
  wire _0413_;
  wire _0414_;
  wire _0415_;
  wire _0416_;
  wire _0417_;
  wire _0418_;
  wire _0419_;
  wire _0420_;
  wire _0421_;
  wire _0422_;
  wire _0423_;
  wire _0424_;
  wire _0425_;
  wire _0426_;
  wire _0427_;
  wire _0428_;
  wire _0429_;
  wire _0430_;
  wire _0431_;
  wire _0432_;
  wire _0433_;
  wire _0434_;
  wire _0435_;
  wire _0436_;
  wire _0437_;
  wire _0438_;
  wire _0439_;
  wire _0440_;
  wire _0441_;
  wire _0442_;
  wire _0443_;
  wire _0444_;
  wire _0445_;
  wire _0446_;
  wire _0447_;
  wire _0448_;
  wire _0449_;
  wire _0450_;
  wire _0451_;
  wire _0452_;
  wire _0453_;
  wire _0454_;
  wire _0455_;
  wire _0456_;
  wire _0457_;
  wire _0458_;
  wire _0459_;
  wire _0460_;
  wire _0461_;
  wire _0462_;
  wire _0463_;
  wire _0464_;
  wire _0465_;
  wire _0466_;
  wire _0467_;
  wire _0468_;
  wire _0469_;
  wire _0470_;
  wire _0471_;
  wire _0472_;
  wire _0473_;
  wire _0474_;
  wire _0475_;
  wire _0476_;
  wire _0477_;
  wire _0478_;
  wire _0479_;
  wire _0480_;
  wire _0481_;
  wire _0482_;
  wire _0483_;
  wire _0484_;
  wire _0485_;
  wire _0486_;
  wire _0487_;
  wire _0488_;
  wire _0489_;
  wire _0490_;
  wire _0491_;
  wire _0492_;
  wire _0493_;
  wire _0494_;
  wire _0495_;
  wire _0496_;
  wire _0497_;
  wire _0498_;
  wire _0499_;
  wire _0500_;
  wire _0501_;
  wire _0502_;
  wire _0503_;
  wire _0504_;
  wire _0505_;
  wire _0506_;
  wire _0507_;
  wire _0508_;
  wire _0509_;
  wire _0510_;
  wire _0511_;
  wire _0512_;
  wire _0513_;
  wire _0514_;
  wire _0515_;
  wire _0516_;
  wire _0517_;
  wire _0518_;
  wire _0519_;
  wire _0520_;
  wire _0521_;
  wire _0522_;
  wire _0523_;
  wire _0524_;
  wire _0525_;
  wire _0526_;
  wire _0527_;
  wire _0528_;
  wire _0529_;
  wire _0530_;
  wire _0531_;
  wire _0532_;
  wire _0533_;
  wire _0534_;
  wire _0535_;
  wire _0536_;
  wire _0537_;
  wire _0538_;
  wire _0539_;
  wire _0540_;
  wire _0541_;
  wire _0542_;
  wire _0543_;
  wire _0544_;
  wire _0545_;
  wire _0546_;
  wire _0547_;
  wire _0548_;
  wire _0549_;
  wire _0550_;
  wire _0551_;
  wire _0552_;
  wire _0553_;
  wire _0554_;
  wire _0555_;
  wire _0556_;
  wire _0557_;
  wire _0558_;
  wire _0559_;
  wire _0560_;
  wire _0561_;
  wire _0562_;
  wire _0563_;
  wire _0564_;
  wire _0565_;
  wire _0566_;
  wire _0567_;
  wire _0568_;
  wire _0569_;
  wire _0570_;
  wire _0571_;
  wire _0572_;
  wire _0573_;
  wire _0574_;
  wire _0575_;
  wire _0576_;
  wire _0577_;
  wire _0578_;
  wire _0579_;
  wire _0580_;
  wire _0581_;
  wire _0582_;
  wire _0583_;
  wire _0584_;
  wire _0585_;
  wire _0586_;
  wire _0587_;
  wire _0588_;
  wire _0589_;
  wire _0590_;
  wire _0591_;
  wire _0592_;
  wire _0593_;
  wire _0594_;
  wire _0595_;
  wire _0596_;
  wire _0597_;
  wire _0598_;
  wire _0599_;
  wire _0600_;
  wire _0601_;
  wire _0602_;
  wire _0603_;
  wire _0604_;
  wire _0605_;
  wire _0606_;
  wire _0607_;
  wire _0608_;
  wire _0609_;
  wire _0610_;
  wire _0611_;
  wire _0612_;
  wire _0613_;
  wire _0614_;
  wire _0615_;
  wire _0616_;
  wire _0617_;
  wire _0618_;
  wire _0619_;
  wire _0620_;
  wire _0621_;
  wire _0622_;
  wire _0623_;
  wire _0624_;
  wire _0625_;
  wire _0626_;
  wire _0627_;
  wire _0628_;
  wire _0629_;
  wire _0630_;
  wire _0631_;
  wire _0632_;
  wire _0633_;
  wire _0634_;
  wire _0635_;
  wire _0636_;
  wire _0637_;
  wire _0638_;
  wire _0639_;
  wire _0640_;
  wire _0641_;
  wire _0642_;
  wire _0643_;
  wire _0644_;
  wire _0645_;
  wire _0646_;
  wire _0647_;
  wire _0648_;
  wire _0649_;
  wire _0650_;
  wire _0651_;
  wire _0652_;
  wire _0653_;
  wire _0654_;
  wire _0655_;
  wire _0656_;
  wire _0657_;
  wire _0658_;
  wire _0659_;
  wire _0660_;
  wire _0661_;
  wire _0662_;
  wire _0663_;
  wire _0664_;
  wire _0665_;
  wire _0666_;
  wire _0667_;
  wire _0668_;
  wire _0669_;
  wire _0670_;
  wire _0671_;
  wire _0672_;
  wire _0673_;
  wire _0674_;
  wire _0675_;
  wire _0676_;
  wire _0677_;
  wire _0678_;
  wire _0679_;
  wire _0680_;
  wire _0681_;
  wire _0682_;
  wire _0683_;
  wire _0684_;
  wire _0685_;
  wire _0686_;
  wire _0687_;
  wire _0688_;
  wire _0689_;
  wire _0690_;
  wire _0691_;
  wire _0692_;
  wire _0693_;
  wire _0694_;
  wire _0695_;
  wire _0696_;
  wire _0697_;
  wire _0698_;
  wire _0699_;
  wire _0700_;
  wire _0701_;
  wire _0702_;
  wire _0703_;
  wire _0704_;
  wire _0705_;
  wire _0706_;
  wire _0707_;
  wire _0708_;
  wire _0709_;
  wire _0710_;
  wire _0711_;
  wire _0712_;
  wire _0713_;
  wire _0714_;
  wire _0715_;
  wire _0716_;
  wire _0717_;
  wire _0718_;
  wire _0719_;
  wire _0720_;
  wire _0721_;
  wire _0722_;
  wire _0723_;
  wire _0724_;
  wire _0725_;
  wire _0726_;
  wire _0727_;
  wire _0728_;
  wire _0729_;
  wire _0730_;
  wire _0731_;
  wire _0732_;
  wire _0733_;
  wire _0734_;
  wire _0735_;
  wire _0736_;
  wire _0737_;
  wire _0738_;
  wire _0739_;
  wire _0740_;
  wire _0741_;
  wire _0742_;
  wire _0743_;
  wire _0744_;
  wire _0745_;
  wire _0746_;
  wire _0747_;
  wire _0748_;
  wire _0749_;
  wire _0750_;
  wire _0751_;
  wire _0752_;
  wire _0753_;
  wire _0754_;
  wire _0755_;
  wire _0756_;
  wire _0757_;
  wire _0758_;
  wire _0759_;
  wire _0760_;
  wire _0761_;
  wire _0762_;
  wire _0763_;
  wire _0764_;
  wire _0765_;
  wire _0766_;
  wire _0767_;
  wire _0768_;
  wire _0769_;
  wire _0770_;
  wire _0771_;
  wire _0772_;
  wire _0773_;
  wire _0774_;
  wire _0775_;
  wire _0776_;
  wire _0777_;
  wire _0778_;
  wire _0779_;
  wire _0780_;
  wire _0781_;
  wire _0782_;
  wire _0783_;
  wire _0784_;
  wire _0785_;
  wire _0786_;
  wire _0787_;
  wire _0788_;
  wire _0789_;
  wire _0790_;
  wire _0791_;
  wire _0792_;
  wire _0793_;
  wire _0794_;
  wire _0795_;
  wire _0796_;
  wire _0797_;
  wire _0798_;
  wire _0799_;
  wire _0800_;
  wire _0801_;
  wire _0802_;
  wire _0803_;
  wire _0804_;
  wire _0805_;
  wire _0806_;
  wire _0807_;
  wire _0808_;
  wire _0809_;
  wire _0810_;
  wire _0811_;
  wire _0812_;
  wire _0813_;
  wire _0814_;
  wire _0815_;
  wire _0816_;
  wire _0817_;
  wire _0818_;
  wire _0819_;
  wire _0820_;
  wire _0821_;
  wire _0822_;
  wire _0823_;
  wire _0824_;
  wire _0825_;
  wire _0826_;
  wire _0827_;
  wire _0828_;
  wire _0829_;
  wire _0830_;
  wire _0831_;
  wire _0832_;
  wire _0833_;
  wire _0834_;
  wire _0835_;
  wire _0836_;
  wire _0837_;
  wire _0838_;
  wire _0839_;
  wire _0840_;
  wire _0841_;
  wire _0842_;
  wire _0843_;
  wire _0844_;
  wire _0845_;
  wire _0846_;
  wire _0847_;
  wire _0848_;
  wire _0849_;
  wire _0850_;
  wire _0851_;
  wire _0852_;
  wire _0853_;
  wire _0854_;
  wire _0855_;
  wire _0856_;
  wire _0857_;
  wire _0858_;
  wire _0859_;
  wire _0860_;
  wire _0861_;
  wire _0862_;
  wire _0863_;
  wire _0864_;
  wire _0865_;
  wire _0866_;
  wire _0867_;
  wire _0868_;
  wire _0869_;
  wire _0870_;
  wire _0871_;
  wire _0872_;
  wire _0873_;
  wire _0874_;
  wire _0875_;
  wire _0876_;
  wire _0877_;
  wire _0878_;
  wire _0879_;
  wire _0880_;
  wire _0881_;
  wire _0882_;
  wire _0883_;
  wire _0884_;
  wire _0885_;
  wire _0886_;
  wire _0887_;
  wire _0888_;
  wire _0889_;
  wire _0890_;
  wire _0891_;
  wire _0892_;
  wire _0893_;
  wire _0894_;
  wire _0895_;
  wire _0896_;
  wire _0897_;
  wire _0898_;
  wire _0899_;
  wire _0900_;
  wire _0901_;
  wire _0902_;
  wire _0903_;
  wire _0904_;
  wire _0905_;
  wire _0906_;
  wire _0907_;
  wire _0908_;
  wire _0909_;
  wire _0910_;
  wire _0911_;
  wire _0912_;
  wire _0913_;
  wire _0914_;
  wire _0915_;
  wire _0916_;
  wire _0917_;
  wire _0918_;
  wire _0919_;
  wire _0920_;
  wire _0921_;
  wire _0922_;
  wire _0923_;
  wire _0924_;
  wire _0925_;
  wire _0926_;
  wire _0927_;
  wire _0928_;
  wire _0929_;
  wire _0930_;
  wire _0931_;
  wire _0932_;
  wire _0933_;
  wire _0934_;
  wire _0935_;
  wire _0936_;
  wire _0937_;
  wire _0938_;
  wire _0939_;
  wire _0940_;
  wire _0941_;
  wire _0942_;
  wire _0943_;
  wire _0944_;
  wire _0945_;
  wire _0946_;
  wire _0947_;
  wire _0948_;
  wire _0949_;
  wire _0950_;
  wire _0951_;
  wire _0952_;
  wire _0953_;
  wire _0954_;
  wire _0955_;
  wire _0956_;
  wire _0957_;
  wire _0958_;
  wire _0959_;
  wire _0960_;
  wire _0961_;
  wire _0962_;
  wire _0963_;
  wire _0964_;
  wire _0965_;
  wire _0966_;
  wire _0967_;
  wire _0968_;
  wire _0969_;
  wire _0970_;
  wire _0971_;
  wire _0972_;
  wire _0973_;
  wire _0974_;
  wire _0975_;
  wire _0976_;
  wire _0977_;
  wire _0978_;
  wire _0979_;
  wire _0980_;
  wire _0981_;
  wire _0982_;
  wire _0983_;
  wire _0984_;
  wire _0985_;
  wire _0986_;
  wire _0987_;
  wire _0988_;
  wire _0989_;
  wire _0990_;
  wire _0991_;
  wire _0992_;
  wire _0993_;
  wire _0994_;
  wire _0995_;
  wire _0996_;
  wire _0997_;
  wire _0998_;
  wire _0999_;
  wire _1000_;
  wire _1001_;
  wire _1002_;
  wire _1003_;
  wire _1004_;
  wire _1005_;
  wire _1006_;
  wire _1007_;
  wire _1008_;
  wire _1009_;
  wire _1010_;
  wire _1011_;
  wire _1012_;
  wire _1013_;
  wire _1014_;
  wire _1015_;
  wire _1016_;
  wire _1017_;
  wire _1018_;
  wire _1019_;
  wire _1020_;
  wire _1021_;
  wire _1022_;
  wire _1023_;
  wire _1024_;
  wire _1025_;
  wire _1026_;
  wire _1027_;
  wire _1028_;
  wire _1029_;
  wire _1030_;
  wire _1031_;
  wire _1032_;
  wire _1033_;
  wire _1034_;
  wire _1035_;
  wire _1036_;
  wire _1037_;
  wire _1038_;
  wire _1039_;
  wire _1040_;
  wire _1041_;
  wire _1042_;
  wire _1043_;
  wire _1044_;
  wire _1045_;
  wire _1046_;
  wire _1047_;
  wire _1048_;
  wire _1049_;
  wire _1050_;
  wire _1051_;
  wire _1052_;
  wire _1053_;
  wire _1054_;
  wire _1055_;
  wire _1056_;
  wire _1057_;
  wire _1058_;
  wire _1059_;
  wire _1060_;
  wire _1061_;
  wire _1062_;
  wire _1063_;
  wire _1064_;
  wire _1065_;
  wire _1066_;
  wire _1067_;
  wire _1068_;
  wire _1069_;
  wire _1070_;
  wire _1071_;
  wire _1072_;
  wire _1073_;
  wire _1074_;
  wire _1075_;
  wire _1076_;
  wire _1077_;
  wire _1078_;
  wire _1079_;
  wire _1080_;
  wire _1081_;
  wire _1082_;
  wire _1083_;
  wire _1084_;
  wire _1085_;
  wire _1086_;
  wire _1087_;
  wire _1088_;
  wire _1089_;
  wire _1090_;
  wire _1091_;
  wire _1092_;
  wire _1093_;
  wire _1094_;
  wire _1095_;
  wire _1096_;
  wire _1097_;
  wire _1098_;
  wire _1099_;
  wire _1100_;
  wire _1101_;
  wire _1102_;
  wire _1103_;
  wire _1104_;
  wire _1105_;
  wire _1106_;
  wire _1107_;
  wire _1108_;
  wire _1109_;
  wire _1110_;
  wire _1111_;
  wire _1112_;
  wire _1113_;
  wire _1114_;
  wire _1115_;
  wire _1116_;
  wire _1117_;
  wire _1118_;
  wire _1119_;
  wire _1120_;
  wire _1121_;
  wire _1122_;
  wire _1123_;
  wire _1124_;
  wire _1125_;
  wire _1126_;
  wire _1127_;
  wire _1128_;
  wire _1129_;
  wire _1130_;
  wire _1131_;
  wire _1132_;
  wire _1133_;
  wire _1134_;
  wire _1135_;
  wire _1136_;
  wire _1137_;
  wire _1138_;
  wire _1139_;
  wire _1140_;
  wire _1141_;
  wire _1142_;
  wire _1143_;
  wire _1144_;
  wire _1145_;
  wire _1146_;
  wire _1147_;
  wire _1148_;
  wire _1149_;
  wire _1150_;
  wire _1151_;
  wire _1152_;
  wire _1153_;
  wire _1154_;
  wire _1155_;
  wire _1156_;
  wire _1157_;
  wire _1158_;
  wire _1159_;
  wire _1160_;
  wire _1161_;
  wire _1162_;
  wire _1163_;
  wire _1164_;
  wire _1165_;
  wire _1166_;
  wire _1167_;
  wire _1168_;
  wire _1169_;
  wire _1170_;
  wire _1171_;
  wire _1172_;
  wire _1173_;
  wire _1174_;
  wire _1175_;
  wire _1176_;
  wire _1177_;
  wire _1178_;
  wire _1179_;
  wire _1180_;
  wire _1181_;
  wire _1182_;
  wire _1183_;
  wire _1184_;
  wire _1185_;
  wire _1186_;
  wire _1187_;
  wire _1188_;
  wire _1189_;
  wire _1190_;
  wire _1191_;
  wire _1192_;
  wire _1193_;
  wire _1194_;
  wire _1195_;
  wire _1196_;
  wire _1197_;
  wire _1198_;
  wire _1199_;
  wire _1200_;
  wire _1201_;
  wire _1202_;
  wire _1203_;
  wire _1204_;
  wire _1205_;
  wire _1206_;
  wire _1207_;
  wire _1208_;
  wire _1209_;
  wire _1210_;
  wire _1211_;
  wire _1212_;
  wire _1213_;
  wire _1214_;
  wire _1215_;
  wire _1216_;
  wire _1217_;
  wire _1218_;
  wire _1219_;
  wire _1220_;
  wire _1221_;
  wire _1222_;
  wire _1223_;
  wire _1224_;
  wire _1225_;
  wire _1226_;
  wire _1227_;
  wire _1228_;
  wire _1229_;
  wire _1230_;
  wire _1231_;
  wire _1232_;
  wire _1233_;
  wire _1234_;
  wire _1235_;
  wire _1236_;
  wire _1237_;
  wire _1238_;
  wire _1239_;
  wire _1240_;
  wire _1241_;
  wire _1242_;
  wire _1243_;
  wire _1244_;
  wire _1245_;
  wire _1246_;
  wire _1247_;
  wire _1248_;
  wire _1249_;
  wire _1250_;
  wire _1251_;
  wire _1252_;
  wire _1253_;
  wire _1254_;
  wire _1255_;
  wire _1256_;
  wire _1257_;
  wire _1258_;
  wire _1259_;
  wire _1260_;
  wire _1261_;
  wire _1262_;
  wire _1263_;
  wire _1264_;
  wire _1265_;
  wire _1266_;
  wire _1267_;
  wire _1268_;
  wire _1269_;
  wire _1270_;
  wire _1271_;
  wire _1272_;
  wire _1273_;
  wire _1274_;
  wire _1275_;
  wire _1276_;
  wire _1277_;
  wire _1278_;
  wire _1279_;
  wire _1280_;
  wire _1281_;
  wire _1282_;
  wire _1283_;
  wire _1284_;
  wire _1285_;
  wire _1286_;
  wire _1287_;
  wire _1288_;
  wire _1289_;
  wire _1290_;
  wire _1291_;
  wire _1292_;
  wire _1293_;
  wire _1294_;
  wire _1295_;
  wire _1296_;
  wire _1297_;
  wire _1298_;
  wire _1299_;
  wire _1300_;
  wire _1301_;
  wire _1302_;
  wire _1303_;
  wire _1304_;
  wire _1305_;
  wire _1306_;
  wire _1307_;
  wire _1308_;
  wire _1309_;
  wire _1310_;
  wire _1311_;
  wire _1312_;
  wire _1313_;
  wire _1314_;
  wire _1315_;
  wire _1316_;
  wire _1317_;
  wire _1318_;
  wire _1319_;
  wire _1320_;
  wire _1321_;
  wire _1322_;
  wire _1323_;
  wire _1324_;
  wire _1325_;
  wire _1326_;
  wire _1327_;
  wire _1328_;
  wire _1329_;
  wire _1330_;
  wire _1331_;
  wire _1332_;
  wire _1333_;
  wire _1334_;
  wire _1335_;
  wire _1336_;
  wire _1337_;
  wire _1338_;
  wire _1339_;
  wire _1340_;
  wire _1341_;
  wire _1342_;
  wire _1343_;
  wire _1344_;
  wire _1345_;
  wire _1346_;
  wire _1347_;
  wire _1348_;
  wire _1349_;
  wire _1350_;
  wire _1351_;
  wire _1352_;
  wire _1353_;
  wire _1354_;
  wire _1355_;
  wire _1356_;
  wire _1357_;
  wire _1358_;
  wire _1359_;
  wire _1360_;
  wire _1361_;
  wire _1362_;
  wire _1363_;
  wire _1364_;
  wire _1365_;
  wire _1366_;
  wire _1367_;
  wire _1368_;
  wire _1369_;
  wire _1370_;
  wire _1371_;
  wire _1372_;
  wire _1373_;
  wire _1374_;
  wire _1375_;
  wire _1376_;
  wire _1377_;
  wire _1378_;
  wire _1379_;
  wire _1380_;
  wire _1381_;
  wire _1382_;
  wire _1383_;
  wire _1384_;
  wire _1385_;
  wire _1386_;
  wire _1387_;
  wire _1388_;
  wire _1389_;
  wire _1390_;
  wire _1391_;
  wire _1392_;
  wire _1393_;
  wire _1394_;
  wire _1395_;
  wire _1396_;
  wire _1397_;
  wire _1398_;
  wire _1399_;
  wire _1400_;
  wire _1401_;
  wire _1402_;
  wire _1403_;
  wire _1404_;
  wire _1405_;
  wire _1406_;
  wire _1407_;
  wire _1408_;
  wire _1409_;
  wire _1410_;
  wire _1411_;
  wire _1412_;
  wire _1413_;
  wire _1414_;
  wire _1415_;
  wire _1416_;
  wire _1417_;
  wire _1418_;
  wire _1419_;
  wire _1420_;
  wire _1421_;
  wire _1422_;
  wire _1423_;
  wire _1424_;
  wire _1425_;
  wire _1426_;
  wire _1427_;
  wire _1428_;
  wire _1429_;
  wire _1430_;
  wire _1431_;
  wire _1432_;
  wire _1433_;
  wire _1434_;
  wire _1435_;
  wire _1436_;
  wire _1437_;
  wire _1438_;
  wire _1439_;
  wire _1440_;
  wire _1441_;
  wire _1442_;
  wire _1443_;
  wire _1444_;
  wire _1445_;
  wire _1446_;
  wire _1447_;
  wire _1448_;
  wire _1449_;
  wire _1450_;
  wire _1451_;
  wire _1452_;
  wire _1453_;
  wire _1454_;
  wire _1455_;
  wire _1456_;
  wire _1457_;
  wire _1458_;
  wire _1459_;
  wire _1460_;
  wire _1461_;
  wire _1462_;
  wire _1463_;
  wire _1464_;
  wire _1465_;
  wire _1466_;
  wire _1467_;
  wire _1468_;
  wire _1469_;
  wire _1470_;
  wire _1471_;
  wire _1472_;
  wire _1473_;
  wire _1474_;
  wire _1475_;
  wire _1476_;
  wire _1477_;
  input [3:0] byte_sel;
  input clk;
  reg [7:0] cnt;
  reg [127:0] data;
  input go;
  output last;
  input [3:0] latch;
  input [6:0] len;
  input lsb;
  input neg_edge;
  input [31:0] p_in;
  output [127:0] p_out;
  input pos_edge;
  input rst;
  input rx_negedge;
  input s_clk;
  input s_in;
  output s_out;
  reg s_out;
  output tip;
  reg tip;
  input tx_negedge;
  assign _0857_ = ~cnt[4];
  assign _0858_ = ~cnt[5];
  assign _0859_ = _0858_ & _0857_;
  assign _0860_ = ~cnt[6];
  assign _0861_ = ~cnt[7];
  assign _0862_ = _0861_ & _0860_;
  assign _0863_ = _0862_ & _0859_;
  assign _0864_ = ~cnt[0];
  assign _0865_ = ~cnt[1];
  assign _0866_ = _0865_ & _0864_;
  assign _0867_ = ~cnt[2];
  assign _0868_ = ~cnt[3];
  assign _0869_ = _0868_ & _0867_;
  assign _0870_ = _0869_ & _0866_;
  assign last = _0870_ & _0863_;
  assign _0871_ = ~tip;
  assign _0872_ = latch[0] & _0871_;
  assign _0873_ = byte_sel[3] ? p_in[26] : data[26];
  assign _0874_ = latch[1] & _0871_;
  assign _0875_ = latch[2] & _0871_;
  assign _0876_ = latch[3] & _0871_;
  assign _0877_ = ~len[6];
  assign _0878_ = ~rx_negedge;
  assign _0879_ = cnt[1] & cnt[0];
  assign _0880_ = _0879_ & cnt[2];
  assign _0881_ = _0880_ & cnt[3];
  assign _0882_ = _0881_ & cnt[4];
  assign _0883_ = _0882_ & cnt[5];
  assign _0884_ = _0883_ ^ _0860_;
  assign _0885_ = _0878_ ? _0860_ : _0884_;
  assign _0886_ = _0885_ ^ _0877_;
  assign _0887_ = ~_0886_;
  assign _0888_ = ~len[5];
  assign _0889_ = _0882_ ^ _0858_;
  assign _0890_ = _0878_ ? _0858_ : _0889_;
  assign _0891_ = ~_0890_;
  assign _0892_ = _0891_ | _0888_;
  assign _0893_ = _0890_ ^ _0888_;
  assign _0894_ = ~len[4];
  assign _0895_ = _0881_ ^ _0857_;
  assign _0896_ = _0878_ ? _0857_ : _0895_;
  assign _0897_ = ~_0896_;
  assign _0898_ = _0897_ | _0894_;
  assign _0899_ = _0896_ ^ _0894_;
  assign _0900_ = ~len[3];
  assign _0901_ = _0880_ ^ _0868_;
  assign _0902_ = _0878_ ? _0868_ : _0901_;
  assign _0903_ = ~_0902_;
  assign _0904_ = _0903_ | _0900_;
  assign _0905_ = _0902_ ^ _0900_;
  assign _0906_ = ~len[2];
  assign _0907_ = _0879_ ^ _0867_;
  assign _0908_ = _0878_ ? _0867_ : _0907_;
  assign _0909_ = ~_0908_;
  assign _0910_ = _0909_ | _0906_;
  assign _0911_ = _0908_ ^ _0906_;
  assign _0912_ = ~len[1];
  assign _0913_ = cnt[1] ^ cnt[0];
  assign _0914_ = _0878_ ? cnt[1] : _0913_;
  assign _0915_ = _0914_ | _0912_;
  assign _0916_ = _0914_ ^ len[1];
  assign _0917_ = ~len[0];
  assign _0918_ = rx_negedge ^ cnt[0];
  assign _0919_ = _0918_ & _0917_;
  assign _0920_ = _0919_ | _0916_;
  assign _0921_ = _0920_ & _0915_;
  assign _0922_ = _0921_ | _0911_;
  assign _0923_ = _0922_ & _0910_;
  assign _0924_ = _0923_ | _0905_;
  assign _0925_ = _0924_ & _0904_;
  assign _0926_ = _0925_ | _0899_;
  assign _0927_ = _0926_ & _0898_;
  assign _0928_ = _0927_ | _0893_;
  assign _0929_ = _0928_ & _0892_;
  assign _0930_ = _0929_ ^ _0887_;
  assign _0931_ = cnt[1] | cnt[0];
  assign _0932_ = _0931_ | cnt[2];
  assign _0933_ = _0932_ | cnt[3];
  assign _0934_ = _0933_ | cnt[4];
  assign _0935_ = _0934_ | cnt[5];
  assign _0936_ = _0935_ ^ cnt[6];
  assign _0937_ = rx_negedge ? _0860_ : _0936_;
  assign _0938_ = lsb ? _0930_ : _0937_;
  assign _0939_ = ~_0893_;
  assign _0940_ = _0927_ ^ _0939_;
  assign _0941_ = _0934_ ^ cnt[5];
  assign _0942_ = rx_negedge ? _0858_ : _0941_;
  assign _0943_ = lsb ? _0940_ : _0942_;
  assign _0944_ = _0925_ ^ _0899_;
  assign _0945_ = _0933_ ^ cnt[4];
  assign _0946_ = rx_negedge ? _0857_ : _0945_;
  assign _0947_ = ~_0946_;
  assign _0948_ = lsb ? _0944_ : _0947_;
  assign _0949_ = _0923_ ^ _0905_;
  assign _0950_ = ~_0949_;
  assign _0951_ = _0932_ ^ cnt[3];
  assign _0952_ = rx_negedge ? _0868_ : _0951_;
  assign _0953_ = lsb ? _0950_ : _0952_;
  assign _0954_ = ~_0953_;
  assign _0955_ = _0921_ ^ _0911_;
  assign _0956_ = ~_0955_;
  assign _0957_ = _0931_ ^ cnt[2];
  assign _0958_ = rx_negedge ? _0867_ : _0957_;
  assign _0959_ = lsb ? _0956_ : _0958_;
  assign _0960_ = _0919_ ^ _0916_;
  assign _0961_ = rx_negedge ? _0865_ : _0913_;
  assign _0962_ = ~_0961_;
  assign _0963_ = lsb ? _0960_ : _0962_;
  assign _0964_ = _0918_ ^ len[0];
  assign _0965_ = ~_0964_;
  assign _0966_ = lsb ? _0965_ : _0918_;
  assign _0967_ = _0966_ & _0963_;
  assign _0968_ = _0967_ & _0959_;
  assign _0969_ = _0968_ & _0954_;
  assign _0970_ = _0969_ & _0948_;
  assign _0971_ = _0970_ & _0943_;
  assign _0972_ = _0971_ & _0938_;
  assign _0973_ = rx_negedge ? neg_edge : pos_edge;
  assign _0974_ = ~last;
  assign _0975_ = _0974_ | s_clk;
  assign _0976_ = _0975_ & _0973_;
  assign _0977_ = _0929_ ^ _0886_;
  assign _0978_ = ~_0937_;
  assign _0979_ = lsb ? _0977_ : _0978_;
  assign _0980_ = _0927_ ^ _0893_;
  assign _0981_ = ~_0942_;
  assign _0982_ = lsb ? _0980_ : _0981_;
  assign _0983_ = _0966_ ? data[126] : data[127];
  assign _0984_ = _0966_ ? data[124] : data[125];
  assign _0985_ = _0963_ ? _0983_ : _0984_;
  assign _0986_ = _0966_ ? data[122] : data[123];
  assign _0987_ = _0966_ ? data[120] : data[121];
  assign _0988_ = _0963_ ? _0986_ : _0987_;
  assign _0989_ = _0959_ ? _0988_ : _0985_;
  assign _0990_ = _0966_ ? data[118] : data[119];
  assign _0991_ = _0966_ ? data[116] : data[117];
  assign _0992_ = _0963_ ? _0990_ : _0991_;
  assign _0993_ = _0966_ ? data[114] : data[115];
  assign _0994_ = _0966_ ? data[112] : data[113];
  assign _0995_ = _0963_ ? _0993_ : _0994_;
  assign _0996_ = _0959_ ? _0995_ : _0992_;
  assign _0997_ = _0953_ ? _0996_ : _0989_;
  assign _0998_ = _0966_ ? data[110] : data[111];
  assign _0999_ = _0966_ ? data[108] : data[109];
  assign _1000_ = _0963_ ? _0998_ : _0999_;
  assign _1001_ = _0966_ ? data[106] : data[107];
  assign _1002_ = _0966_ ? data[104] : data[105];
  assign _1003_ = _0963_ ? _1001_ : _1002_;
  assign _1004_ = _0959_ ? _1003_ : _1000_;
  assign _1005_ = _0966_ ? data[102] : data[103];
  assign _1006_ = _0966_ ? data[100] : data[101];
  assign _1007_ = _0963_ ? _1005_ : _1006_;
  assign _1008_ = _0966_ ? data[98] : data[99];
  assign _1009_ = _0966_ ? data[96] : data[97];
  assign _1010_ = _0963_ ? _1008_ : _1009_;
  assign _1011_ = _0959_ ? _1010_ : _1007_;
  assign _1012_ = _0953_ ? _1011_ : _1004_;
  assign _1013_ = _0948_ ? _0997_ : _1012_;
  assign _1014_ = _0966_ ? data[94] : data[95];
  assign _1015_ = _0966_ ? data[92] : data[93];
  assign _1016_ = _0963_ ? _1014_ : _1015_;
  assign _1017_ = _0966_ ? data[90] : data[91];
  assign _1018_ = _0966_ ? data[88] : data[89];
  assign _1019_ = _0963_ ? _1017_ : _1018_;
  assign _1020_ = _0959_ ? _1019_ : _1016_;
  assign _1021_ = _0966_ ? data[86] : data[87];
  assign _1022_ = _0966_ ? data[84] : data[85];
  assign _1023_ = _0963_ ? _1021_ : _1022_;
  assign _1024_ = _0966_ ? data[82] : data[83];
  assign _1025_ = _0966_ ? data[80] : data[81];
  assign _1026_ = _0963_ ? _1024_ : _1025_;
  assign _1027_ = _0959_ ? _1026_ : _1023_;
  assign _1028_ = _0953_ ? _1027_ : _1020_;
  assign _1029_ = _0966_ ? data[78] : data[79];
  assign _1030_ = _0966_ ? data[76] : data[77];
  assign _1031_ = _0963_ ? _1029_ : _1030_;
  assign _1032_ = _0966_ ? data[74] : data[75];
  assign _1033_ = _0966_ ? data[72] : data[73];
  assign _1034_ = _0963_ ? _1032_ : _1033_;
  assign _1035_ = _0959_ ? _1034_ : _1031_;
  assign _1036_ = _0966_ ? data[70] : data[71];
  assign _1037_ = _0966_ ? data[68] : data[69];
  assign _1038_ = _0963_ ? _1036_ : _1037_;
  assign _1039_ = _0966_ ? data[66] : data[67];
  assign _1040_ = _0966_ ? data[64] : data[65];
  assign _1041_ = _0963_ ? _1039_ : _1040_;
  assign _1042_ = _0959_ ? _1041_ : _1038_;
  assign _1043_ = _0953_ ? _1042_ : _1035_;
  assign _1044_ = _0948_ ? _1028_ : _1043_;
  assign _1045_ = _0982_ ? _1013_ : _1044_;
  assign _1046_ = _0966_ ? data[62] : data[63];
  assign _1047_ = _0966_ ? data[60] : data[61];
  assign _1048_ = _0963_ ? _1046_ : _1047_;
  assign _1049_ = _0966_ ? data[58] : data[59];
  assign _1050_ = _0966_ ? data[56] : data[57];
  assign _1051_ = _0963_ ? _1049_ : _1050_;
  assign _1052_ = _0959_ ? _1051_ : _1048_;
  assign _1053_ = _0966_ ? data[54] : data[55];
  assign _1054_ = _0966_ ? data[52] : data[53];
  assign _1055_ = _0963_ ? _1053_ : _1054_;
  assign _1056_ = _0966_ ? data[50] : data[51];
  assign _1057_ = _0966_ ? data[48] : data[49];
  assign _1058_ = _0963_ ? _1056_ : _1057_;
  assign _1059_ = _0959_ ? _1058_ : _1055_;
  assign _1060_ = _0953_ ? _1059_ : _1052_;
  assign _1061_ = _0966_ ? data[46] : data[47];
  assign _1062_ = _0966_ ? data[44] : data[45];
  assign _1063_ = _0963_ ? _1061_ : _1062_;
  assign _1064_ = _0966_ ? data[42] : data[43];
  assign _1065_ = _0966_ ? data[40] : data[41];
  assign _1066_ = _0963_ ? _1064_ : _1065_;
  assign _1067_ = _0959_ ? _1066_ : _1063_;
  assign _1068_ = _0966_ ? data[38] : data[39];
  assign _1069_ = _0966_ ? data[36] : data[37];
  assign _1070_ = _0963_ ? _1068_ : _1069_;
  assign _1071_ = _0966_ ? data[34] : data[35];
  assign _1072_ = _0966_ ? data[32] : data[33];
  assign _1073_ = _0963_ ? _1071_ : _1072_;
  assign _1074_ = _0959_ ? _1073_ : _1070_;
  assign _1075_ = _0953_ ? _1074_ : _1067_;
  assign _1076_ = _0948_ ? _1060_ : _1075_;
  assign _1077_ = _0966_ ? data[30] : data[31];
  assign _1078_ = _0966_ ? data[28] : data[29];
  assign _1079_ = _0963_ ? _1077_ : _1078_;
  assign _1080_ = _0966_ ? data[26] : data[27];
  assign _1081_ = _0966_ ? data[24] : data[25];
  assign _1082_ = _0963_ ? _1080_ : _1081_;
  assign _1083_ = _0959_ ? _1082_ : _1079_;
  assign _1084_ = _0966_ ? data[22] : data[23];
  assign _1085_ = _0966_ ? data[20] : data[21];
  assign _1086_ = _0963_ ? _1084_ : _1085_;
  assign _1087_ = _0966_ ? data[18] : data[19];
  assign _1088_ = _0966_ ? data[16] : data[17];
  assign _1089_ = _0963_ ? _1087_ : _1088_;
  assign _1090_ = _0959_ ? _1089_ : _1086_;
  assign _1091_ = _0953_ ? _1090_ : _1083_;
  assign _1092_ = _0966_ ? data[14] : data[15];
  assign _1093_ = _0966_ ? data[12] : data[13];
  assign _1094_ = _0963_ ? _1092_ : _1093_;
  assign _1095_ = _0966_ ? data[10] : data[11];
  assign _1096_ = _0966_ ? data[8] : data[9];
  assign _1097_ = _0963_ ? _1095_ : _1096_;
  assign _1098_ = _0959_ ? _1097_ : _1094_;
  assign _1099_ = _0966_ ? data[6] : data[7];
  assign _1100_ = _0966_ ? data[4] : data[5];
  assign _1101_ = _0963_ ? _1099_ : _1100_;
  assign _1102_ = _0966_ ? data[2] : data[3];
  assign _1103_ = _0966_ ? data[0] : data[1];
  assign _1104_ = _0963_ ? _1102_ : _1103_;
  assign _1105_ = _0959_ ? _1104_ : _1101_;
  assign _1106_ = _0953_ ? _1105_ : _1098_;
  assign _1107_ = _0948_ ? _1091_ : _1106_;
  assign _1108_ = _0982_ ? _1076_ : _1107_;
  assign _1109_ = _0979_ ? _1045_ : _1108_;
  assign _1110_ = _0976_ ? s_in : _1109_;
  assign _1111_ = _0972_ ? _1110_ : data[26];
  assign _1112_ = _0876_ ? data[26] : _1111_;
  assign _1113_ = _0875_ ? data[26] : _1112_;
  assign _1114_ = _0874_ ? data[26] : _1113_;
  assign _0001_[26] = _0872_ ? _0873_ : _1114_;
  assign _1115_ = byte_sel[2] ? p_in[23] : data[55];
  assign _1116_ = ~_0959_;
  assign _1117_ = ~_0966_;
  assign _1118_ = _1117_ & _0963_;
  assign _1119_ = _1118_ & _1116_;
  assign _1120_ = _1119_ & _0953_;
  assign _1121_ = _1120_ & _0948_;
  assign _1122_ = _1121_ & _0982_;
  assign _1123_ = _1122_ & _0938_;
  assign _1124_ = _1123_ ? _1110_ : data[55];
  assign _1125_ = _0876_ ? data[55] : _1124_;
  assign _1126_ = _0875_ ? data[55] : _1125_;
  assign _1127_ = _0874_ ? _1115_ : _1126_;
  assign _0001_[55] = _0872_ ? data[55] : _1127_;
  assign _1128_ = byte_sel[1] ? p_in[8] : data[40];
  assign _1129_ = ~_0948_;
  assign _1130_ = ~_0963_;
  assign _1131_ = _0966_ & _1130_;
  assign _1132_ = _1131_ & _0959_;
  assign _1133_ = _1132_ & _0954_;
  assign _1134_ = _1133_ & _1129_;
  assign _1135_ = _1134_ & _0982_;
  assign _1136_ = _1135_ & _0938_;
  assign _1137_ = _1136_ ? _1110_ : data[40];
  assign _1138_ = _0876_ ? data[40] : _1137_;
  assign _1139_ = _0875_ ? data[40] : _1138_;
  assign _1140_ = _0874_ ? _1128_ : _1139_;
  assign _0001_[40] = _0872_ ? data[40] : _1140_;
  assign _1141_ = byte_sel[1] ? p_in[9] : data[41];
  assign _1142_ = _1117_ & _1130_;
  assign _1143_ = _1142_ & _0959_;
  assign _1144_ = _1143_ & _0954_;
  assign _1145_ = _1144_ & _1129_;
  assign _1146_ = _1145_ & _0982_;
  assign _1147_ = _1146_ & _0938_;
  assign _1148_ = _1147_ ? _1110_ : data[41];
  assign _1149_ = _0876_ ? data[41] : _1148_;
  assign _1150_ = _0875_ ? data[41] : _1149_;
  assign _1151_ = _0874_ ? _1141_ : _1150_;
  assign _0001_[41] = _0872_ ? data[41] : _1151_;
  assign _1152_ = byte_sel[1] ? p_in[10] : data[42];
  assign _1153_ = _0969_ & _1129_;
  assign _1154_ = _1153_ & _0982_;
  assign _1155_ = _1154_ & _0938_;
  assign _1156_ = _1155_ ? _1110_ : data[42];
  assign _1157_ = _0876_ ? data[42] : _1156_;
  assign _1158_ = _0875_ ? data[42] : _1157_;
  assign _1159_ = _0874_ ? _1152_ : _1158_;
  assign _0001_[42] = _0872_ ? data[42] : _1159_;
  assign _1160_ = byte_sel[1] ? p_in[11] : data[43];
  assign _1161_ = _1118_ & _0959_;
  assign _1162_ = _1161_ & _0954_;
  assign _1163_ = _1162_ & _1129_;
  assign _1164_ = _1163_ & _0982_;
  assign _1165_ = _1164_ & _0938_;
  assign _1166_ = _1165_ ? _1110_ : data[43];
  assign _1167_ = _0876_ ? data[43] : _1166_;
  assign _1168_ = _0875_ ? data[43] : _1167_;
  assign _1169_ = _0874_ ? _1160_ : _1168_;
  assign _0001_[43] = _0872_ ? data[43] : _1169_;
  assign _1170_ = byte_sel[1] ? p_in[12] : data[44];
  assign _1171_ = _1131_ & _1116_;
  assign _1172_ = _1171_ & _0954_;
  assign _1173_ = _1172_ & _1129_;
  assign _1174_ = _1173_ & _0982_;
  assign _1175_ = _1174_ & _0938_;
  assign _1176_ = _1175_ ? _1110_ : data[44];
  assign _1177_ = _0876_ ? data[44] : _1176_;
  assign _1178_ = _0875_ ? data[44] : _1177_;
  assign _1179_ = _0874_ ? _1170_ : _1178_;
  assign _0001_[44] = _0872_ ? data[44] : _1179_;
  assign _1180_ = byte_sel[1] ? p_in[13] : data[45];
  assign _1181_ = _1142_ & _1116_;
  assign _1182_ = _1181_ & _0954_;
  assign _1183_ = _1182_ & _1129_;
  assign _1184_ = _1183_ & _0982_;
  assign _1185_ = _1184_ & _0938_;
  assign _1186_ = _1185_ ? _1110_ : data[45];
  assign _1187_ = _0876_ ? data[45] : _1186_;
  assign _1188_ = _0875_ ? data[45] : _1187_;
  assign _1189_ = _0874_ ? _1180_ : _1188_;
  assign _0001_[45] = _0872_ ? data[45] : _1189_;
  assign _1190_ = byte_sel[1] ? p_in[14] : data[46];
  assign _1191_ = _0967_ & _1116_;
  assign _1192_ = _1191_ & _0954_;
  assign _1193_ = _1192_ & _1129_;
  assign _1194_ = _1193_ & _0982_;
  assign _1195_ = _1194_ & _0938_;
  assign _1196_ = _1195_ ? _1110_ : data[46];
  assign _1197_ = _0876_ ? data[46] : _1196_;
  assign _1198_ = _0875_ ? data[46] : _1197_;
  assign _1199_ = _0874_ ? _1190_ : _1198_;
  assign _0001_[46] = _0872_ ? data[46] : _1199_;
  assign _1200_ = byte_sel[1] ? p_in[15] : data[47];
  assign _1201_ = _1119_ & _0954_;
  assign _1202_ = _1201_ & _1129_;
  assign _1203_ = _1202_ & _0982_;
  assign _1204_ = _1203_ & _0938_;
  assign _1205_ = _1204_ ? _1110_ : data[47];
  assign _1206_ = _0876_ ? data[47] : _1205_;
  assign _1207_ = _0875_ ? data[47] : _1206_;
  assign _1208_ = _0874_ ? _1200_ : _1207_;
  assign _0001_[47] = _0872_ ? data[47] : _1208_;
  assign _1209_ = byte_sel[3] ? p_in[27] : data[27];
  assign _1210_ = _1162_ & _0948_;
  assign _1211_ = _1210_ & _0943_;
  assign _1212_ = _1211_ & _0938_;
  assign _1213_ = _1212_ ? _1110_ : data[27];
  assign _1214_ = _0876_ ? data[27] : _1213_;
  assign _1215_ = _0875_ ? data[27] : _1214_;
  assign _1216_ = _0874_ ? data[27] : _1215_;
  assign _0001_[27] = _0872_ ? _1209_ : _1216_;
  assign _1217_ = byte_sel[0] ? p_in[0] : data[32];
  assign _1218_ = _1132_ & _0953_;
  assign _1219_ = _1218_ & _1129_;
  assign _1220_ = _1219_ & _0982_;
  assign _1221_ = _1220_ & _0938_;
  assign _1222_ = _1221_ ? _1110_ : data[32];
  assign _1223_ = _0876_ ? data[32] : _1222_;
  assign _1224_ = _0875_ ? data[32] : _1223_;
  assign _1225_ = _0874_ ? _1217_ : _1224_;
  assign _0001_[32] = _0872_ ? data[32] : _1225_;
  assign _1226_ = byte_sel[0] ? p_in[1] : data[33];
  assign _1227_ = _1143_ & _0953_;
  assign _1228_ = _1227_ & _1129_;
  assign _1229_ = _1228_ & _0982_;
  assign _1230_ = _1229_ & _0938_;
  assign _1231_ = _1230_ ? _1110_ : data[33];
  assign _1232_ = _0876_ ? data[33] : _1231_;
  assign _1233_ = _0875_ ? data[33] : _1232_;
  assign _1234_ = _0874_ ? _1226_ : _1233_;
  assign _0001_[33] = _0872_ ? data[33] : _1234_;
  assign _1235_ = byte_sel[0] ? p_in[2] : data[34];
  assign _1236_ = _0968_ & _0953_;
  assign _1237_ = _1236_ & _1129_;
  assign _1238_ = _1237_ & _0982_;
  assign _1239_ = _1238_ & _0938_;
  assign _1240_ = _1239_ ? _1110_ : data[34];
  assign _1241_ = _0876_ ? data[34] : _1240_;
  assign _1242_ = _0875_ ? data[34] : _1241_;
  assign _1243_ = _0874_ ? _1235_ : _1242_;
  assign _0001_[34] = _0872_ ? data[34] : _1243_;
  assign _1244_ = byte_sel[0] ? p_in[3] : data[35];
  assign _1245_ = _1161_ & _0953_;
  assign _1246_ = _1245_ & _1129_;
  assign _1247_ = _1246_ & _0982_;
  assign _1248_ = _1247_ & _0938_;
  assign _1249_ = _1248_ ? _1110_ : data[35];
  assign _1250_ = _0876_ ? data[35] : _1249_;
  assign _1251_ = _0875_ ? data[35] : _1250_;
  assign _1252_ = _0874_ ? _1244_ : _1251_;
  assign _0001_[35] = _0872_ ? data[35] : _1252_;
  assign _1253_ = byte_sel[0] ? p_in[4] : data[36];
  assign _1254_ = _1171_ & _0953_;
  assign _1255_ = _1254_ & _1129_;
  assign _1256_ = _1255_ & _0982_;
  assign _1257_ = _1256_ & _0938_;
  assign _1258_ = _1257_ ? _1110_ : data[36];
  assign _1259_ = _0876_ ? data[36] : _1258_;
  assign _1260_ = _0875_ ? data[36] : _1259_;
  assign _1261_ = _0874_ ? _1253_ : _1260_;
  assign _0001_[36] = _0872_ ? data[36] : _1261_;
  assign _1262_ = byte_sel[0] ? p_in[5] : data[37];
  assign _1263_ = _1181_ & _0953_;
  assign _1264_ = _1263_ & _1129_;
  assign _1265_ = _1264_ & _0982_;
  assign _1266_ = _1265_ & _0938_;
  assign _1267_ = _1266_ ? _1110_ : data[37];
  assign _1268_ = _0876_ ? data[37] : _1267_;
  assign _1269_ = _0875_ ? data[37] : _1268_;
  assign _1270_ = _0874_ ? _1262_ : _1269_;
  assign _0001_[37] = _0872_ ? data[37] : _1270_;
  assign _1271_ = byte_sel[0] ? p_in[6] : data[38];
  assign _1272_ = _1191_ & _0953_;
  assign _1273_ = _1272_ & _1129_;
  assign _1274_ = _1273_ & _0982_;
  assign _1275_ = _1274_ & _0938_;
  assign _1276_ = _1275_ ? _1110_ : data[38];
  assign _1277_ = _0876_ ? data[38] : _1276_;
  assign _1278_ = _0875_ ? data[38] : _1277_;
  assign _1279_ = _0874_ ? _1271_ : _1278_;
  assign _0001_[38] = _0872_ ? data[38] : _1279_;
  assign _1280_ = byte_sel[0] ? p_in[7] : data[39];
  assign _1281_ = _1120_ & _1129_;
  assign _1282_ = _1281_ & _0982_;
  assign _1283_ = _1282_ & _0938_;
  assign _1284_ = _1283_ ? _1110_ : data[39];
  assign _1285_ = _0876_ ? data[39] : _1284_;
  assign _1286_ = _0875_ ? data[39] : _1285_;
  assign _1287_ = _0874_ ? _1280_ : _1286_;
  assign _0001_[39] = _0872_ ? data[39] : _1287_;
  assign _1288_ = byte_sel[3] ? p_in[24] : data[88];
  assign _1289_ = _1133_ & _0948_;
  assign _1290_ = _1289_ & _0943_;
  assign _1291_ = _1290_ & _0979_;
  assign _1292_ = _1291_ ? _1110_ : data[88];
  assign _1293_ = _0876_ ? data[88] : _1292_;
  assign _1294_ = _0875_ ? _1288_ : _1293_;
  assign _1295_ = _0874_ ? data[88] : _1294_;
  assign _0001_[88] = _0872_ ? data[88] : _1295_;
  assign _1296_ = byte_sel[3] ? p_in[28] : data[28];
  assign _1297_ = _1172_ & _0948_;
  assign _1298_ = _1297_ & _0943_;
  assign _1299_ = _1298_ & _0938_;
  assign _1300_ = _1299_ ? _1110_ : data[28];
  assign _1301_ = _0876_ ? data[28] : _1300_;
  assign _1302_ = _0875_ ? data[28] : _1301_;
  assign _1303_ = _0874_ ? data[28] : _1302_;
  assign _0001_[28] = _0872_ ? _1296_ : _1303_;
  assign _1304_ = byte_sel[3] ? p_in[25] : data[89];
  assign _1305_ = _1144_ & _0948_;
  assign _1306_ = _1305_ & _0943_;
  assign _1307_ = _1306_ & _0979_;
  assign _1308_ = _1307_ ? _1110_ : data[89];
  assign _1309_ = _0876_ ? data[89] : _1308_;
  assign _1310_ = _0875_ ? _1304_ : _1309_;
  assign _1311_ = _0874_ ? data[89] : _1310_;
  assign _0001_[89] = _0872_ ? data[89] : _1311_;
  assign _1312_ = byte_sel[3] ? p_in[26] : data[90];
  assign _1313_ = _0971_ & _0979_;
  assign _1314_ = _1313_ ? _1110_ : data[90];
  assign _1315_ = _0876_ ? data[90] : _1314_;
  assign _1316_ = _0875_ ? _1312_ : _1315_;
  assign _1317_ = _0874_ ? data[90] : _1316_;
  assign _0001_[90] = _0872_ ? data[90] : _1317_;
  assign _1318_ = byte_sel[3] ? p_in[27] : data[91];
  assign _1319_ = _1211_ & _0979_;
  assign _1320_ = _1319_ ? _1110_ : data[91];
  assign _1321_ = _0876_ ? data[91] : _1320_;
  assign _1322_ = _0875_ ? _1318_ : _1321_;
  assign _1323_ = _0874_ ? data[91] : _1322_;
  assign _0001_[91] = _0872_ ? data[91] : _1323_;
  assign _1324_ = byte_sel[3] ? p_in[28] : data[92];
  assign _1325_ = _1298_ & _0979_;
  assign _1326_ = _1325_ ? _1110_ : data[92];
  assign _1327_ = _0876_ ? data[92] : _1326_;
  assign _1328_ = _0875_ ? _1324_ : _1327_;
  assign _1329_ = _0874_ ? data[92] : _1328_;
  assign _0001_[92] = _0872_ ? data[92] : _1329_;
  assign _1330_ = byte_sel[3] ? p_in[29] : data[93];
  assign _1331_ = _1182_ & _0948_;
  assign _1332_ = _1331_ & _0943_;
  assign _1333_ = _1332_ & _0979_;
  assign _1334_ = _1333_ ? _1110_ : data[93];
  assign _1335_ = _0876_ ? data[93] : _1334_;
  assign _1336_ = _0875_ ? _1330_ : _1335_;
  assign _1337_ = _0874_ ? data[93] : _1336_;
  assign _0001_[93] = _0872_ ? data[93] : _1337_;
  assign _1338_ = byte_sel[3] ? p_in[30] : data[94];
  assign _1339_ = _1192_ & _0948_;
  assign _1340_ = _1339_ & _0943_;
  assign _1341_ = _1340_ & _0979_;
  assign _1342_ = _1341_ ? _1110_ : data[94];
  assign _1343_ = _0876_ ? data[94] : _1342_;
  assign _1344_ = _0875_ ? _1338_ : _1343_;
  assign _1345_ = _0874_ ? data[94] : _1344_;
  assign _0001_[94] = _0872_ ? data[94] : _1345_;
  assign _1346_ = byte_sel[3] ? p_in[31] : data[95];
  assign _1347_ = _1201_ & _0948_;
  assign _1348_ = _1347_ & _0943_;
  assign _1349_ = _1348_ & _0979_;
  assign _1350_ = _1349_ ? _1110_ : data[95];
  assign _1351_ = _0876_ ? data[95] : _1350_;
  assign _1352_ = _0875_ ? _1346_ : _1351_;
  assign _1353_ = _0874_ ? data[95] : _1352_;
  assign _0001_[95] = _0872_ ? data[95] : _1353_;
  assign _1354_ = byte_sel[2] ? p_in[16] : data[80];
  assign _1355_ = _1218_ & _0948_;
  assign _1356_ = _1355_ & _0943_;
  assign _1357_ = _1356_ & _0979_;
  assign _1358_ = _1357_ ? _1110_ : data[80];
  assign _1359_ = _0876_ ? data[80] : _1358_;
  assign _1360_ = _0875_ ? _1354_ : _1359_;
  assign _1361_ = _0874_ ? data[80] : _1360_;
  assign _0001_[80] = _0872_ ? data[80] : _1361_;
  assign _1362_ = byte_sel[3] ? p_in[29] : data[29];
  assign _1363_ = _1332_ & _0938_;
  assign _1364_ = _1363_ ? _1110_ : data[29];
  assign _1365_ = _0876_ ? data[29] : _1364_;
  assign _1366_ = _0875_ ? data[29] : _1365_;
  assign _1367_ = _0874_ ? data[29] : _1366_;
  assign _0001_[29] = _0872_ ? _1362_ : _1367_;
  assign _1368_ = byte_sel[2] ? p_in[17] : data[81];
  assign _1369_ = _1227_ & _0948_;
  assign _1370_ = _1369_ & _0943_;
  assign _1371_ = _1370_ & _0979_;
  assign _1372_ = _1371_ ? _1110_ : data[81];
  assign _1373_ = _0876_ ? data[81] : _1372_;
  assign _1374_ = _0875_ ? _1368_ : _1373_;
  assign _1375_ = _0874_ ? data[81] : _1374_;
  assign _0001_[81] = _0872_ ? data[81] : _1375_;
  assign _1376_ = byte_sel[2] ? p_in[18] : data[82];
  assign _1377_ = _1236_ & _0948_;
  assign _1378_ = _1377_ & _0943_;
  assign _1379_ = _1378_ & _0979_;
  assign _1380_ = _1379_ ? _1110_ : data[82];
  assign _1381_ = _0876_ ? data[82] : _1380_;
  assign _1382_ = _0875_ ? _1376_ : _1381_;
  assign _1383_ = _0874_ ? data[82] : _1382_;
  assign _0001_[82] = _0872_ ? data[82] : _1383_;
  assign _1384_ = byte_sel[2] ? p_in[19] : data[83];
  assign _1385_ = _1245_ & _0948_;
  assign _1386_ = _1385_ & _0943_;
  assign _1387_ = _1386_ & _0979_;
  assign _1388_ = _1387_ ? _1110_ : data[83];
  assign _1389_ = _0876_ ? data[83] : _1388_;
  assign _1390_ = _0875_ ? _1384_ : _1389_;
  assign _1391_ = _0874_ ? data[83] : _1390_;
  assign _0001_[83] = _0872_ ? data[83] : _1391_;
  assign _1392_ = byte_sel[2] ? p_in[20] : data[84];
  assign _1393_ = _1254_ & _0948_;
  assign _1394_ = _1393_ & _0943_;
  assign _1395_ = _1394_ & _0979_;
  assign _1396_ = _1395_ ? _1110_ : data[84];
  assign _1397_ = _0876_ ? data[84] : _1396_;
  assign _1398_ = _0875_ ? _1392_ : _1397_;
  assign _1399_ = _0874_ ? data[84] : _1398_;
  assign _0001_[84] = _0872_ ? data[84] : _1399_;
  assign _1400_ = byte_sel[2] ? p_in[21] : data[85];
  assign _1401_ = _1263_ & _0948_;
  assign _1402_ = _1401_ & _0943_;
  assign _1403_ = _1402_ & _0979_;
  assign _1404_ = _1403_ ? _1110_ : data[85];
  assign _1405_ = _0876_ ? data[85] : _1404_;
  assign _1406_ = _0875_ ? _1400_ : _1405_;
  assign _1407_ = _0874_ ? data[85] : _1406_;
  assign _0001_[85] = _0872_ ? data[85] : _1407_;
  assign _1408_ = byte_sel[2] ? p_in[22] : data[86];
  assign _1409_ = _1272_ & _0948_;
  assign _1410_ = _1409_ & _0943_;
  assign _1411_ = _1410_ & _0979_;
  assign _1412_ = _1411_ ? _1110_ : data[86];
  assign _1413_ = _0876_ ? data[86] : _1412_;
  assign _1414_ = _0875_ ? _1408_ : _1413_;
  assign _1415_ = _0874_ ? data[86] : _1414_;
  assign _0001_[86] = _0872_ ? data[86] : _1415_;
  assign _1416_ = byte_sel[2] ? p_in[23] : data[87];
  assign _1417_ = _1121_ & _0943_;
  assign _1418_ = _1417_ & _0979_;
  assign _1419_ = _1418_ ? _1110_ : data[87];
  assign _1420_ = _0876_ ? data[87] : _1419_;
  assign _1421_ = _0875_ ? _1416_ : _1420_;
  assign _1422_ = _0874_ ? data[87] : _1421_;
  assign _0001_[87] = _0872_ ? data[87] : _1422_;
  assign _1423_ = byte_sel[1] ? p_in[8] : data[72];
  assign _1424_ = _1134_ & _0943_;
  assign _1425_ = _1424_ & _0979_;
  assign _1426_ = _1425_ ? _1110_ : data[72];
  assign _1427_ = _0876_ ? data[72] : _1426_;
  assign _1428_ = _0875_ ? _1423_ : _1427_;
  assign _1429_ = _0874_ ? data[72] : _1428_;
  assign _0001_[72] = _0872_ ? data[72] : _1429_;
  assign _1430_ = byte_sel[3] ? p_in[30] : data[30];
  assign _1431_ = _1340_ & _0938_;
  assign _1432_ = _1431_ ? _1110_ : data[30];
  assign _1433_ = _0876_ ? data[30] : _1432_;
  assign _1434_ = _0875_ ? data[30] : _1433_;
  assign _1435_ = _0874_ ? data[30] : _1434_;
  assign _0001_[30] = _0872_ ? _1430_ : _1435_;
  assign _1436_ = byte_sel[1] ? p_in[9] : data[73];
  assign _1437_ = _1145_ & _0943_;
  assign _1438_ = _1437_ & _0979_;
  assign _1439_ = _1438_ ? _1110_ : data[73];
  assign _1440_ = _0876_ ? data[73] : _1439_;
  assign _1441_ = _0875_ ? _1436_ : _1440_;
  assign _1442_ = _0874_ ? data[73] : _1441_;
  assign _0001_[73] = _0872_ ? data[73] : _1442_;
  assign _1443_ = byte_sel[1] ? p_in[10] : data[74];
  assign _1444_ = _1153_ & _0943_;
  assign _1445_ = _1444_ & _0979_;
  assign _1446_ = _1445_ ? _1110_ : data[74];
  assign _1447_ = _0876_ ? data[74] : _1446_;
  assign _1448_ = _0875_ ? _1443_ : _1447_;
  assign _1449_ = _0874_ ? data[74] : _1448_;
  assign _0001_[74] = _0872_ ? data[74] : _1449_;
  assign _1450_ = byte_sel[1] ? p_in[11] : data[75];
  assign _1451_ = _1163_ & _0943_;
  assign _1452_ = _1451_ & _0979_;
  assign _1453_ = _1452_ ? _1110_ : data[75];
  assign _1454_ = _0876_ ? data[75] : _1453_;
  assign _1455_ = _0875_ ? _1450_ : _1454_;
  assign _1456_ = _0874_ ? data[75] : _1455_;
  assign _0001_[75] = _0872_ ? data[75] : _1456_;
  assign _1457_ = byte_sel[1] ? p_in[12] : data[76];
  assign _1458_ = _1173_ & _0943_;
  assign _1459_ = _1458_ & _0979_;
  assign _1460_ = _1459_ ? _1110_ : data[76];
  assign _1461_ = _0876_ ? data[76] : _1460_;
  assign _1462_ = _0875_ ? _1457_ : _1461_;
  assign _1463_ = _0874_ ? data[76] : _1462_;
  assign _0001_[76] = _0872_ ? data[76] : _1463_;
  assign _1464_ = byte_sel[1] ? p_in[13] : data[77];
  assign _1465_ = _1183_ & _0943_;
  assign _1466_ = _1465_ & _0979_;
  assign _1467_ = _1466_ ? _1110_ : data[77];
  assign _1468_ = _0876_ ? data[77] : _1467_;
  assign _1469_ = _0875_ ? _1464_ : _1468_;
  assign _1470_ = _0874_ ? data[77] : _1469_;
  assign _0001_[77] = _0872_ ? data[77] : _1470_;
  assign _1471_ = byte_sel[1] ? p_in[14] : data[78];
  assign _1472_ = _1193_ & _0943_;
  assign _1473_ = _1472_ & _0979_;
  assign _1474_ = _1473_ ? _1110_ : data[78];
  assign _1475_ = _0876_ ? data[78] : _1474_;
  assign _1476_ = _0875_ ? _1471_ : _1475_;
  assign _1477_ = _0874_ ? data[78] : _1476_;
  assign _0001_[78] = _0872_ ? data[78] : _1477_;
  assign _0004_ = byte_sel[1] ? p_in[15] : data[79];
  assign _0005_ = _1202_ & _0943_;
  assign _0006_ = _0005_ & _0979_;
  assign _0007_ = _0006_ ? _1110_ : data[79];
  assign _0008_ = _0876_ ? data[79] : _0007_;
  assign _0009_ = _0875_ ? _0004_ : _0008_;
  assign _0010_ = _0874_ ? data[79] : _0009_;
  assign _0001_[79] = _0872_ ? data[79] : _0010_;
  assign _0011_ = byte_sel[0] ? p_in[0] : data[64];
  assign _0012_ = _1219_ & _0943_;
  assign _0013_ = _0012_ & _0979_;
  assign _0014_ = _0013_ ? _1110_ : data[64];
  assign _0015_ = _0876_ ? data[64] : _0014_;
  assign _0016_ = _0875_ ? _0011_ : _0015_;
  assign _0017_ = _0874_ ? data[64] : _0016_;
  assign _0001_[64] = _0872_ ? data[64] : _0017_;
  assign _0018_ = byte_sel[3] ? p_in[31] : data[31];
  assign _0019_ = _1348_ & _0938_;
  assign _0020_ = _0019_ ? _1110_ : data[31];
  assign _0021_ = _0876_ ? data[31] : _0020_;
  assign _0022_ = _0875_ ? data[31] : _0021_;
  assign _0023_ = _0874_ ? data[31] : _0022_;
  assign _0001_[31] = _0872_ ? _0018_ : _0023_;
  assign _0024_ = byte_sel[0] ? p_in[1] : data[65];
  assign _0025_ = _1228_ & _0943_;
  assign _0026_ = _0025_ & _0979_;
  assign _0027_ = _0026_ ? _1110_ : data[65];
  assign _0028_ = _0876_ ? data[65] : _0027_;
  assign _0029_ = _0875_ ? _0024_ : _0028_;
  assign _0030_ = _0874_ ? data[65] : _0029_;
  assign _0001_[65] = _0872_ ? data[65] : _0030_;
  assign _0031_ = byte_sel[0] ? p_in[2] : data[66];
  assign _0032_ = _1237_ & _0943_;
  assign _0033_ = _0032_ & _0979_;
  assign _0034_ = _0033_ ? _1110_ : data[66];
  assign _0035_ = _0876_ ? data[66] : _0034_;
  assign _0036_ = _0875_ ? _0031_ : _0035_;
  assign _0037_ = _0874_ ? data[66] : _0036_;
  assign _0001_[66] = _0872_ ? data[66] : _0037_;
  assign _0038_ = byte_sel[0] ? p_in[3] : data[67];
  assign _0039_ = _1246_ & _0943_;
  assign _0040_ = _0039_ & _0979_;
  assign _0041_ = _0040_ ? _1110_ : data[67];
  assign _0042_ = _0876_ ? data[67] : _0041_;
  assign _0043_ = _0875_ ? _0038_ : _0042_;
  assign _0044_ = _0874_ ? data[67] : _0043_;
  assign _0001_[67] = _0872_ ? data[67] : _0044_;
  assign _0045_ = byte_sel[0] ? p_in[4] : data[68];
  assign _0046_ = _1255_ & _0943_;
  assign _0047_ = _0046_ & _0979_;
  assign _0048_ = _0047_ ? _1110_ : data[68];
  assign _0049_ = _0876_ ? data[68] : _0048_;
  assign _0050_ = _0875_ ? _0045_ : _0049_;
  assign _0051_ = _0874_ ? data[68] : _0050_;
  assign _0001_[68] = _0872_ ? data[68] : _0051_;
  assign _0052_ = byte_sel[0] ? p_in[5] : data[69];
  assign _0053_ = _1264_ & _0943_;
  assign _0054_ = _0053_ & _0979_;
  assign _0055_ = _0054_ ? _1110_ : data[69];
  assign _0056_ = _0876_ ? data[69] : _0055_;
  assign _0057_ = _0875_ ? _0052_ : _0056_;
  assign _0058_ = _0874_ ? data[69] : _0057_;
  assign _0001_[69] = _0872_ ? data[69] : _0058_;
  assign _0059_ = byte_sel[0] ? p_in[6] : data[70];
  assign _0060_ = _1273_ & _0943_;
  assign _0061_ = _0060_ & _0979_;
  assign _0062_ = _0061_ ? _1110_ : data[70];
  assign _0063_ = _0876_ ? data[70] : _0062_;
  assign _0064_ = _0875_ ? _0059_ : _0063_;
  assign _0065_ = _0874_ ? data[70] : _0064_;
  assign _0001_[70] = _0872_ ? data[70] : _0065_;
  assign _0066_ = byte_sel[0] ? p_in[7] : data[71];
  assign _0067_ = _1281_ & _0943_;
  assign _0068_ = _0067_ & _0979_;
  assign _0069_ = _0068_ ? _1110_ : data[71];
  assign _0070_ = _0876_ ? data[71] : _0069_;
  assign _0071_ = _0875_ ? _0066_ : _0070_;
  assign _0072_ = _0874_ ? data[71] : _0071_;
  assign _0001_[71] = _0872_ ? data[71] : _0072_;
  assign _0073_ = byte_sel[3] ? p_in[24] : data[120];
  assign _0074_ = _1289_ & _0982_;
  assign _0075_ = _0074_ & _0979_;
  assign _0076_ = _0075_ ? _1110_ : data[120];
  assign _0077_ = _0876_ ? _0073_ : _0076_;
  assign _0078_ = _0875_ ? data[120] : _0077_;
  assign _0079_ = _0874_ ? data[120] : _0078_;
  assign _0001_[120] = _0872_ ? data[120] : _0079_;
  assign _0080_ = byte_sel[2] ? p_in[16] : data[16];
  assign _0081_ = _1356_ & _0938_;
  assign _0082_ = _0081_ ? _1110_ : data[16];
  assign _0083_ = _0876_ ? data[16] : _0082_;
  assign _0084_ = _0875_ ? data[16] : _0083_;
  assign _0085_ = _0874_ ? data[16] : _0084_;
  assign _0001_[16] = _0872_ ? _0080_ : _0085_;
  assign _0086_ = byte_sel[3] ? p_in[25] : data[121];
  assign _0087_ = _1305_ & _0982_;
  assign _0088_ = _0087_ & _0979_;
  assign _0089_ = _0088_ ? _1110_ : data[121];
  assign _0090_ = _0876_ ? _0086_ : _0089_;
  assign _0091_ = _0875_ ? data[121] : _0090_;
  assign _0092_ = _0874_ ? data[121] : _0091_;
  assign _0001_[121] = _0872_ ? data[121] : _0092_;
  assign _0093_ = byte_sel[3] ? p_in[26] : data[122];
  assign _0094_ = _0970_ & _0982_;
  assign _0095_ = _0094_ & _0979_;
  assign _0096_ = _0095_ ? _1110_ : data[122];
  assign _0097_ = _0876_ ? _0093_ : _0096_;
  assign _0098_ = _0875_ ? data[122] : _0097_;
  assign _0099_ = _0874_ ? data[122] : _0098_;
  assign _0001_[122] = _0872_ ? data[122] : _0099_;
  assign _0100_ = byte_sel[3] ? p_in[27] : data[123];
  assign _0101_ = _1210_ & _0982_;
  assign _0102_ = _0101_ & _0979_;
  assign _0103_ = _0102_ ? _1110_ : data[123];
  assign _0104_ = _0876_ ? _0100_ : _0103_;
  assign _0105_ = _0875_ ? data[123] : _0104_;
  assign _0106_ = _0874_ ? data[123] : _0105_;
  assign _0001_[123] = _0872_ ? data[123] : _0106_;
  assign _0107_ = byte_sel[3] ? p_in[28] : data[124];
  assign _0108_ = _1297_ & _0982_;
  assign _0109_ = _0108_ & _0979_;
  assign _0110_ = _0109_ ? _1110_ : data[124];
  assign _0111_ = _0876_ ? _0107_ : _0110_;
  assign _0112_ = _0875_ ? data[124] : _0111_;
  assign _0113_ = _0874_ ? data[124] : _0112_;
  assign _0001_[124] = _0872_ ? data[124] : _0113_;
  assign _0114_ = byte_sel[3] ? p_in[29] : data[125];
  assign _0115_ = _1331_ & _0982_;
  assign _0116_ = _0115_ & _0979_;
  assign _0117_ = _0116_ ? _1110_ : data[125];
  assign _0118_ = _0876_ ? _0114_ : _0117_;
  assign _0119_ = _0875_ ? data[125] : _0118_;
  assign _0120_ = _0874_ ? data[125] : _0119_;
  assign _0001_[125] = _0872_ ? data[125] : _0120_;
  assign _0121_ = byte_sel[3] ? p_in[30] : data[126];
  assign _0122_ = _1339_ & _0982_;
  assign _0123_ = _0122_ & _0979_;
  assign _0124_ = _0123_ ? _1110_ : data[126];
  assign _0125_ = _0876_ ? _0121_ : _0124_;
  assign _0126_ = _0875_ ? data[126] : _0125_;
  assign _0127_ = _0874_ ? data[126] : _0126_;
  assign _0001_[126] = _0872_ ? data[126] : _0127_;
  assign _0128_ = byte_sel[2] ? p_in[17] : data[17];
  assign _0129_ = _1370_ & _0938_;
  assign _0130_ = _0129_ ? _1110_ : data[17];
  assign _0131_ = _0876_ ? data[17] : _0130_;
  assign _0132_ = _0875_ ? data[17] : _0131_;
  assign _0133_ = _0874_ ? data[17] : _0132_;
  assign _0001_[17] = _0872_ ? _0128_ : _0133_;
  assign _0134_ = byte_sel[3] ? p_in[31] : data[127];
  assign _0135_ = _1393_ & _0982_;
  assign _0136_ = _0135_ & _0979_;
  assign _0137_ = _1401_ & _0982_;
  assign _0138_ = _0137_ & _0979_;
  assign _0139_ = _0138_ | _0136_;
  assign _0140_ = _1409_ & _0982_;
  assign _0141_ = _0140_ & _0979_;
  assign _0142_ = _1122_ & _0979_;
  assign _0143_ = _0142_ | _0141_;
  assign _0144_ = _0143_ | _0139_;
  assign _0145_ = _1355_ & _0982_;
  assign _0146_ = _0145_ & _0979_;
  assign _0147_ = _1369_ & _0982_;
  assign _0148_ = _0147_ & _0979_;
  assign _0149_ = _0148_ | _0146_;
  assign _0150_ = _1377_ & _0982_;
  assign _0151_ = _0150_ & _0979_;
  assign _0152_ = _1385_ & _0982_;
  assign _0153_ = _0152_ & _0979_;
  assign _0154_ = _0153_ | _0151_;
  assign _0155_ = _0154_ | _0149_;
  assign _0156_ = _0155_ | _0144_;
  assign _0157_ = _0108_ & _0938_;
  assign _0158_ = _0115_ & _0938_;
  assign _0159_ = _0158_ | _0157_;
  assign _0160_ = _0122_ & _0938_;
  assign _0161_ = _1347_ & _0982_;
  assign _0162_ = _0161_ & _0938_;
  assign _0163_ = _0162_ | _0160_;
  assign _0164_ = _0163_ | _0159_;
  assign _0165_ = _0074_ & _0938_;
  assign _0166_ = _0087_ & _0938_;
  assign _0167_ = _0166_ | _0165_;
  assign _0168_ = _0094_ & _0938_;
  assign _0169_ = _0101_ & _0938_;
  assign _0170_ = _0169_ | _0168_;
  assign _0171_ = _0170_ | _0167_;
  assign _0172_ = _0171_ | _0164_;
  assign _0173_ = _0172_ | _0156_;
  assign _0174_ = _1256_ & _0979_;
  assign _0175_ = _1265_ & _0979_;
  assign _0176_ = _0175_ | _0174_;
  assign _0177_ = _1274_ & _0979_;
  assign _0178_ = _1282_ & _0979_;
  assign _0179_ = _0178_ | _0177_;
  assign _0180_ = _0179_ | _0176_;
  assign _0181_ = _1220_ & _0979_;
  assign _0182_ = _1229_ & _0979_;
  assign _0183_ = _0182_ | _0181_;
  assign _0184_ = _1238_ & _0979_;
  assign _0185_ = _1247_ & _0979_;
  assign _0186_ = _0185_ | _0184_;
  assign _0187_ = _0186_ | _0183_;
  assign _0188_ = _0187_ | _0180_;
  assign _0189_ = _1174_ & _0979_;
  assign _0190_ = _1184_ & _0979_;
  assign _0191_ = _0190_ | _0189_;
  assign _0192_ = _1194_ & _0979_;
  assign _0193_ = _1203_ & _0979_;
  assign _0194_ = _0193_ | _0192_;
  assign _0195_ = _0194_ | _0191_;
  assign _0196_ = _1135_ & _0979_;
  assign _0197_ = _1146_ & _0979_;
  assign _0198_ = _0197_ | _0196_;
  assign _0199_ = _1154_ & _0979_;
  assign _0200_ = _1164_ & _0979_;
  assign _0201_ = _0200_ | _0199_;
  assign _0202_ = _0201_ | _0198_;
  assign _0203_ = _0202_ | _0195_;
  assign _0204_ = _0203_ | _0188_;
  assign _0205_ = _0204_ | _0173_;
  assign _0206_ = _1410_ & _0938_;
  assign _0207_ = _1417_ & _0938_;
  assign _0208_ = _0207_ | _0206_;
  assign _0209_ = _1290_ & _0938_;
  assign _0210_ = _1306_ & _0938_;
  assign _0211_ = _0210_ | _0209_;
  assign _0212_ = _0211_ | _0208_;
  assign _0213_ = _1378_ & _0938_;
  assign _0214_ = _1386_ & _0938_;
  assign _0215_ = _0214_ | _0213_;
  assign _0216_ = _1394_ & _0938_;
  assign _0217_ = _1402_ & _0938_;
  assign _0218_ = _0217_ | _0216_;
  assign _0219_ = _0218_ | _0215_;
  assign _0220_ = _0219_ | _0212_;
  assign _0221_ = _0140_ & _0938_;
  assign _0222_ = _0135_ & _0938_;
  assign _0223_ = _0137_ & _0938_;
  assign _0224_ = _0223_ | _0222_;
  assign _0225_ = _0224_ | _0221_;
  assign _0226_ = _0145_ & _0938_;
  assign _0227_ = _0147_ & _0938_;
  assign _0228_ = _0227_ | _0226_;
  assign _0229_ = _0150_ & _0938_;
  assign _0230_ = _0152_ & _0938_;
  assign _0231_ = _0230_ | _0229_;
  assign _0232_ = _0231_ | _0228_;
  assign _0233_ = _0232_ | _0225_;
  assign _0234_ = _0233_ | _0220_;
  assign _0235_ = _0046_ & _0938_;
  assign _0236_ = _0053_ & _0938_;
  assign _0237_ = _0236_ | _0235_;
  assign _0238_ = _0060_ & _0938_;
  assign _0239_ = _0067_ & _0938_;
  assign _0240_ = _0239_ | _0238_;
  assign _0241_ = _0240_ | _0237_;
  assign _0242_ = _0012_ & _0938_;
  assign _0243_ = _0025_ & _0938_;
  assign _0244_ = _0243_ | _0242_;
  assign _0245_ = _0032_ & _0938_;
  assign _0246_ = _0039_ & _0938_;
  assign _0247_ = _0246_ | _0245_;
  assign _0248_ = _0247_ | _0244_;
  assign _0249_ = _0248_ | _0241_;
  assign _0250_ = _1458_ & _0938_;
  assign _0251_ = _1465_ & _0938_;
  assign _0252_ = _0251_ | _0250_;
  assign _0253_ = _1472_ & _0938_;
  assign _0254_ = _0005_ & _0938_;
  assign _0255_ = _0254_ | _0253_;
  assign _0256_ = _0255_ | _0252_;
  assign _0257_ = _1424_ & _0938_;
  assign _0258_ = _1437_ & _0938_;
  assign _0259_ = _0258_ | _0257_;
  assign _0260_ = _1444_ & _0938_;
  assign _0261_ = _1451_ & _0938_;
  assign _0262_ = _0261_ | _0260_;
  assign _0263_ = _0262_ | _0259_;
  assign _0264_ = _0263_ | _0256_;
  assign _0265_ = _0264_ | _0249_;
  assign _0266_ = _0265_ | _0234_;
  assign _0267_ = _0266_ | _0205_;
  assign _0268_ = _0938_ ? _1298_ : _1306_;
  assign _0269_ = _1319_ | _1313_;
  assign _0270_ = _0269_ | _0268_;
  assign _0271_ = _1275_ | _1266_;
  assign _0272_ = _0938_ ? _1282_ : _1290_;
  assign _0273_ = _0272_ | _0271_;
  assign _0274_ = _0273_ | _0270_;
  assign _0275_ = _0938_ ? _1332_ : _1356_;
  assign _0276_ = _1379_ | _1371_;
  assign _0277_ = _0276_ | _0275_;
  assign _0278_ = _1333_ | _1325_;
  assign _0279_ = _1349_ | _1341_;
  assign _0280_ = _0279_ | _0278_;
  assign _0281_ = _0280_ | _0277_;
  assign _0282_ = _0281_ | _0274_;
  assign _0283_ = _1165_ | _1155_;
  assign _0284_ = _1185_ | _1175_;
  assign _0285_ = _0284_ | _0283_;
  assign _0286_ = _1123_ | _0972_;
  assign _0287_ = _1147_ | _1136_;
  assign _0288_ = _0287_ | _0286_;
  assign _0289_ = _0288_ | _0285_;
  assign _0290_ = _1239_ | _1230_;
  assign _0291_ = _1257_ | _1248_;
  assign _0292_ = _0291_ | _0290_;
  assign _0293_ = _1204_ | _1195_;
  assign _0294_ = _1221_ | _1212_;
  assign _0295_ = _0294_ | _0293_;
  assign _0296_ = _0295_ | _0292_;
  assign _0297_ = _0296_ | _0289_;
  assign _0298_ = _0297_ | _0282_;
  assign _0299_ = _0061_ | _0054_;
  assign _0300_ = _0075_ | _0068_;
  assign _0301_ = _0300_ | _0299_;
  assign _0302_ = _0033_ | _0026_;
  assign _0303_ = _0047_ | _0040_;
  assign _0304_ = _0303_ | _0302_;
  assign _0305_ = _0304_ | _0301_;
  assign _0306_ = _0116_ | _0109_;
  assign _0307_ = _0938_ ? _1370_ : _0122_;
  assign _0308_ = _0307_ | _0306_;
  assign _0309_ = _0938_ ? _1356_ : _0087_;
  assign _0310_ = _0102_ | _0095_;
  assign _0311_ = _0310_ | _0309_;
  assign _0312_ = _0311_ | _0308_;
  assign _0313_ = _0312_ | _0305_;
  assign _0314_ = _1425_ | _1418_;
  assign _0315_ = _0938_ ? _1340_ : _1437_;
  assign _0316_ = _0315_ | _0314_;
  assign _0317_ = _1395_ | _1387_;
  assign _0318_ = _1411_ | _1403_;
  assign _0319_ = _0318_ | _0317_;
  assign _0320_ = _0319_ | _0316_;
  assign _0321_ = _0006_ | _1473_;
  assign _0322_ = _0938_ ? _1348_ : _0012_;
  assign _0323_ = _0322_ | _0321_;
  assign _0324_ = _1452_ | _1445_;
  assign _0325_ = _1466_ | _1459_;
  assign _0326_ = _0325_ | _0324_;
  assign _0327_ = _0326_ | _0323_;
  assign _0328_ = _0327_ | _0320_;
  assign _0329_ = _0328_ | _0313_;
  assign _0330_ = _0329_ | _0298_;
  assign _0331_ = _0330_ | _0267_;
  assign _0332_ = _0331_ ? data[127] : _1110_;
  assign _0333_ = _0876_ ? _0134_ : _0332_;
  assign _0334_ = _0875_ ? data[127] : _0333_;
  assign _0335_ = _0874_ ? data[127] : _0334_;
  assign _0001_[127] = _0872_ ? data[127] : _0335_;
  assign _0336_ = byte_sel[2] ? p_in[16] : data[112];
  assign _0337_ = _0146_ ? _1110_ : data[112];
  assign _0338_ = _0876_ ? _0336_ : _0337_;
  assign _0339_ = _0875_ ? data[112] : _0338_;
  assign _0340_ = _0874_ ? data[112] : _0339_;
  assign _0001_[112] = _0872_ ? data[112] : _0340_;
  assign _0341_ = byte_sel[2] ? p_in[17] : data[113];
  assign _0342_ = _0148_ ? _1110_ : data[113];
  assign _0343_ = _0876_ ? _0341_ : _0342_;
  assign _0344_ = _0875_ ? data[113] : _0343_;
  assign _0345_ = _0874_ ? data[113] : _0344_;
  assign _0001_[113] = _0872_ ? data[113] : _0345_;
  assign _0346_ = byte_sel[2] ? p_in[18] : data[114];
  assign _0347_ = _0151_ ? _1110_ : data[114];
  assign _0348_ = _0876_ ? _0346_ : _0347_;
  assign _0349_ = _0875_ ? data[114] : _0348_;
  assign _0350_ = _0874_ ? data[114] : _0349_;
  assign _0001_[114] = _0872_ ? data[114] : _0350_;
  assign _0351_ = byte_sel[2] ? p_in[19] : data[115];
  assign _0352_ = _0153_ ? _1110_ : data[115];
  assign _0353_ = _0876_ ? _0351_ : _0352_;
  assign _0354_ = _0875_ ? data[115] : _0353_;
  assign _0355_ = _0874_ ? data[115] : _0354_;
  assign _0001_[115] = _0872_ ? data[115] : _0355_;
  assign _0356_ = byte_sel[2] ? p_in[20] : data[116];
  assign _0357_ = _0136_ ? _1110_ : data[116];
  assign _0358_ = _0876_ ? _0356_ : _0357_;
  assign _0359_ = _0875_ ? data[116] : _0358_;
  assign _0360_ = _0874_ ? data[116] : _0359_;
  assign _0001_[116] = _0872_ ? data[116] : _0360_;
  assign _0361_ = byte_sel[2] ? p_in[21] : data[117];
  assign _0362_ = _0138_ ? _1110_ : data[117];
  assign _0363_ = _0876_ ? _0361_ : _0362_;
  assign _0364_ = _0875_ ? data[117] : _0363_;
  assign _0365_ = _0874_ ? data[117] : _0364_;
  assign _0001_[117] = _0872_ ? data[117] : _0365_;
  assign _0366_ = byte_sel[2] ? p_in[18] : data[18];
  assign _0367_ = _0213_ ? _1110_ : data[18];
  assign _0368_ = _0876_ ? data[18] : _0367_;
  assign _0369_ = _0875_ ? data[18] : _0368_;
  assign _0370_ = _0874_ ? data[18] : _0369_;
  assign _0001_[18] = _0872_ ? _0366_ : _0370_;
  assign _0371_ = byte_sel[2] ? p_in[22] : data[118];
  assign _0372_ = _0141_ ? _1110_ : data[118];
  assign _0373_ = _0876_ ? _0371_ : _0372_;
  assign _0374_ = _0875_ ? data[118] : _0373_;
  assign _0375_ = _0874_ ? data[118] : _0374_;
  assign _0001_[118] = _0872_ ? data[118] : _0375_;
  assign _0376_ = byte_sel[2] ? p_in[23] : data[119];
  assign _0377_ = _0142_ ? _1110_ : data[119];
  assign _0378_ = _0876_ ? _0376_ : _0377_;
  assign _0379_ = _0875_ ? data[119] : _0378_;
  assign _0380_ = _0874_ ? data[119] : _0379_;
  assign _0001_[119] = _0872_ ? data[119] : _0380_;
  assign _0381_ = byte_sel[1] ? p_in[8] : data[104];
  assign _0382_ = _0196_ ? _1110_ : data[104];
  assign _0383_ = _0876_ ? _0381_ : _0382_;
  assign _0384_ = _0875_ ? data[104] : _0383_;
  assign _0385_ = _0874_ ? data[104] : _0384_;
  assign _0001_[104] = _0872_ ? data[104] : _0385_;
  assign _0386_ = byte_sel[1] ? p_in[9] : data[105];
  assign _0387_ = _0197_ ? _1110_ : data[105];
  assign _0388_ = _0876_ ? _0386_ : _0387_;
  assign _0389_ = _0875_ ? data[105] : _0388_;
  assign _0390_ = _0874_ ? data[105] : _0389_;
  assign _0001_[105] = _0872_ ? data[105] : _0390_;
  assign _0391_ = byte_sel[1] ? p_in[10] : data[106];
  assign _0392_ = _0199_ ? _1110_ : data[106];
  assign _0393_ = _0876_ ? _0391_ : _0392_;
  assign _0394_ = _0875_ ? data[106] : _0393_;
  assign _0395_ = _0874_ ? data[106] : _0394_;
  assign _0001_[106] = _0872_ ? data[106] : _0395_;
  assign _0396_ = byte_sel[1] ? p_in[11] : data[107];
  assign _0397_ = _0200_ ? _1110_ : data[107];
  assign _0398_ = _0876_ ? _0396_ : _0397_;
  assign _0399_ = _0875_ ? data[107] : _0398_;
  assign _0400_ = _0874_ ? data[107] : _0399_;
  assign _0001_[107] = _0872_ ? data[107] : _0400_;
  assign _0401_ = byte_sel[1] ? p_in[12] : data[108];
  assign _0402_ = _0189_ ? _1110_ : data[108];
  assign _0403_ = _0876_ ? _0401_ : _0402_;
  assign _0404_ = _0875_ ? data[108] : _0403_;
  assign _0405_ = _0874_ ? data[108] : _0404_;
  assign _0001_[108] = _0872_ ? data[108] : _0405_;
  assign _0406_ = byte_sel[2] ? p_in[19] : data[19];
  assign _0407_ = _0214_ ? _1110_ : data[19];
  assign _0408_ = _0876_ ? data[19] : _0407_;
  assign _0409_ = _0875_ ? data[19] : _0408_;
  assign _0410_ = _0874_ ? data[19] : _0409_;
  assign _0001_[19] = _0872_ ? _0406_ : _0410_;
  assign _0411_ = byte_sel[1] ? p_in[13] : data[109];
  assign _0412_ = _0190_ ? _1110_ : data[109];
  assign _0413_ = _0876_ ? _0411_ : _0412_;
  assign _0414_ = _0875_ ? data[109] : _0413_;
  assign _0415_ = _0874_ ? data[109] : _0414_;
  assign _0001_[109] = _0872_ ? data[109] : _0415_;
  assign _0416_ = byte_sel[1] ? p_in[14] : data[110];
  assign _0417_ = _0192_ ? _1110_ : data[110];
  assign _0418_ = _0876_ ? _0416_ : _0417_;
  assign _0419_ = _0875_ ? data[110] : _0418_;
  assign _0420_ = _0874_ ? data[110] : _0419_;
  assign _0001_[110] = _0872_ ? data[110] : _0420_;
  assign _0421_ = byte_sel[1] ? p_in[15] : data[111];
  assign _0422_ = _0193_ ? _1110_ : data[111];
  assign _0423_ = _0876_ ? _0421_ : _0422_;
  assign _0424_ = _0875_ ? data[111] : _0423_;
  assign _0425_ = _0874_ ? data[111] : _0424_;
  assign _0001_[111] = _0872_ ? data[111] : _0425_;
  assign _0426_ = byte_sel[0] ? p_in[0] : data[96];
  assign _0427_ = _0181_ ? _1110_ : data[96];
  assign _0428_ = _0876_ ? _0426_ : _0427_;
  assign _0429_ = _0875_ ? data[96] : _0428_;
  assign _0430_ = _0874_ ? data[96] : _0429_;
  assign _0001_[96] = _0872_ ? data[96] : _0430_;
  assign _0431_ = byte_sel[0] ? p_in[1] : data[97];
  assign _0432_ = _0182_ ? _1110_ : data[97];
  assign _0433_ = _0876_ ? _0431_ : _0432_;
  assign _0434_ = _0875_ ? data[97] : _0433_;
  assign _0435_ = _0874_ ? data[97] : _0434_;
  assign _0001_[97] = _0872_ ? data[97] : _0435_;
  assign _0436_ = byte_sel[0] ? p_in[2] : data[98];
  assign _0437_ = _0184_ ? _1110_ : data[98];
  assign _0438_ = _0876_ ? _0436_ : _0437_;
  assign _0439_ = _0875_ ? data[98] : _0438_;
  assign _0440_ = _0874_ ? data[98] : _0439_;
  assign _0001_[98] = _0872_ ? data[98] : _0440_;
  assign _0441_ = byte_sel[0] ? p_in[3] : data[99];
  assign _0442_ = _0185_ ? _1110_ : data[99];
  assign _0443_ = _0876_ ? _0441_ : _0442_;
  assign _0444_ = _0875_ ? data[99] : _0443_;
  assign _0445_ = _0874_ ? data[99] : _0444_;
  assign _0001_[99] = _0872_ ? data[99] : _0445_;
  assign _0446_ = byte_sel[2] ? p_in[20] : data[20];
  assign _0447_ = _0216_ ? _1110_ : data[20];
  assign _0448_ = _0876_ ? data[20] : _0447_;
  assign _0449_ = _0875_ ? data[20] : _0448_;
  assign _0450_ = _0874_ ? data[20] : _0449_;
  assign _0001_[20] = _0872_ ? _0446_ : _0450_;
  assign _0451_ = byte_sel[0] ? p_in[4] : data[100];
  assign _0452_ = _0174_ ? _1110_ : data[100];
  assign _0453_ = _0876_ ? _0451_ : _0452_;
  assign _0454_ = _0875_ ? data[100] : _0453_;
  assign _0455_ = _0874_ ? data[100] : _0454_;
  assign _0001_[100] = _0872_ ? data[100] : _0455_;
  assign _0456_ = byte_sel[0] ? p_in[5] : data[101];
  assign _0457_ = _0175_ ? _1110_ : data[101];
  assign _0458_ = _0876_ ? _0456_ : _0457_;
  assign _0459_ = _0875_ ? data[101] : _0458_;
  assign _0460_ = _0874_ ? data[101] : _0459_;
  assign _0001_[101] = _0872_ ? data[101] : _0460_;
  assign _0461_ = byte_sel[0] ? p_in[6] : data[102];
  assign _0462_ = _0177_ ? _1110_ : data[102];
  assign _0463_ = _0876_ ? _0461_ : _0462_;
  assign _0464_ = _0875_ ? data[102] : _0463_;
  assign _0465_ = _0874_ ? data[102] : _0464_;
  assign _0001_[102] = _0872_ ? data[102] : _0465_;
  assign _0466_ = byte_sel[0] ? p_in[7] : data[103];
  assign _0467_ = _0178_ ? _1110_ : data[103];
  assign _0468_ = _0876_ ? _0466_ : _0467_;
  assign _0469_ = _0875_ ? data[103] : _0468_;
  assign _0470_ = _0874_ ? data[103] : _0469_;
  assign _0001_[103] = _0872_ ? data[103] : _0470_;
  assign _0471_ = pos_edge ^ cnt[0];
  assign _0472_ = _0471_ & tip;
  assign _0473_ = _0888_ & _0894_;
  assign _0474_ = _0473_ & _0877_;
  assign _0475_ = _0900_ & _0906_;
  assign _0476_ = len[0] & _0871_;
  assign _0000_[0] = _0476_ | _0472_;
  assign _0477_ = ~pos_edge;
  assign _0478_ = ~_0913_;
  assign _0479_ = _0477_ ? cnt[1] : _0478_;
  assign _0480_ = _0479_ & tip;
  assign _0481_ = _0912_ & _0917_;
  assign _0482_ = _0475_ & _0481_;
  assign _0483_ = _0482_ & _0474_;
  assign _0484_ = len[1] & _0871_;
  assign _0000_[1] = _0484_ | _0480_;
  assign _0485_ = ~_0957_;
  assign _0486_ = _0477_ ? cnt[2] : _0485_;
  assign _0487_ = _0486_ & tip;
  assign _0488_ = len[2] & _0871_;
  assign _0000_[2] = _0488_ | _0487_;
  assign _0489_ = ~_0951_;
  assign _0490_ = _0477_ ? cnt[3] : _0489_;
  assign _0491_ = _0490_ & tip;
  assign _0492_ = len[3] & _0871_;
  assign _0000_[3] = _0492_ | _0491_;
  assign _0493_ = ~_0945_;
  assign _0494_ = _0477_ ? cnt[4] : _0493_;
  assign _0495_ = _0494_ & tip;
  assign _0496_ = len[4] & _0871_;
  assign _0000_[4] = _0496_ | _0495_;
  assign _0497_ = ~_0941_;
  assign _0498_ = _0477_ ? cnt[5] : _0497_;
  assign _0499_ = _0498_ & tip;
  assign _0500_ = len[5] & _0871_;
  assign _0000_[5] = _0500_ | _0499_;
  assign _0501_ = ~_0936_;
  assign _0502_ = _0477_ ? cnt[6] : _0501_;
  assign _0503_ = _0502_ & tip;
  assign _0504_ = len[6] & _0871_;
  assign _0000_[6] = _0504_ | _0503_;
  assign _0505_ = _0935_ | cnt[6];
  assign _0506_ = _0505_ ^ _0861_;
  assign _0507_ = _0477_ ? cnt[7] : _0506_;
  assign _0000_[7] = _0871_ ? _0483_ : _0507_;
  assign _0508_ = byte_sel[2] ? p_in[21] : data[21];
  assign _0509_ = _0217_ ? _1110_ : data[21];
  assign _0510_ = _0876_ ? data[21] : _0509_;
  assign _0511_ = _0875_ ? data[21] : _0510_;
  assign _0512_ = _0874_ ? data[21] : _0511_;
  assign _0001_[21] = _0872_ ? _0508_ : _0512_;
  assign _0513_ = byte_sel[2] ? p_in[22] : data[22];
  assign _0514_ = _0206_ ? _1110_ : data[22];
  assign _0515_ = _0876_ ? data[22] : _0514_;
  assign _0516_ = _0875_ ? data[22] : _0515_;
  assign _0517_ = _0874_ ? data[22] : _0516_;
  assign _0001_[22] = _0872_ ? _0513_ : _0517_;
  assign _0518_ = byte_sel[2] ? p_in[23] : data[23];
  assign _0519_ = _0207_ ? _1110_ : data[23];
  assign _0520_ = _0876_ ? data[23] : _0519_;
  assign _0521_ = _0875_ ? data[23] : _0520_;
  assign _0522_ = _0874_ ? data[23] : _0521_;
  assign _0001_[23] = _0872_ ? _0518_ : _0522_;
  assign _0523_ = byte_sel[1] ? p_in[8] : data[8];
  assign _0524_ = _0257_ ? _1110_ : data[8];
  assign _0525_ = _0876_ ? data[8] : _0524_;
  assign _0526_ = _0875_ ? data[8] : _0525_;
  assign _0527_ = _0874_ ? data[8] : _0526_;
  assign _0001_[8] = _0872_ ? _0523_ : _0527_;
  assign _0528_ = byte_sel[1] ? p_in[9] : data[9];
  assign _0529_ = _0258_ ? _1110_ : data[9];
  assign _0530_ = _0876_ ? data[9] : _0529_;
  assign _0531_ = _0875_ ? data[9] : _0530_;
  assign _0532_ = _0874_ ? data[9] : _0531_;
  assign _0001_[9] = _0872_ ? _0528_ : _0532_;
  assign _0533_ = _0477_ | _0871_;
  assign _0534_ = _0533_ | _0974_;
  assign _0003_ = _0871_ ? go : _0534_;
  assign _0535_ = byte_sel[1] ? p_in[10] : data[10];
  assign _0536_ = _0260_ ? _1110_ : data[10];
  assign _0537_ = _0876_ ? data[10] : _0536_;
  assign _0538_ = _0875_ ? data[10] : _0537_;
  assign _0539_ = _0874_ ? data[10] : _0538_;
  assign _0001_[10] = _0872_ ? _0535_ : _0539_;
  assign _0540_ = byte_sel[1] ? p_in[11] : data[11];
  assign _0541_ = _0261_ ? _1110_ : data[11];
  assign _0542_ = _0876_ ? data[11] : _0541_;
  assign _0543_ = _0875_ ? data[11] : _0542_;
  assign _0544_ = _0874_ ? data[11] : _0543_;
  assign _0001_[11] = _0872_ ? _0540_ : _0544_;
  assign _0545_ = byte_sel[1] ? p_in[12] : data[12];
  assign _0546_ = _0250_ ? _1110_ : data[12];
  assign _0547_ = _0876_ ? data[12] : _0546_;
  assign _0548_ = _0875_ ? data[12] : _0547_;
  assign _0549_ = _0874_ ? data[12] : _0548_;
  assign _0001_[12] = _0872_ ? _0545_ : _0549_;
  assign _0550_ = byte_sel[1] ? p_in[13] : data[13];
  assign _0551_ = _0251_ ? _1110_ : data[13];
  assign _0552_ = _0876_ ? data[13] : _0551_;
  assign _0553_ = _0875_ ? data[13] : _0552_;
  assign _0554_ = _0874_ ? data[13] : _0553_;
  assign _0001_[13] = _0872_ ? _0550_ : _0554_;
  assign _0555_ = byte_sel[1] ? p_in[14] : data[14];
  assign _0556_ = _0253_ ? _1110_ : data[14];
  assign _0557_ = _0876_ ? data[14] : _0556_;
  assign _0558_ = _0875_ ? data[14] : _0557_;
  assign _0559_ = _0874_ ? data[14] : _0558_;
  assign _0001_[14] = _0872_ ? _0555_ : _0559_;
  assign _0560_ = byte_sel[1] ? p_in[15] : data[15];
  assign _0561_ = _0254_ ? _1110_ : data[15];
  assign _0562_ = _0876_ ? data[15] : _0561_;
  assign _0563_ = _0875_ ? data[15] : _0562_;
  assign _0564_ = _0874_ ? data[15] : _0563_;
  assign _0001_[15] = _0872_ ? _0560_ : _0564_;
  assign _0565_ = byte_sel[0] ? p_in[0] : data[0];
  assign _0566_ = _0242_ ? _1110_ : data[0];
  assign _0567_ = _0876_ ? data[0] : _0566_;
  assign _0568_ = _0875_ ? data[0] : _0567_;
  assign _0569_ = _0874_ ? data[0] : _0568_;
  assign _0001_[0] = _0872_ ? _0565_ : _0569_;
  assign _0570_ = byte_sel[0] ? p_in[1] : data[1];
  assign _0571_ = _0243_ ? _1110_ : data[1];
  assign _0572_ = _0876_ ? data[1] : _0571_;
  assign _0573_ = _0875_ ? data[1] : _0572_;
  assign _0574_ = _0874_ ? data[1] : _0573_;
  assign _0001_[1] = _0872_ ? _0570_ : _0574_;
  assign _0575_ = byte_sel[0] ? p_in[2] : data[2];
  assign _0576_ = _0245_ ? _1110_ : data[2];
  assign _0577_ = _0876_ ? data[2] : _0576_;
  assign _0578_ = _0875_ ? data[2] : _0577_;
  assign _0579_ = _0874_ ? data[2] : _0578_;
  assign _0001_[2] = _0872_ ? _0575_ : _0579_;
  assign _0580_ = byte_sel[0] ? p_in[3] : data[3];
  assign _0581_ = _0246_ ? _1110_ : data[3];
  assign _0582_ = _0876_ ? data[3] : _0581_;
  assign _0583_ = _0875_ ? data[3] : _0582_;
  assign _0584_ = _0874_ ? data[3] : _0583_;
  assign _0001_[3] = _0872_ ? _0580_ : _0584_;
  assign _0585_ = byte_sel[0] ? p_in[4] : data[4];
  assign _0586_ = _0235_ ? _1110_ : data[4];
  assign _0587_ = _0876_ ? data[4] : _0586_;
  assign _0588_ = _0875_ ? data[4] : _0587_;
  assign _0589_ = _0874_ ? data[4] : _0588_;
  assign _0001_[4] = _0872_ ? _0585_ : _0589_;
  assign _0590_ = byte_sel[3] ? p_in[24] : data[24];
  assign _0591_ = _0209_ ? _1110_ : data[24];
  assign _0592_ = _0876_ ? data[24] : _0591_;
  assign _0593_ = _0875_ ? data[24] : _0592_;
  assign _0594_ = _0874_ ? data[24] : _0593_;
  assign _0001_[24] = _0872_ ? _0590_ : _0594_;
  assign _0595_ = byte_sel[0] ? p_in[5] : data[5];
  assign _0596_ = _0236_ ? _1110_ : data[5];
  assign _0597_ = _0876_ ? data[5] : _0596_;
  assign _0598_ = _0875_ ? data[5] : _0597_;
  assign _0599_ = _0874_ ? data[5] : _0598_;
  assign _0001_[5] = _0872_ ? _0595_ : _0599_;
  assign _0600_ = byte_sel[0] ? p_in[6] : data[6];
  assign _0601_ = _0238_ ? _1110_ : data[6];
  assign _0602_ = _0876_ ? data[6] : _0601_;
  assign _0603_ = _0875_ ? data[6] : _0602_;
  assign _0604_ = _0874_ ? data[6] : _0603_;
  assign _0001_[6] = _0872_ ? _0600_ : _0604_;
  assign _0605_ = byte_sel[0] ? p_in[7] : data[7];
  assign _0606_ = _0239_ ? _1110_ : data[7];
  assign _0607_ = _0876_ ? data[7] : _0606_;
  assign _0608_ = _0875_ ? data[7] : _0607_;
  assign _0609_ = _0874_ ? data[7] : _0608_;
  assign _0001_[7] = _0872_ ? _0605_ : _0609_;
  assign _0610_ = byte_sel[3] ? p_in[24] : data[56];
  assign _0611_ = _0165_ ? _1110_ : data[56];
  assign _0612_ = _0876_ ? data[56] : _0611_;
  assign _0613_ = _0875_ ? data[56] : _0612_;
  assign _0614_ = _0874_ ? _0610_ : _0613_;
  assign _0001_[56] = _0872_ ? data[56] : _0614_;
  assign _0615_ = byte_sel[3] ? p_in[25] : data[57];
  assign _0616_ = _0166_ ? _1110_ : data[57];
  assign _0617_ = _0876_ ? data[57] : _0616_;
  assign _0618_ = _0875_ ? data[57] : _0617_;
  assign _0619_ = _0874_ ? _0615_ : _0618_;
  assign _0001_[57] = _0872_ ? data[57] : _0619_;
  assign _0620_ = byte_sel[3] ? p_in[26] : data[58];
  assign _0621_ = _0168_ ? _1110_ : data[58];
  assign _0622_ = _0876_ ? data[58] : _0621_;
  assign _0623_ = _0875_ ? data[58] : _0622_;
  assign _0624_ = _0874_ ? _0620_ : _0623_;
  assign _0001_[58] = _0872_ ? data[58] : _0624_;
  assign _0625_ = byte_sel[3] ? p_in[27] : data[59];
  assign _0626_ = _0169_ ? _1110_ : data[59];
  assign _0627_ = _0876_ ? data[59] : _0626_;
  assign _0628_ = _0875_ ? data[59] : _0627_;
  assign _0629_ = _0874_ ? _0625_ : _0628_;
  assign _0001_[59] = _0872_ ? data[59] : _0629_;
  assign _0630_ = byte_sel[3] ? p_in[28] : data[60];
  assign _0631_ = _0157_ ? _1110_ : data[60];
  assign _0632_ = _0876_ ? data[60] : _0631_;
  assign _0633_ = _0875_ ? data[60] : _0632_;
  assign _0634_ = _0874_ ? _0630_ : _0633_;
  assign _0001_[60] = _0872_ ? data[60] : _0634_;
  assign _0635_ = byte_sel[3] ? p_in[29] : data[61];
  assign _0636_ = _0158_ ? _1110_ : data[61];
  assign _0637_ = _0876_ ? data[61] : _0636_;
  assign _0638_ = _0875_ ? data[61] : _0637_;
  assign _0639_ = _0874_ ? _0635_ : _0638_;
  assign _0001_[61] = _0872_ ? data[61] : _0639_;
  assign _0640_ = byte_sel[3] ? p_in[25] : data[25];
  assign _0641_ = _0210_ ? _1110_ : data[25];
  assign _0642_ = _0876_ ? data[25] : _0641_;
  assign _0643_ = _0875_ ? data[25] : _0642_;
  assign _0644_ = _0874_ ? data[25] : _0643_;
  assign _0001_[25] = _0872_ ? _0640_ : _0644_;
  assign _0645_ = byte_sel[3] ? p_in[30] : data[62];
  assign _0646_ = _0160_ ? _1110_ : data[62];
  assign _0647_ = _0876_ ? data[62] : _0646_;
  assign _0648_ = _0875_ ? data[62] : _0647_;
  assign _0649_ = _0874_ ? _0645_ : _0648_;
  assign _0001_[62] = _0872_ ? data[62] : _0649_;
  assign _0650_ = byte_sel[3] ? p_in[31] : data[63];
  assign _0651_ = _0162_ ? _1110_ : data[63];
  assign _0652_ = _0876_ ? data[63] : _0651_;
  assign _0653_ = _0875_ ? data[63] : _0652_;
  assign _0654_ = _0874_ ? _0650_ : _0653_;
  assign _0001_[63] = _0872_ ? data[63] : _0654_;
  assign _0655_ = byte_sel[2] ? p_in[16] : data[48];
  assign _0656_ = _0226_ ? _1110_ : data[48];
  assign _0657_ = _0876_ ? data[48] : _0656_;
  assign _0658_ = _0875_ ? data[48] : _0657_;
  assign _0659_ = _0874_ ? _0655_ : _0658_;
  assign _0001_[48] = _0872_ ? data[48] : _0659_;
  assign _0660_ = byte_sel[2] ? p_in[17] : data[49];
  assign _0661_ = _0227_ ? _1110_ : data[49];
  assign _0662_ = _0876_ ? data[49] : _0661_;
  assign _0663_ = _0875_ ? data[49] : _0662_;
  assign _0664_ = _0874_ ? _0660_ : _0663_;
  assign _0001_[49] = _0872_ ? data[49] : _0664_;
  assign _0665_ = byte_sel[2] ? p_in[18] : data[50];
  assign _0666_ = _0229_ ? _1110_ : data[50];
  assign _0667_ = _0876_ ? data[50] : _0666_;
  assign _0668_ = _0875_ ? data[50] : _0667_;
  assign _0669_ = _0874_ ? _0665_ : _0668_;
  assign _0001_[50] = _0872_ ? data[50] : _0669_;
  assign _0670_ = byte_sel[2] ? p_in[19] : data[51];
  assign _0671_ = _0230_ ? _1110_ : data[51];
  assign _0672_ = _0876_ ? data[51] : _0671_;
  assign _0673_ = _0875_ ? data[51] : _0672_;
  assign _0674_ = _0874_ ? _0670_ : _0673_;
  assign _0001_[51] = _0872_ ? data[51] : _0674_;
  assign _0675_ = byte_sel[2] ? p_in[20] : data[52];
  assign _0676_ = _0222_ ? _1110_ : data[52];
  assign _0677_ = _0876_ ? data[52] : _0676_;
  assign _0678_ = _0875_ ? data[52] : _0677_;
  assign _0679_ = _0874_ ? _0675_ : _0678_;
  assign _0001_[52] = _0872_ ? data[52] : _0679_;
  assign _0680_ = byte_sel[2] ? p_in[21] : data[53];
  assign _0681_ = _0223_ ? _1110_ : data[53];
  assign _0682_ = _0876_ ? data[53] : _0681_;
  assign _0683_ = _0875_ ? data[53] : _0682_;
  assign _0684_ = _0874_ ? _0680_ : _0683_;
  assign _0001_[53] = _0872_ ? data[53] : _0684_;
  assign _0685_ = byte_sel[2] ? p_in[22] : data[54];
  assign _0686_ = _0221_ ? _1110_ : data[54];
  assign _0687_ = _0876_ ? data[54] : _0686_;
  assign _0688_ = _0875_ ? data[54] : _0687_;
  assign _0689_ = _0874_ ? _0685_ : _0688_;
  assign _0001_[54] = _0872_ ? data[54] : _0689_;
  assign _0690_ = tx_negedge ? neg_edge : pos_edge;
  assign _0691_ = _0690_ & _0974_;
  assign _0692_ = _0691_ | _0871_;
  assign _0693_ = ~lsb;
  assign _0694_ = len[6] ^ cnt[6];
  assign _0695_ = _0888_ | cnt[5];
  assign _0696_ = len[5] ^ cnt[5];
  assign _0697_ = _0894_ | cnt[4];
  assign _0698_ = len[4] ^ cnt[4];
  assign _0699_ = _0900_ | cnt[3];
  assign _0700_ = len[3] ^ cnt[3];
  assign _0701_ = _0906_ | cnt[2];
  assign _0702_ = len[2] ^ cnt[2];
  assign _0703_ = _0912_ | cnt[1];
  assign _0704_ = len[1] ^ cnt[1];
  assign _0705_ = _0917_ & cnt[0];
  assign _0706_ = _0705_ | _0704_;
  assign _0707_ = _0706_ & _0703_;
  assign _0708_ = _0707_ | _0702_;
  assign _0709_ = _0708_ & _0701_;
  assign _0710_ = _0709_ | _0700_;
  assign _0711_ = _0710_ & _0699_;
  assign _0712_ = _0711_ | _0698_;
  assign _0713_ = _0712_ & _0697_;
  assign _0714_ = _0713_ | _0696_;
  assign _0715_ = _0714_ & _0695_;
  assign _0716_ = _0715_ ^ _0694_;
  assign _0717_ = _0693_ ? _0501_ : _0716_;
  assign _0718_ = _0713_ ^ _0696_;
  assign _0719_ = _0693_ ? _0497_ : _0718_;
  assign _0720_ = _0711_ ^ _0698_;
  assign _0721_ = _0693_ ? _0493_ : _0720_;
  assign _0722_ = _0709_ ^ _0700_;
  assign _0723_ = _0693_ ? _0489_ : _0722_;
  assign _0724_ = _0707_ ^ _0702_;
  assign _0725_ = _0693_ ? _0485_ : _0724_;
  assign _0726_ = _0705_ ^ _0704_;
  assign _0727_ = _0693_ ? _0478_ : _0726_;
  assign _0728_ = len[0] ^ cnt[0];
  assign _0729_ = _0693_ ? _0864_ : _0728_;
  assign _0730_ = _0729_ ? data[127] : data[126];
  assign _0731_ = _0729_ ? data[125] : data[124];
  assign _0732_ = _0727_ ? _0730_ : _0731_;
  assign _0733_ = _0729_ ? data[123] : data[122];
  assign _0734_ = _0729_ ? data[121] : data[120];
  assign _0735_ = _0727_ ? _0733_ : _0734_;
  assign _0736_ = _0725_ ? _0732_ : _0735_;
  assign _0737_ = _0729_ ? data[119] : data[118];
  assign _0738_ = _0729_ ? data[117] : data[116];
  assign _0739_ = _0727_ ? _0737_ : _0738_;
  assign _0740_ = _0729_ ? data[115] : data[114];
  assign _0741_ = _0729_ ? data[113] : data[112];
  assign _0742_ = _0727_ ? _0740_ : _0741_;
  assign _0743_ = _0725_ ? _0739_ : _0742_;
  assign _0744_ = _0723_ ? _0736_ : _0743_;
  assign _0745_ = _0729_ ? data[111] : data[110];
  assign _0746_ = _0729_ ? data[109] : data[108];
  assign _0747_ = _0727_ ? _0745_ : _0746_;
  assign _0748_ = _0729_ ? data[107] : data[106];
  assign _0749_ = _0729_ ? data[105] : data[104];
  assign _0750_ = _0727_ ? _0748_ : _0749_;
  assign _0751_ = _0725_ ? _0747_ : _0750_;
  assign _0752_ = _0729_ ? data[103] : data[102];
  assign _0753_ = _0729_ ? data[101] : data[100];
  assign _0754_ = _0727_ ? _0752_ : _0753_;
  assign _0755_ = _0729_ ? data[99] : data[98];
  assign _0756_ = _0729_ ? data[97] : data[96];
  assign _0757_ = _0727_ ? _0755_ : _0756_;
  assign _0758_ = _0725_ ? _0754_ : _0757_;
  assign _0759_ = _0723_ ? _0751_ : _0758_;
  assign _0760_ = _0721_ ? _0744_ : _0759_;
  assign _0761_ = _0729_ ? data[95] : data[94];
  assign _0762_ = _0729_ ? data[93] : data[92];
  assign _0763_ = _0727_ ? _0761_ : _0762_;
  assign _0764_ = _0729_ ? data[91] : data[90];
  assign _0765_ = _0729_ ? data[89] : data[88];
  assign _0766_ = _0727_ ? _0764_ : _0765_;
  assign _0767_ = _0725_ ? _0763_ : _0766_;
  assign _0768_ = _0729_ ? data[87] : data[86];
  assign _0769_ = _0729_ ? data[85] : data[84];
  assign _0770_ = _0727_ ? _0768_ : _0769_;
  assign _0771_ = _0729_ ? data[83] : data[82];
  assign _0772_ = _0729_ ? data[81] : data[80];
  assign _0773_ = _0727_ ? _0771_ : _0772_;
  assign _0774_ = _0725_ ? _0770_ : _0773_;
  assign _0775_ = _0723_ ? _0767_ : _0774_;
  assign _0776_ = _0729_ ? data[79] : data[78];
  assign _0777_ = _0729_ ? data[77] : data[76];
  assign _0778_ = _0727_ ? _0776_ : _0777_;
  assign _0779_ = _0729_ ? data[75] : data[74];
  assign _0780_ = _0729_ ? data[73] : data[72];
  assign _0781_ = _0727_ ? _0779_ : _0780_;
  assign _0782_ = _0725_ ? _0778_ : _0781_;
  assign _0783_ = _0729_ ? data[71] : data[70];
  assign _0784_ = _0729_ ? data[69] : data[68];
  assign _0785_ = _0727_ ? _0783_ : _0784_;
  assign _0786_ = _0729_ ? data[67] : data[66];
  assign _0787_ = _0729_ ? data[65] : data[64];
  assign _0788_ = _0727_ ? _0786_ : _0787_;
  assign _0789_ = _0725_ ? _0785_ : _0788_;
  assign _0790_ = _0723_ ? _0782_ : _0789_;
  assign _0791_ = _0721_ ? _0775_ : _0790_;
  assign _0792_ = _0719_ ? _0760_ : _0791_;
  assign _0793_ = _0729_ ? data[63] : data[62];
  assign _0794_ = _0729_ ? data[61] : data[60];
  assign _0795_ = _0727_ ? _0793_ : _0794_;
  assign _0796_ = _0729_ ? data[59] : data[58];
  assign _0797_ = _0729_ ? data[57] : data[56];
  assign _0798_ = _0727_ ? _0796_ : _0797_;
  assign _0799_ = _0725_ ? _0795_ : _0798_;
  assign _0800_ = _0729_ ? data[55] : data[54];
  assign _0801_ = _0729_ ? data[53] : data[52];
  assign _0802_ = _0727_ ? _0800_ : _0801_;
  assign _0803_ = _0729_ ? data[51] : data[50];
  assign _0804_ = _0729_ ? data[49] : data[48];
  assign _0805_ = _0727_ ? _0803_ : _0804_;
  assign _0806_ = _0725_ ? _0802_ : _0805_;
  assign _0807_ = _0723_ ? _0799_ : _0806_;
  assign _0808_ = _0729_ ? data[47] : data[46];
  assign _0809_ = _0729_ ? data[45] : data[44];
  assign _0810_ = _0727_ ? _0808_ : _0809_;
  assign _0811_ = _0729_ ? data[43] : data[42];
  assign _0812_ = _0729_ ? data[41] : data[40];
  assign _0813_ = _0727_ ? _0811_ : _0812_;
  assign _0814_ = _0725_ ? _0810_ : _0813_;
  assign _0815_ = _0729_ ? data[39] : data[38];
  assign _0816_ = _0729_ ? data[37] : data[36];
  assign _0817_ = _0727_ ? _0815_ : _0816_;
  assign _0818_ = _0729_ ? data[35] : data[34];
  assign _0819_ = _0729_ ? data[33] : data[32];
  assign _0820_ = _0727_ ? _0818_ : _0819_;
  assign _0821_ = _0725_ ? _0817_ : _0820_;
  assign _0822_ = _0723_ ? _0814_ : _0821_;
  assign _0823_ = _0721_ ? _0807_ : _0822_;
  assign _0824_ = _0729_ ? data[31] : data[30];
  assign _0825_ = _0729_ ? data[29] : data[28];
  assign _0826_ = _0727_ ? _0824_ : _0825_;
  assign _0827_ = _0729_ ? data[27] : data[26];
  assign _0828_ = _0729_ ? data[25] : data[24];
  assign _0829_ = _0727_ ? _0827_ : _0828_;
  assign _0830_ = _0725_ ? _0826_ : _0829_;
  assign _0831_ = _0729_ ? data[23] : data[22];
  assign _0832_ = _0729_ ? data[21] : data[20];
  assign _0833_ = _0727_ ? _0831_ : _0832_;
  assign _0834_ = _0729_ ? data[19] : data[18];
  assign _0835_ = _0729_ ? data[17] : data[16];
  assign _0836_ = _0727_ ? _0834_ : _0835_;
  assign _0837_ = _0725_ ? _0833_ : _0836_;
  assign _0838_ = _0723_ ? _0830_ : _0837_;
  assign _0839_ = _0729_ ? data[15] : data[14];
  assign _0840_ = _0729_ ? data[13] : data[12];
  assign _0841_ = _0727_ ? _0839_ : _0840_;
  assign _0842_ = _0729_ ? data[11] : data[10];
  assign _0843_ = _0729_ ? data[9] : data[8];
  assign _0844_ = _0727_ ? _0842_ : _0843_;
  assign _0845_ = _0725_ ? _0841_ : _0844_;
  assign _0846_ = _0729_ ? data[7] : data[6];
  assign _0847_ = _0729_ ? data[5] : data[4];
  assign _0848_ = _0727_ ? _0846_ : _0847_;
  assign _0849_ = _0729_ ? data[3] : data[2];
  assign _0850_ = _0729_ ? data[1] : data[0];
  assign _0851_ = _0727_ ? _0849_ : _0850_;
  assign _0852_ = _0725_ ? _0848_ : _0851_;
  assign _0853_ = _0723_ ? _0845_ : _0852_;
  assign _0854_ = _0721_ ? _0838_ : _0853_;
  assign _0855_ = _0719_ ? _0823_ : _0854_;
  assign _0856_ = _0717_ ? _0792_ : _0855_;
  assign _0002_ = _0692_ ? _0856_ : s_out;
  always @(posedge clk or posedge rst)
    if (rst)
      tip <= 0;
    else
      tip <= _0003_;
  always @(posedge clk or posedge rst)
    if (rst)
      s_out <= 0;
    else
      s_out <= _0002_;
  always @(posedge clk or posedge rst)
    if (rst)
      data[0] <= 0;
    else
      data[0] <= _0001_[0];
  always @(posedge clk or posedge rst)
    if (rst)
      data[100] <= 0;
    else
      data[100] <= _0001_[100];
  always @(posedge clk or posedge rst)
    if (rst)
      data[101] <= 0;
    else
      data[101] <= _0001_[101];
  always @(posedge clk or posedge rst)
    if (rst)
      data[102] <= 0;
    else
      data[102] <= _0001_[102];
  always @(posedge clk or posedge rst)
    if (rst)
      data[103] <= 0;
    else
      data[103] <= _0001_[103];
  always @(posedge clk or posedge rst)
    if (rst)
      data[104] <= 0;
    else
      data[104] <= _0001_[104];
  always @(posedge clk or posedge rst)
    if (rst)
      data[105] <= 0;
    else
      data[105] <= _0001_[105];
  always @(posedge clk or posedge rst)
    if (rst)
      data[106] <= 0;
    else
      data[106] <= _0001_[106];
  always @(posedge clk or posedge rst)
    if (rst)
      data[107] <= 0;
    else
      data[107] <= _0001_[107];
  always @(posedge clk or posedge rst)
    if (rst)
      data[108] <= 0;
    else
      data[108] <= _0001_[108];
  always @(posedge clk or posedge rst)
    if (rst)
      data[109] <= 0;
    else
      data[109] <= _0001_[109];
  always @(posedge clk or posedge rst)
    if (rst)
      data[10] <= 0;
    else
      data[10] <= _0001_[10];
  always @(posedge clk or posedge rst)
    if (rst)
      data[110] <= 0;
    else
      data[110] <= _0001_[110];
  always @(posedge clk or posedge rst)
    if (rst)
      data[111] <= 0;
    else
      data[111] <= _0001_[111];
  always @(posedge clk or posedge rst)
    if (rst)
      data[112] <= 0;
    else
      data[112] <= _0001_[112];
  always @(posedge clk or posedge rst)
    if (rst)
      data[113] <= 0;
    else
      data[113] <= _0001_[113];
  always @(posedge clk or posedge rst)
    if (rst)
      data[114] <= 0;
    else
      data[114] <= _0001_[114];
  always @(posedge clk or posedge rst)
    if (rst)
      data[115] <= 0;
    else
      data[115] <= _0001_[115];
  always @(posedge clk or posedge rst)
    if (rst)
      data[116] <= 0;
    else
      data[116] <= _0001_[116];
  always @(posedge clk or posedge rst)
    if (rst)
      data[117] <= 0;
    else
      data[117] <= _0001_[117];
  always @(posedge clk or posedge rst)
    if (rst)
      data[118] <= 0;
    else
      data[118] <= _0001_[118];
  always @(posedge clk or posedge rst)
    if (rst)
      data[119] <= 0;
    else
      data[119] <= _0001_[119];
  always @(posedge clk or posedge rst)
    if (rst)
      data[11] <= 0;
    else
      data[11] <= _0001_[11];
  always @(posedge clk or posedge rst)
    if (rst)
      data[120] <= 0;
    else
      data[120] <= _0001_[120];
  always @(posedge clk or posedge rst)
    if (rst)
      data[121] <= 0;
    else
      data[121] <= _0001_[121];
  always @(posedge clk or posedge rst)
    if (rst)
      data[122] <= 0;
    else
      data[122] <= _0001_[122];
  always @(posedge clk or posedge rst)
    if (rst)
      data[123] <= 0;
    else
      data[123] <= _0001_[123];
  always @(posedge clk or posedge rst)
    if (rst)
      data[124] <= 0;
    else
      data[124] <= _0001_[124];
  always @(posedge clk or posedge rst)
    if (rst)
      data[125] <= 0;
    else
      data[125] <= _0001_[125];
  always @(posedge clk or posedge rst)
    if (rst)
      data[126] <= 0;
    else
      data[126] <= _0001_[126];
  always @(posedge clk or posedge rst)
    if (rst)
      data[127] <= 0;
    else
      data[127] <= _0001_[127];
  always @(posedge clk or posedge rst)
    if (rst)
      data[12] <= 0;
    else
      data[12] <= _0001_[12];
  always @(posedge clk or posedge rst)
    if (rst)
      data[13] <= 0;
    else
      data[13] <= _0001_[13];
  always @(posedge clk or posedge rst)
    if (rst)
      data[14] <= 0;
    else
      data[14] <= _0001_[14];
  always @(posedge clk or posedge rst)
    if (rst)
      data[15] <= 0;
    else
      data[15] <= _0001_[15];
  always @(posedge clk or posedge rst)
    if (rst)
      data[16] <= 0;
    else
      data[16] <= _0001_[16];
  always @(posedge clk or posedge rst)
    if (rst)
      data[17] <= 0;
    else
      data[17] <= _0001_[17];
  always @(posedge clk or posedge rst)
    if (rst)
      data[18] <= 0;
    else
      data[18] <= _0001_[18];
  always @(posedge clk or posedge rst)
    if (rst)
      data[19] <= 0;
    else
      data[19] <= _0001_[19];
  always @(posedge clk or posedge rst)
    if (rst)
      data[1] <= 0;
    else
      data[1] <= _0001_[1];
  always @(posedge clk or posedge rst)
    if (rst)
      data[20] <= 0;
    else
      data[20] <= _0001_[20];
  always @(posedge clk or posedge rst)
    if (rst)
      data[21] <= 0;
    else
      data[21] <= _0001_[21];
  always @(posedge clk or posedge rst)
    if (rst)
      data[22] <= 0;
    else
      data[22] <= _0001_[22];
  always @(posedge clk or posedge rst)
    if (rst)
      data[23] <= 0;
    else
      data[23] <= _0001_[23];
  always @(posedge clk or posedge rst)
    if (rst)
      data[24] <= 0;
    else
      data[24] <= _0001_[24];
  always @(posedge clk or posedge rst)
    if (rst)
      data[25] <= 0;
    else
      data[25] <= _0001_[25];
  always @(posedge clk or posedge rst)
    if (rst)
      data[26] <= 0;
    else
      data[26] <= _0001_[26];
  always @(posedge clk or posedge rst)
    if (rst)
      data[27] <= 0;
    else
      data[27] <= _0001_[27];
  always @(posedge clk or posedge rst)
    if (rst)
      data[28] <= 0;
    else
      data[28] <= _0001_[28];
  always @(posedge clk or posedge rst)
    if (rst)
      data[29] <= 0;
    else
      data[29] <= _0001_[29];
  always @(posedge clk or posedge rst)
    if (rst)
      data[2] <= 0;
    else
      data[2] <= _0001_[2];
  always @(posedge clk or posedge rst)
    if (rst)
      data[30] <= 0;
    else
      data[30] <= _0001_[30];
  always @(posedge clk or posedge rst)
    if (rst)
      data[31] <= 0;
    else
      data[31] <= _0001_[31];
  always @(posedge clk or posedge rst)
    if (rst)
      data[32] <= 0;
    else
      data[32] <= _0001_[32];
  always @(posedge clk or posedge rst)
    if (rst)
      data[33] <= 0;
    else
      data[33] <= _0001_[33];
  always @(posedge clk or posedge rst)
    if (rst)
      data[34] <= 0;
    else
      data[34] <= _0001_[34];
  always @(posedge clk or posedge rst)
    if (rst)
      data[35] <= 0;
    else
      data[35] <= _0001_[35];
  always @(posedge clk or posedge rst)
    if (rst)
      data[36] <= 0;
    else
      data[36] <= _0001_[36];
  always @(posedge clk or posedge rst)
    if (rst)
      data[37] <= 0;
    else
      data[37] <= _0001_[37];
  always @(posedge clk or posedge rst)
    if (rst)
      data[38] <= 0;
    else
      data[38] <= _0001_[38];
  always @(posedge clk or posedge rst)
    if (rst)
      data[39] <= 0;
    else
      data[39] <= _0001_[39];
  always @(posedge clk or posedge rst)
    if (rst)
      data[3] <= 0;
    else
      data[3] <= _0001_[3];
  always @(posedge clk or posedge rst)
    if (rst)
      data[40] <= 0;
    else
      data[40] <= _0001_[40];
  always @(posedge clk or posedge rst)
    if (rst)
      data[41] <= 0;
    else
      data[41] <= _0001_[41];
  always @(posedge clk or posedge rst)
    if (rst)
      data[42] <= 0;
    else
      data[42] <= _0001_[42];
  always @(posedge clk or posedge rst)
    if (rst)
      data[43] <= 0;
    else
      data[43] <= _0001_[43];
  always @(posedge clk or posedge rst)
    if (rst)
      data[44] <= 0;
    else
      data[44] <= _0001_[44];
  always @(posedge clk or posedge rst)
    if (rst)
      data[45] <= 0;
    else
      data[45] <= _0001_[45];
  always @(posedge clk or posedge rst)
    if (rst)
      data[46] <= 0;
    else
      data[46] <= _0001_[46];
  always @(posedge clk or posedge rst)
    if (rst)
      data[47] <= 0;
    else
      data[47] <= _0001_[47];
  always @(posedge clk or posedge rst)
    if (rst)
      data[48] <= 0;
    else
      data[48] <= _0001_[48];
  always @(posedge clk or posedge rst)
    if (rst)
      data[49] <= 0;
    else
      data[49] <= _0001_[49];
  always @(posedge clk or posedge rst)
    if (rst)
      data[4] <= 0;
    else
      data[4] <= _0001_[4];
  always @(posedge clk or posedge rst)
    if (rst)
      data[50] <= 0;
    else
      data[50] <= _0001_[50];
  always @(posedge clk or posedge rst)
    if (rst)
      data[51] <= 0;
    else
      data[51] <= _0001_[51];
  always @(posedge clk or posedge rst)
    if (rst)
      data[52] <= 0;
    else
      data[52] <= _0001_[52];
  always @(posedge clk or posedge rst)
    if (rst)
      data[53] <= 0;
    else
      data[53] <= _0001_[53];
  always @(posedge clk or posedge rst)
    if (rst)
      data[54] <= 0;
    else
      data[54] <= _0001_[54];
  always @(posedge clk or posedge rst)
    if (rst)
      data[55] <= 0;
    else
      data[55] <= _0001_[55];
  always @(posedge clk or posedge rst)
    if (rst)
      data[56] <= 0;
    else
      data[56] <= _0001_[56];
  always @(posedge clk or posedge rst)
    if (rst)
      data[57] <= 0;
    else
      data[57] <= _0001_[57];
  always @(posedge clk or posedge rst)
    if (rst)
      data[58] <= 0;
    else
      data[58] <= _0001_[58];
  always @(posedge clk or posedge rst)
    if (rst)
      data[59] <= 0;
    else
      data[59] <= _0001_[59];
  always @(posedge clk or posedge rst)
    if (rst)
      data[5] <= 0;
    else
      data[5] <= _0001_[5];
  always @(posedge clk or posedge rst)
    if (rst)
      data[60] <= 0;
    else
      data[60] <= _0001_[60];
  always @(posedge clk or posedge rst)
    if (rst)
      data[61] <= 0;
    else
      data[61] <= _0001_[61];
  always @(posedge clk or posedge rst)
    if (rst)
      data[62] <= 0;
    else
      data[62] <= _0001_[62];
  always @(posedge clk or posedge rst)
    if (rst)
      data[63] <= 0;
    else
      data[63] <= _0001_[63];
  always @(posedge clk or posedge rst)
    if (rst)
      data[64] <= 0;
    else
      data[64] <= _0001_[64];
  always @(posedge clk or posedge rst)
    if (rst)
      data[65] <= 0;
    else
      data[65] <= _0001_[65];
  always @(posedge clk or posedge rst)
    if (rst)
      data[66] <= 0;
    else
      data[66] <= _0001_[66];
  always @(posedge clk or posedge rst)
    if (rst)
      data[67] <= 0;
    else
      data[67] <= _0001_[67];
  always @(posedge clk or posedge rst)
    if (rst)
      data[68] <= 0;
    else
      data[68] <= _0001_[68];
  always @(posedge clk or posedge rst)
    if (rst)
      data[69] <= 0;
    else
      data[69] <= _0001_[69];
  always @(posedge clk or posedge rst)
    if (rst)
      data[6] <= 0;
    else
      data[6] <= _0001_[6];
  always @(posedge clk or posedge rst)
    if (rst)
      data[70] <= 0;
    else
      data[70] <= _0001_[70];
  always @(posedge clk or posedge rst)
    if (rst)
      data[71] <= 0;
    else
      data[71] <= _0001_[71];
  always @(posedge clk or posedge rst)
    if (rst)
      data[72] <= 0;
    else
      data[72] <= _0001_[72];
  always @(posedge clk or posedge rst)
    if (rst)
      data[73] <= 0;
    else
      data[73] <= _0001_[73];
  always @(posedge clk or posedge rst)
    if (rst)
      data[74] <= 0;
    else
      data[74] <= _0001_[74];
  always @(posedge clk or posedge rst)
    if (rst)
      data[75] <= 0;
    else
      data[75] <= _0001_[75];
  always @(posedge clk or posedge rst)
    if (rst)
      data[76] <= 0;
    else
      data[76] <= _0001_[76];
  always @(posedge clk or posedge rst)
    if (rst)
      data[77] <= 0;
    else
      data[77] <= _0001_[77];
  always @(posedge clk or posedge rst)
    if (rst)
      data[78] <= 0;
    else
      data[78] <= _0001_[78];
  always @(posedge clk or posedge rst)
    if (rst)
      data[79] <= 0;
    else
      data[79] <= _0001_[79];
  always @(posedge clk or posedge rst)
    if (rst)
      data[7] <= 0;
    else
      data[7] <= _0001_[7];
  always @(posedge clk or posedge rst)
    if (rst)
      data[80] <= 0;
    else
      data[80] <= _0001_[80];
  always @(posedge clk or posedge rst)
    if (rst)
      data[81] <= 0;
    else
      data[81] <= _0001_[81];
  always @(posedge clk or posedge rst)
    if (rst)
      data[82] <= 0;
    else
      data[82] <= _0001_[82];
  always @(posedge clk or posedge rst)
    if (rst)
      data[83] <= 0;
    else
      data[83] <= _0001_[83];
  always @(posedge clk or posedge rst)
    if (rst)
      data[84] <= 0;
    else
      data[84] <= _0001_[84];
  always @(posedge clk or posedge rst)
    if (rst)
      data[85] <= 0;
    else
      data[85] <= _0001_[85];
  always @(posedge clk or posedge rst)
    if (rst)
      data[86] <= 0;
    else
      data[86] <= _0001_[86];
  always @(posedge clk or posedge rst)
    if (rst)
      data[87] <= 0;
    else
      data[87] <= _0001_[87];
  always @(posedge clk or posedge rst)
    if (rst)
      data[88] <= 0;
    else
      data[88] <= _0001_[88];
  always @(posedge clk or posedge rst)
    if (rst)
      data[89] <= 0;
    else
      data[89] <= _0001_[89];
  always @(posedge clk or posedge rst)
    if (rst)
      data[8] <= 0;
    else
      data[8] <= _0001_[8];
  always @(posedge clk or posedge rst)
    if (rst)
      data[90] <= 0;
    else
      data[90] <= _0001_[90];
  always @(posedge clk or posedge rst)
    if (rst)
      data[91] <= 0;
    else
      data[91] <= _0001_[91];
  always @(posedge clk or posedge rst)
    if (rst)
      data[92] <= 0;
    else
      data[92] <= _0001_[92];
  always @(posedge clk or posedge rst)
    if (rst)
      data[93] <= 0;
    else
      data[93] <= _0001_[93];
  always @(posedge clk or posedge rst)
    if (rst)
      data[94] <= 0;
    else
      data[94] <= _0001_[94];
  always @(posedge clk or posedge rst)
    if (rst)
      data[95] <= 0;
    else
      data[95] <= _0001_[95];
  always @(posedge clk or posedge rst)
    if (rst)
      data[96] <= 0;
    else
      data[96] <= _0001_[96];
  always @(posedge clk or posedge rst)
    if (rst)
      data[97] <= 0;
    else
      data[97] <= _0001_[97];
  always @(posedge clk or posedge rst)
    if (rst)
      data[98] <= 0;
    else
      data[98] <= _0001_[98];
  always @(posedge clk or posedge rst)
    if (rst)
      data[99] <= 0;
    else
      data[99] <= _0001_[99];
  always @(posedge clk or posedge rst)
    if (rst)
      data[9] <= 0;
    else
      data[9] <= _0001_[9];
  always @(posedge clk or posedge rst)
    if (rst)
      cnt[0] <= 0;
    else
      cnt[0] <= _0000_[0];
  always @(posedge clk or posedge rst)
    if (rst)
      cnt[1] <= 0;
    else
      cnt[1] <= _0000_[1];
  always @(posedge clk or posedge rst)
    if (rst)
      cnt[2] <= 0;
    else
      cnt[2] <= _0000_[2];
  always @(posedge clk or posedge rst)
    if (rst)
      cnt[3] <= 0;
    else
      cnt[3] <= _0000_[3];
  always @(posedge clk or posedge rst)
    if (rst)
      cnt[4] <= 0;
    else
      cnt[4] <= _0000_[4];
  always @(posedge clk or posedge rst)
    if (rst)
      cnt[5] <= 0;
    else
      cnt[5] <= _0000_[5];
  always @(posedge clk or posedge rst)
    if (rst)
      cnt[6] <= 0;
    else
      cnt[6] <= _0000_[6];
  always @(posedge clk or posedge rst)
    if (rst)
      cnt[7] <= 0;
    else
      cnt[7] <= _0000_[7];
  assign p_out = data;
endmodule

module spi_top(wb_clk_i, wb_rst_i, wb_adr_i, wb_dat_i, wb_dat_o, wb_sel_i, wb_we_i, wb_stb_i, wb_cyc_i, wb_ack_o, wb_err_o, wb_int_o, ss_pad_o, sclk_pad_o, mosi_pad_o, miso_pad_i);
  wire [13:0] _000_;
  wire [15:0] _001_;
  wire [7:0] _002_;
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
  wire _310_;
  wire _311_;
  wire _312_;
  wire _313_;
  wire _314_;
  wire _315_;
  wire _316_;
  wire _317_;
  wire _318_;
  wire _319_;
  wire _320_;
  wire _321_;
  wire _322_;
  wire _323_;
  wire _324_;
  wire _325_;
  wire _326_;
  wire _327_;
  wire _328_;
  wire _329_;
  wire _330_;
  wire _331_;
  wire _332_;
  wire _333_;
  wire _334_;
  wire _335_;
  wire _336_;
  wire _337_;
  wire _338_;
  wire _339_;
  wire _340_;
  wire _341_;
  wire _342_;
  wire _343_;
  wire _344_;
  wire _345_;
  wire _346_;
  wire _347_;
  wire _348_;
  wire _349_;
  wire _350_;
  wire _351_;
  wire _352_;
  wire _353_;
  wire _354_;
  wire _355_;
  wire _356_;
  wire _357_;
  wire _358_;
  wire _359_;
  wire _360_;
  wire _361_;
  wire _362_;
  wire _363_;
  wire _364_;
  wire _365_;
  wire _366_;
  wire _367_;
  wire _368_;
  wire _369_;
  wire _370_;
  wire _371_;
  wire _372_;
  wire _373_;
  wire _374_;
  wire _375_;
  wire _376_;
  wire _377_;
  wire _378_;
  wire _379_;
  wire _380_;
  wire _381_;
  wire _382_;
  wire _383_;
  wire _384_;
  wire _385_;
  wire _386_;
  wire _387_;
  wire _388_;
  wire _389_;
  wire _390_;
  wire _391_;
  wire _392_;
  wire _393_;
  wire _394_;
  wire _395_;
  wire _396_;
  wire _397_;
  wire _398_;
  wire _399_;
  wire _400_;
  wire _401_;
  wire _402_;
  wire _403_;
  wire _404_;
  wire _405_;
  wire _406_;
  wire _407_;
  wire _408_;
  wire _409_;
  wire [3:0] _410_;
  reg ass;
  reg [6:0] char_len;
  wire [13:0] ctrl;
  reg [15:0] divider;
  wire go;
  wire ie;
  wire last_bit;
  wire lsb;
  input miso_pad_i;
  output mosi_pad_o;
  wire neg_edge;
  wire pos_edge;
  wire [127:0] rx;
  wire rx_negedge;
  output sclk_pad_o;
  reg [7:0] ss;
  output [7:0] ss_pad_o;
  wire tip;
  wire tx_negedge;
  output wb_ack_o;
  reg wb_ack_o;
  input [4:0] wb_adr_i;
  input wb_clk_i;
  input wb_cyc_i;
  wire [31:0] wb_dat;
  input [31:0] wb_dat_i;
  output [31:0] wb_dat_o;
  reg [31:0] wb_dat_o;
  output wb_err_o;
  output wb_int_o;
  reg wb_int_o;
  input wb_rst_i;
  input [3:0] wb_sel_i;
  input wb_stb_i;
  input wb_we_i;
  assign _005_ = ~wb_ack_o;
  assign _006_ = wb_cyc_i & wb_stb_i;
  assign _003_ = _006_ & _005_;
  assign _007_ = ~wb_adr_i[4];
  assign _008_ = ~wb_adr_i[3];
  assign _009_ = ~wb_adr_i[2];
  assign _010_ = _009_ & _008_;
  assign _011_ = _010_ & _007_;
  assign _012_ = _006_ & wb_we_i;
  assign _410_[0] = _012_ & _011_;
  assign _013_ = wb_adr_i[2] & _008_;
  assign _014_ = _013_ & _007_;
  assign _410_[1] = _014_ & _012_;
  assign _015_ = _009_ & wb_adr_i[3];
  assign _016_ = _015_ & _007_;
  assign _410_[2] = _016_ & _012_;
  assign _017_ = wb_adr_i[2] & wb_adr_i[3];
  assign _018_ = _017_ & _007_;
  assign _410_[3] = _018_ & _012_;
  assign _019_ = ~ss[0];
  assign _020_ = ~ass;
  assign _021_ = ~tip;
  assign _022_ = _021_ | _020_;
  assign _023_ = _022_ | _019_;
  assign _024_ = _019_ | ass;
  assign ss_pad_o[0] = _024_ & _023_;
  assign _025_ = ~ss[1];
  assign _026_ = _022_ | _025_;
  assign _027_ = _025_ | ass;
  assign ss_pad_o[1] = _027_ & _026_;
  assign _028_ = ~ss[2];
  assign _029_ = _022_ | _028_;
  assign _030_ = _028_ | ass;
  assign ss_pad_o[2] = _030_ & _029_;
  assign _031_ = ~ss[3];
  assign _032_ = _022_ | _031_;
  assign _033_ = _031_ | ass;
  assign ss_pad_o[3] = _033_ & _032_;
  assign _034_ = ~ss[4];
  assign _035_ = _022_ | _034_;
  assign _036_ = _034_ | ass;
  assign ss_pad_o[4] = _036_ & _035_;
  assign _037_ = ~ss[5];
  assign _038_ = _022_ | _037_;
  assign _039_ = _037_ | ass;
  assign ss_pad_o[5] = _039_ & _038_;
  assign _040_ = ~ss[6];
  assign _041_ = _022_ | _040_;
  assign _042_ = _040_ | ass;
  assign ss_pad_o[6] = _042_ & _041_;
  assign _043_ = ~ss[7];
  assign _044_ = _022_ | _043_;
  assign _045_ = _043_ | ass;
  assign ss_pad_o[7] = _045_ & _044_;
  assign _046_ = ctrl[12] & tip;
  assign _047_ = pos_edge & last_bit;
  assign _048_ = _047_ & _046_;
  assign _049_ = wb_int_o & _005_;
  assign _004_ = _049_ | _048_;
  assign _050_ = _013_ & wb_adr_i[4];
  assign _051_ = ~_050_;
  assign _052_ = ~_006_;
  assign _053_ = ~wb_we_i;
  assign _054_ = _053_ | tip;
  assign _055_ = _054_ | _052_;
  assign _056_ = _055_ | _051_;
  assign _057_ = wb_sel_i[0] ? wb_dat_i[0] : divider[0];
  assign _001_[0] = _056_ ? divider[0] : _057_;
  assign _058_ = wb_sel_i[0] ? wb_dat_i[1] : divider[1];
  assign _001_[1] = _056_ ? divider[1] : _058_;
  assign _059_ = wb_sel_i[0] ? wb_dat_i[2] : divider[2];
  assign _001_[2] = _056_ ? divider[2] : _059_;
  assign _060_ = wb_sel_i[0] ? wb_dat_i[3] : divider[3];
  assign _001_[3] = _056_ ? divider[3] : _060_;
  assign _061_ = wb_sel_i[0] ? wb_dat_i[4] : divider[4];
  assign _001_[4] = _056_ ? divider[4] : _061_;
  assign _062_ = wb_sel_i[0] ? wb_dat_i[5] : divider[5];
  assign _001_[5] = _056_ ? divider[5] : _062_;
  assign _063_ = wb_sel_i[0] ? wb_dat_i[6] : divider[6];
  assign _001_[6] = _056_ ? divider[6] : _063_;
  assign _064_ = wb_sel_i[0] ? wb_dat_i[7] : divider[7];
  assign _001_[7] = _056_ ? divider[7] : _064_;
  assign _065_ = wb_sel_i[1] ? wb_dat_i[8] : divider[8];
  assign _001_[8] = _056_ ? divider[8] : _065_;
  assign _066_ = wb_sel_i[1] ? wb_dat_i[9] : divider[9];
  assign _001_[9] = _056_ ? divider[9] : _066_;
  assign _067_ = wb_sel_i[1] ? wb_dat_i[10] : divider[10];
  assign _001_[10] = _056_ ? divider[10] : _067_;
  assign _068_ = wb_sel_i[1] ? wb_dat_i[11] : divider[11];
  assign _001_[11] = _056_ ? divider[11] : _068_;
  assign _069_ = wb_sel_i[1] ? wb_dat_i[12] : divider[12];
  assign _001_[12] = _056_ ? divider[12] : _069_;
  assign _070_ = wb_sel_i[1] ? wb_dat_i[13] : divider[13];
  assign _001_[13] = _056_ ? divider[13] : _070_;
  assign _071_ = wb_sel_i[1] ? wb_dat_i[14] : divider[14];
  assign _001_[14] = _056_ ? divider[14] : _071_;
  assign _072_ = wb_sel_i[1] ? wb_dat_i[15] : divider[15];
  assign _001_[15] = _056_ ? divider[15] : _072_;
  assign _073_ = _010_ & wb_adr_i[4];
  assign _074_ = ~_073_;
  assign _075_ = _074_ | _055_;
  assign _076_ = wb_dat_i[0] | char_len[0];
  assign _077_ = wb_sel_i[0] ? _076_ : char_len[0];
  assign _000_[0] = _075_ ? char_len[0] : _077_;
  assign _078_ = wb_sel_i[0] ? wb_dat_i[1] : char_len[1];
  assign _000_[1] = _075_ ? char_len[1] : _078_;
  assign _079_ = wb_sel_i[0] ? wb_dat_i[2] : char_len[2];
  assign _000_[2] = _075_ ? char_len[2] : _079_;
  assign _080_ = wb_sel_i[0] ? wb_dat_i[3] : char_len[3];
  assign _000_[3] = _075_ ? char_len[3] : _080_;
  assign _081_ = wb_sel_i[0] ? wb_dat_i[4] : char_len[4];
  assign _000_[4] = _075_ ? char_len[4] : _081_;
  assign _082_ = wb_sel_i[0] ? wb_dat_i[5] : char_len[5];
  assign _000_[5] = _075_ ? char_len[5] : _082_;
  assign _083_ = wb_sel_i[0] ? wb_dat_i[6] : char_len[6];
  assign _000_[6] = _075_ ? char_len[6] : _083_;
  assign _084_ = wb_sel_i[0] ? wb_dat_i[7] : ctrl[7];
  assign _000_[7] = _075_ ? ctrl[7] : _084_;
  assign _085_ = wb_sel_i[1] ? wb_dat_i[8] : ctrl[8];
  assign _086_ = ~pos_edge;
  assign _087_ = ~last_bit;
  assign _088_ = _087_ | _021_;
  assign _089_ = _088_ | _086_;
  assign _090_ = _089_ & ctrl[8];
  assign _000_[8] = _075_ ? _090_ : _085_;
  assign _091_ = wb_sel_i[1] ? wb_dat_i[9] : ctrl[9];
  assign _000_[9] = _075_ ? ctrl[9] : _091_;
  assign _092_ = wb_sel_i[1] ? wb_dat_i[10] : ctrl[10];
  assign _000_[10] = _075_ ? ctrl[10] : _092_;
  assign _093_ = wb_sel_i[1] ? wb_dat_i[11] : ctrl[11];
  assign _000_[11] = _075_ ? ctrl[11] : _093_;
  assign _094_ = wb_sel_i[1] ? wb_dat_i[12] : ctrl[12];
  assign _000_[12] = _075_ ? ctrl[12] : _094_;
  assign _095_ = wb_sel_i[1] ? wb_dat_i[13] : ass;
  assign _000_[13] = _075_ ? ass : _095_;
  assign _096_ = _015_ & wb_adr_i[4];
  assign _097_ = ~_096_;
  assign _098_ = _097_ | _055_;
  assign _099_ = wb_sel_i[0] ? wb_dat_i[0] : ss[0];
  assign _002_[0] = _098_ ? ss[0] : _099_;
  assign _100_ = wb_sel_i[0] ? wb_dat_i[1] : ss[1];
  assign _002_[1] = _098_ ? ss[1] : _100_;
  assign _101_ = wb_sel_i[0] ? wb_dat_i[2] : ss[2];
  assign _002_[2] = _098_ ? ss[2] : _101_;
  assign _102_ = wb_sel_i[0] ? wb_dat_i[3] : ss[3];
  assign _002_[3] = _098_ ? ss[3] : _102_;
  assign _103_ = wb_sel_i[0] ? wb_dat_i[4] : ss[4];
  assign _002_[4] = _098_ ? ss[4] : _103_;
  assign _104_ = wb_sel_i[0] ? wb_dat_i[5] : ss[5];
  assign _002_[5] = _098_ ? ss[5] : _104_;
  assign _105_ = wb_sel_i[0] ? wb_dat_i[6] : ss[6];
  assign _002_[6] = _098_ ? ss[6] : _105_;
  assign _106_ = wb_sel_i[0] ? wb_dat_i[7] : ss[7];
  assign _002_[7] = _098_ ? ss[7] : _106_;
  assign _107_ = _073_ | _050_;
  assign _108_ = _107_ | _096_;
  assign _109_ = _007_ | _108_;
  assign _110_ = _096_ & ss[0];
  assign _111_ = _073_ & char_len[0];
  assign _112_ = _050_ & divider[0];
  assign _113_ = _112_ | _111_;
  assign _114_ = _113_ | _110_;
  assign _115_ = _011_ & rx[0];
  assign _116_ = _014_ & rx[32];
  assign _117_ = _116_ | _115_;
  assign _118_ = _016_ & rx[64];
  assign _119_ = _018_ & rx[96];
  assign _120_ = _119_ | _118_;
  assign _121_ = _120_ | _117_;
  assign _122_ = _121_ | _114_;
  assign wb_dat[0] = _122_ & _109_;
  assign _123_ = _011_ & rx[10];
  assign _124_ = _014_ & rx[42];
  assign _125_ = _124_ | _123_;
  assign _126_ = _016_ & rx[74];
  assign _127_ = _018_ & rx[106];
  assign _128_ = _127_ | _126_;
  assign _129_ = _073_ & ctrl[10];
  assign _130_ = _050_ & divider[10];
  assign _131_ = _130_ | _129_;
  assign _132_ = _131_ | _128_;
  assign _133_ = _132_ | _125_;
  assign wb_dat[10] = _133_ & _109_;
  assign _134_ = _011_ & rx[11];
  assign _135_ = _014_ & rx[43];
  assign _136_ = _135_ | _134_;
  assign _137_ = _016_ & rx[75];
  assign _138_ = _018_ & rx[107];
  assign _139_ = _138_ | _137_;
  assign _140_ = _073_ & ctrl[11];
  assign _141_ = _050_ & divider[11];
  assign _142_ = _141_ | _140_;
  assign _143_ = _142_ | _139_;
  assign _144_ = _143_ | _136_;
  assign wb_dat[11] = _144_ & _109_;
  assign _145_ = _011_ & rx[12];
  assign _146_ = _014_ & rx[44];
  assign _147_ = _146_ | _145_;
  assign _148_ = _016_ & rx[76];
  assign _149_ = _018_ & rx[108];
  assign _150_ = _149_ | _148_;
  assign _151_ = _073_ & ctrl[12];
  assign _152_ = _050_ & divider[12];
  assign _153_ = _152_ | _151_;
  assign _154_ = _153_ | _150_;
  assign _155_ = _154_ | _147_;
  assign wb_dat[12] = _155_ & _109_;
  assign _156_ = _011_ & rx[13];
  assign _157_ = _014_ & rx[45];
  assign _158_ = _157_ | _156_;
  assign _159_ = _016_ & rx[77];
  assign _160_ = _018_ & rx[109];
  assign _161_ = _160_ | _159_;
  assign _162_ = _073_ & ass;
  assign _163_ = _050_ & divider[13];
  assign _164_ = _163_ | _162_;
  assign _165_ = _164_ | _161_;
  assign _166_ = _165_ | _158_;
  assign wb_dat[13] = _166_ & _109_;
  assign _167_ = _011_ & rx[14];
  assign _168_ = _014_ & rx[46];
  assign _169_ = _168_ | _167_;
  assign _170_ = _050_ & divider[14];
  assign _171_ = _016_ & rx[78];
  assign _172_ = _018_ & rx[110];
  assign _173_ = _172_ | _171_;
  assign _174_ = _173_ | _170_;
  assign _175_ = _174_ | _169_;
  assign wb_dat[14] = _175_ & _109_;
  assign _176_ = _011_ & rx[15];
  assign _177_ = _014_ & rx[47];
  assign _178_ = _177_ | _176_;
  assign _179_ = _050_ & divider[15];
  assign _180_ = _016_ & rx[79];
  assign _181_ = _018_ & rx[111];
  assign _182_ = _181_ | _180_;
  assign _183_ = _182_ | _179_;
  assign _184_ = _183_ | _178_;
  assign wb_dat[15] = _184_ & _109_;
  assign _185_ = _011_ & rx[16];
  assign _186_ = _014_ & rx[48];
  assign _187_ = _186_ | _185_;
  assign _188_ = _016_ & rx[80];
  assign _189_ = _018_ & rx[112];
  assign _190_ = _189_ | _188_;
  assign _191_ = _190_ | _187_;
  assign wb_dat[16] = _191_ & _109_;
  assign _192_ = _011_ & rx[17];
  assign _193_ = _014_ & rx[49];
  assign _194_ = _193_ | _192_;
  assign _195_ = _016_ & rx[81];
  assign _196_ = _018_ & rx[113];
  assign _197_ = _196_ | _195_;
  assign _198_ = _197_ | _194_;
  assign wb_dat[17] = _198_ & _109_;
  assign _199_ = _011_ & rx[18];
  assign _200_ = _014_ & rx[50];
  assign _201_ = _200_ | _199_;
  assign _202_ = _016_ & rx[82];
  assign _203_ = _018_ & rx[114];
  assign _204_ = _203_ | _202_;
  assign _205_ = _204_ | _201_;
  assign wb_dat[18] = _205_ & _109_;
  assign _206_ = _011_ & rx[19];
  assign _207_ = _014_ & rx[51];
  assign _208_ = _207_ | _206_;
  assign _209_ = _016_ & rx[83];
  assign _210_ = _018_ & rx[115];
  assign _211_ = _210_ | _209_;
  assign _212_ = _211_ | _208_;
  assign wb_dat[19] = _212_ & _109_;
  assign _213_ = _096_ & ss[1];
  assign _214_ = _073_ & char_len[1];
  assign _215_ = _050_ & divider[1];
  assign _216_ = _215_ | _214_;
  assign _217_ = _216_ | _213_;
  assign _218_ = _011_ & rx[1];
  assign _219_ = _014_ & rx[33];
  assign _220_ = _219_ | _218_;
  assign _221_ = _016_ & rx[65];
  assign _222_ = _018_ & rx[97];
  assign _223_ = _222_ | _221_;
  assign _224_ = _223_ | _220_;
  assign _225_ = _224_ | _217_;
  assign wb_dat[1] = _225_ & _109_;
  assign _226_ = _011_ & rx[20];
  assign _227_ = _014_ & rx[52];
  assign _228_ = _227_ | _226_;
  assign _229_ = _016_ & rx[84];
  assign _230_ = _018_ & rx[116];
  assign _231_ = _230_ | _229_;
  assign _232_ = _231_ | _228_;
  assign wb_dat[20] = _232_ & _109_;
  assign _233_ = _011_ & rx[21];
  assign _234_ = _014_ & rx[53];
  assign _235_ = _234_ | _233_;
  assign _236_ = _016_ & rx[85];
  assign _237_ = _018_ & rx[117];
  assign _238_ = _237_ | _236_;
  assign _239_ = _238_ | _235_;
  assign wb_dat[21] = _239_ & _109_;
  assign _240_ = _011_ & rx[22];
  assign _241_ = _014_ & rx[54];
  assign _242_ = _241_ | _240_;
  assign _243_ = _016_ & rx[86];
  assign _244_ = _018_ & rx[118];
  assign _245_ = _244_ | _243_;
  assign _246_ = _245_ | _242_;
  assign wb_dat[22] = _246_ & _109_;
  assign _247_ = _011_ & rx[23];
  assign _248_ = _014_ & rx[55];
  assign _249_ = _248_ | _247_;
  assign _250_ = _016_ & rx[87];
  assign _251_ = _018_ & rx[119];
  assign _252_ = _251_ | _250_;
  assign _253_ = _252_ | _249_;
  assign wb_dat[23] = _253_ & _109_;
  assign _254_ = _011_ & rx[24];
  assign _255_ = _014_ & rx[56];
  assign _256_ = _255_ | _254_;
  assign _257_ = _016_ & rx[88];
  assign _258_ = _018_ & rx[120];
  assign _259_ = _258_ | _257_;
  assign _260_ = _259_ | _256_;
  assign wb_dat[24] = _260_ & _109_;
  assign _261_ = _011_ & rx[25];
  assign _262_ = _014_ & rx[57];
  assign _263_ = _262_ | _261_;
  assign _264_ = _016_ & rx[89];
  assign _265_ = _018_ & rx[121];
  assign _266_ = _265_ | _264_;
  assign _267_ = _266_ | _263_;
  assign wb_dat[25] = _267_ & _109_;
  assign _268_ = _011_ & rx[26];
  assign _269_ = _014_ & rx[58];
  assign _270_ = _269_ | _268_;
  assign _271_ = _016_ & rx[90];
  assign _272_ = _018_ & rx[122];
  assign _273_ = _272_ | _271_;
  assign _274_ = _273_ | _270_;
  assign wb_dat[26] = _274_ & _109_;
  assign _275_ = _011_ & rx[27];
  assign _276_ = _014_ & rx[59];
  assign _277_ = _276_ | _275_;
  assign _278_ = _016_ & rx[91];
  assign _279_ = _018_ & rx[123];
  assign _280_ = _279_ | _278_;
  assign _281_ = _280_ | _277_;
  assign wb_dat[27] = _281_ & _109_;
  assign _282_ = _011_ & rx[28];
  assign _283_ = _014_ & rx[60];
  assign _284_ = _283_ | _282_;
  assign _285_ = _016_ & rx[92];
  assign _286_ = _018_ & rx[124];
  assign _287_ = _286_ | _285_;
  assign _288_ = _287_ | _284_;
  assign wb_dat[28] = _288_ & _109_;
  assign _289_ = _011_ & rx[29];
  assign _290_ = _014_ & rx[61];
  assign _291_ = _290_ | _289_;
  assign _292_ = _016_ & rx[93];
  assign _293_ = _018_ & rx[125];
  assign _294_ = _293_ | _292_;
  assign _295_ = _294_ | _291_;
  assign wb_dat[29] = _295_ & _109_;
  assign _296_ = _096_ & ss[2];
  assign _297_ = _073_ & char_len[2];
  assign _298_ = _050_ & divider[2];
  assign _299_ = _298_ | _297_;
  assign _300_ = _299_ | _296_;
  assign _301_ = _011_ & rx[2];
  assign _302_ = _014_ & rx[34];
  assign _303_ = _302_ | _301_;
  assign _304_ = _016_ & rx[66];
  assign _305_ = _018_ & rx[98];
  assign _306_ = _305_ | _304_;
  assign _307_ = _306_ | _303_;
  assign _308_ = _307_ | _300_;
  assign wb_dat[2] = _308_ & _109_;
  assign _309_ = _011_ & rx[30];
  assign _310_ = _014_ & rx[62];
  assign _311_ = _310_ | _309_;
  assign _312_ = _016_ & rx[94];
  assign _313_ = _018_ & rx[126];
  assign _314_ = _313_ | _312_;
  assign _315_ = _314_ | _311_;
  assign wb_dat[30] = _315_ & _109_;
  assign _316_ = _011_ & rx[31];
  assign _317_ = _014_ & rx[63];
  assign _318_ = _317_ | _316_;
  assign _319_ = _016_ & rx[95];
  assign _320_ = _018_ & rx[127];
  assign _321_ = _320_ | _319_;
  assign _322_ = _321_ | _318_;
  assign wb_dat[31] = _322_ & _109_;
  assign _323_ = _096_ & ss[3];
  assign _324_ = _073_ & char_len[3];
  assign _325_ = _050_ & divider[3];
  assign _326_ = _325_ | _324_;
  assign _327_ = _326_ | _323_;
  assign _328_ = _011_ & rx[3];
  assign _329_ = _014_ & rx[35];
  assign _330_ = _329_ | _328_;
  assign _331_ = _016_ & rx[67];
  assign _332_ = _018_ & rx[99];
  assign _333_ = _332_ | _331_;
  assign _334_ = _333_ | _330_;
  assign _335_ = _334_ | _327_;
  assign wb_dat[3] = _335_ & _109_;
  assign _336_ = _096_ & ss[4];
  assign _337_ = _073_ & char_len[4];
  assign _338_ = _050_ & divider[4];
  assign _339_ = _338_ | _337_;
  assign _340_ = _339_ | _336_;
  assign _341_ = _011_ & rx[4];
  assign _342_ = _014_ & rx[36];
  assign _343_ = _342_ | _341_;
  assign _344_ = _016_ & rx[68];
  assign _345_ = _018_ & rx[100];
  assign _346_ = _345_ | _344_;
  assign _347_ = _346_ | _343_;
  assign _348_ = _347_ | _340_;
  assign wb_dat[4] = _348_ & _109_;
  assign _349_ = _096_ & ss[5];
  assign _350_ = _073_ & char_len[5];
  assign _351_ = _050_ & divider[5];
  assign _352_ = _351_ | _350_;
  assign _353_ = _352_ | _349_;
  assign _354_ = _011_ & rx[5];
  assign _355_ = _014_ & rx[37];
  assign _356_ = _355_ | _354_;
  assign _357_ = _016_ & rx[69];
  assign _358_ = _018_ & rx[101];
  assign _359_ = _358_ | _357_;
  assign _360_ = _359_ | _356_;
  assign _361_ = _360_ | _353_;
  assign wb_dat[5] = _361_ & _109_;
  assign _362_ = _096_ & ss[6];
  assign _363_ = _073_ & char_len[6];
  assign _364_ = _050_ & divider[6];
  assign _365_ = _364_ | _363_;
  assign _366_ = _365_ | _362_;
  assign _367_ = _011_ & rx[6];
  assign _368_ = _014_ & rx[38];
  assign _369_ = _368_ | _367_;
  assign _370_ = _016_ & rx[70];
  assign _371_ = _018_ & rx[102];
  assign _372_ = _371_ | _370_;
  assign _373_ = _372_ | _369_;
  assign _374_ = _373_ | _366_;
  assign wb_dat[6] = _374_ & _109_;
  assign _375_ = _096_ & ss[7];
  assign _376_ = _073_ & ctrl[7];
  assign _377_ = _050_ & divider[7];
  assign _378_ = _377_ | _376_;
  assign _379_ = _378_ | _375_;
  assign _380_ = _011_ & rx[7];
  assign _381_ = _014_ & rx[39];
  assign _382_ = _381_ | _380_;
  assign _383_ = _016_ & rx[71];
  assign _384_ = _018_ & rx[103];
  assign _385_ = _384_ | _383_;
  assign _386_ = _385_ | _382_;
  assign _387_ = _386_ | _379_;
  assign wb_dat[7] = _387_ & _109_;
  assign _388_ = _011_ & rx[8];
  assign _389_ = _014_ & rx[40];
  assign _390_ = _389_ | _388_;
  assign _391_ = _016_ & rx[72];
  assign _392_ = _018_ & rx[104];
  assign _393_ = _392_ | _391_;
  assign _394_ = _073_ & ctrl[8];
  assign _395_ = _050_ & divider[8];
  assign _396_ = _395_ | _394_;
  assign _397_ = _396_ | _393_;
  assign _398_ = _397_ | _390_;
  assign wb_dat[8] = _398_ & _109_;
  assign _399_ = _011_ & rx[9];
  assign _400_ = _014_ & rx[41];
  assign _401_ = _400_ | _399_;
  assign _402_ = _016_ & rx[73];
  assign _403_ = _018_ & rx[105];
  assign _404_ = _403_ | _402_;
  assign _405_ = _073_ & ctrl[9];
  assign _406_ = _050_ & divider[9];
  assign _407_ = _406_ | _405_;
  assign _408_ = _407_ | _404_;
  assign _409_ = _408_ | _401_;
  assign wb_dat[9] = _409_ & _109_;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[0] <= 0;
    else
      wb_dat_o[0] <= wb_dat[0];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[10] <= 0;
    else
      wb_dat_o[10] <= wb_dat[10];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[11] <= 0;
    else
      wb_dat_o[11] <= wb_dat[11];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[12] <= 0;
    else
      wb_dat_o[12] <= wb_dat[12];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[13] <= 0;
    else
      wb_dat_o[13] <= wb_dat[13];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[14] <= 0;
    else
      wb_dat_o[14] <= wb_dat[14];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[15] <= 0;
    else
      wb_dat_o[15] <= wb_dat[15];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[16] <= 0;
    else
      wb_dat_o[16] <= wb_dat[16];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[17] <= 0;
    else
      wb_dat_o[17] <= wb_dat[17];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[18] <= 0;
    else
      wb_dat_o[18] <= wb_dat[18];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[19] <= 0;
    else
      wb_dat_o[19] <= wb_dat[19];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[1] <= 0;
    else
      wb_dat_o[1] <= wb_dat[1];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[20] <= 0;
    else
      wb_dat_o[20] <= wb_dat[20];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[21] <= 0;
    else
      wb_dat_o[21] <= wb_dat[21];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[22] <= 0;
    else
      wb_dat_o[22] <= wb_dat[22];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[23] <= 0;
    else
      wb_dat_o[23] <= wb_dat[23];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[24] <= 0;
    else
      wb_dat_o[24] <= wb_dat[24];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[25] <= 0;
    else
      wb_dat_o[25] <= wb_dat[25];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[26] <= 0;
    else
      wb_dat_o[26] <= wb_dat[26];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[27] <= 0;
    else
      wb_dat_o[27] <= wb_dat[27];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[28] <= 0;
    else
      wb_dat_o[28] <= wb_dat[28];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[29] <= 0;
    else
      wb_dat_o[29] <= wb_dat[29];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[2] <= 0;
    else
      wb_dat_o[2] <= wb_dat[2];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[30] <= 0;
    else
      wb_dat_o[30] <= wb_dat[30];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[31] <= 0;
    else
      wb_dat_o[31] <= wb_dat[31];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[3] <= 0;
    else
      wb_dat_o[3] <= wb_dat[3];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[4] <= 0;
    else
      wb_dat_o[4] <= wb_dat[4];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[5] <= 0;
    else
      wb_dat_o[5] <= wb_dat[5];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[6] <= 0;
    else
      wb_dat_o[6] <= wb_dat[6];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[7] <= 0;
    else
      wb_dat_o[7] <= wb_dat[7];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[8] <= 0;
    else
      wb_dat_o[8] <= wb_dat[8];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_dat_o[9] <= 0;
    else
      wb_dat_o[9] <= wb_dat[9];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_ack_o <= 0;
    else
      wb_ack_o <= _003_;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      wb_int_o <= 0;
    else
      wb_int_o <= _004_;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[0] <= 0;
    else
      divider[0] <= _001_[0];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[10] <= 0;
    else
      divider[10] <= _001_[10];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[11] <= 0;
    else
      divider[11] <= _001_[11];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[12] <= 0;
    else
      divider[12] <= _001_[12];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[13] <= 0;
    else
      divider[13] <= _001_[13];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[14] <= 0;
    else
      divider[14] <= _001_[14];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[15] <= 0;
    else
      divider[15] <= _001_[15];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[1] <= 0;
    else
      divider[1] <= _001_[1];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[2] <= 0;
    else
      divider[2] <= _001_[2];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[3] <= 0;
    else
      divider[3] <= _001_[3];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[4] <= 0;
    else
      divider[4] <= _001_[4];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[5] <= 0;
    else
      divider[5] <= _001_[5];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[6] <= 0;
    else
      divider[6] <= _001_[6];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[7] <= 0;
    else
      divider[7] <= _001_[7];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[8] <= 0;
    else
      divider[8] <= _001_[8];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      divider[9] <= 0;
    else
      divider[9] <= _001_[9];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      char_len[0] <= 0;
    else
      char_len[0] <= _000_[0];
  reg \ctrl_reg[10] ;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      \ctrl_reg[10]  <= 0;
    else
      \ctrl_reg[10]  <= _000_[10];
  assign ctrl[10] = \ctrl_reg[10] ;
  reg \ctrl_reg[11] ;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      \ctrl_reg[11]  <= 0;
    else
      \ctrl_reg[11]  <= _000_[11];
  assign ctrl[11] = \ctrl_reg[11] ;
  reg \ctrl_reg[12] ;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      \ctrl_reg[12]  <= 0;
    else
      \ctrl_reg[12]  <= _000_[12];
  assign ctrl[12] = \ctrl_reg[12] ;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      ass <= 0;
    else
      ass <= _000_[13];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      char_len[1] <= 0;
    else
      char_len[1] <= _000_[1];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      char_len[2] <= 0;
    else
      char_len[2] <= _000_[2];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      char_len[3] <= 0;
    else
      char_len[3] <= _000_[3];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      char_len[4] <= 0;
    else
      char_len[4] <= _000_[4];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      char_len[5] <= 0;
    else
      char_len[5] <= _000_[5];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      char_len[6] <= 0;
    else
      char_len[6] <= _000_[6];
  reg \ctrl_reg[7] ;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      \ctrl_reg[7]  <= 0;
    else
      \ctrl_reg[7]  <= _000_[7];
  assign ctrl[7] = \ctrl_reg[7] ;
  reg \ctrl_reg[8] ;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      \ctrl_reg[8]  <= 0;
    else
      \ctrl_reg[8]  <= _000_[8];
  assign ctrl[8] = \ctrl_reg[8] ;
  reg \ctrl_reg[9] ;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      \ctrl_reg[9]  <= 0;
    else
      \ctrl_reg[9]  <= _000_[9];
  assign ctrl[9] = \ctrl_reg[9] ;
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      ss[0] <= 0;
    else
      ss[0] <= _002_[0];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      ss[1] <= 0;
    else
      ss[1] <= _002_[1];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      ss[2] <= 0;
    else
      ss[2] <= _002_[2];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      ss[3] <= 0;
    else
      ss[3] <= _002_[3];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      ss[4] <= 0;
    else
      ss[4] <= _002_[4];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      ss[5] <= 0;
    else
      ss[5] <= _002_[5];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      ss[6] <= 0;
    else
      ss[6] <= _002_[6];
  always @(posedge wb_clk_i or posedge wb_rst_i)
    if (wb_rst_i)
      ss[7] <= 0;
    else
      ss[7] <= _002_[7];
  spi_clgen clgen (
    .clk_in(wb_clk_i),
    .clk_out(sclk_pad_o),
    .divider(divider),
    .enable(tip),
    .go(ctrl[8]),
    .last_clk(last_bit),
    .neg_edge(neg_edge),
    .pos_edge(pos_edge),
    .rst(wb_rst_i)
  );
  spi_shift shift (
    .byte_sel(wb_sel_i),
    .clk(wb_clk_i),
    .go(ctrl[8]),
    .last(last_bit),
    .latch(_410_),
    .len(char_len),
    .lsb(ctrl[11]),
    .neg_edge(neg_edge),
    .p_in(wb_dat_i),
    .p_out(rx),
    .pos_edge(pos_edge),
    .rst(wb_rst_i),
    .rx_negedge(ctrl[9]),
    .s_clk(sclk_pad_o),
    .s_in(miso_pad_i),
    .s_out(mosi_pad_o),
    .tip(tip),
    .tx_negedge(ctrl[10])
  );
  assign { ctrl[13], ctrl[6:0] } = { ass, char_len };
  assign go = ctrl[8];
  assign ie = ctrl[12];
  assign lsb = ctrl[11];
  assign rx_negedge = ctrl[9];
  assign tx_negedge = ctrl[10];
  assign wb_err_o = 1'b0;
endmodule
